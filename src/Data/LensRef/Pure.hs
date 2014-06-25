{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
RefHandler implementation for the "Data.LensRef.Class" interface.

The implementation uses @unsafeCoerce@ internally, but its effect cannot escape.
-}


module Data.LensRef.Pure
    ( RefReaderT
    , RefCreatorT
    , RefWriterT
    , runRefCreatorT
    ) where

-- import Data.Monoid
import Data.Maybe
--import Data.List
import qualified Data.IntSet as Set
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
--import Control.Monad.Trans.Control
import Control.Lens.Simple

--import Debug.Trace
import Unsafe.Coerce

import Data.LensRef.Class
import Data.LensRef.Common

---------------------------------

-- Each atomic reference has a unique identifier
type Id (m :: * -> *) = Int
type Ids (m :: * -> *) = Set.IntSet

-- trigger id
type TId (m :: * -> *) = Int
type TIds (m :: * -> *) = Set.IntSet

type St m = (ValSt, TriggerSt m, RevMap m)

-- values of references
type ValSt = Map.IntMap Dyn

-- dynamic value
data Dyn where Dyn :: a -> Dyn

-- triggers
type TriggerSt m = Map.IntMap (UpdateFunState m)

-- reverse dependencies for efficiency
-- x `elem` revmap ! s   <==>  s `elem` ((triggerst ! x) ^. dependencies . _2)
type RevMap m = Map.IntMap (TIds m)

data UpdateFunState m = UpdateFunState
    { _alive :: Bool
    , _dependencies :: (Id m, Ids m)       -- (i, dependencies of i)
    , _updateFun :: RefWriterT m ()    -- what to run if at least one of the dependency changes
    }

data RefHandler m a = RefHandler
    { runRefHandler
        :: forall b
        .  (a -> RefFunctor m b a)
        -> RefReaderT m (b, Bool, Bool -> RefCreatorT m ()) -- True: run the trigger initially also
    }

newtype RefFunctor m b a = RefFunctor { runRefFunctor :: (b, Bool, HandT m a) }

instance Functor m => Functor (RefFunctor m b) where
    fmap f (RefFunctor (b, rep, m)) = RefFunctor (b, rep, fmap f m)

----------

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid (StateT (St m) m))

-- collecting identifiers of references on whose values the return value depends on
newtype RefReaderT (m :: * -> *) a
    = RefReaderT { runRefReaderT :: ReaderT ValSt (Writer (Ids m)) a }
        deriving (Monad, Applicative, Functor, MonadReader ValSt)

-- invariant property: the values in St state are not changed, the state may be extended
type HandT m = StateT (St m) (WriterT (Ids m) m)

newtype instance RefWriterOf_ (RefReaderT m) a
    = RefWriterT { runRefWriterT :: StateT (St m) m a }
        deriving (Monad, Applicative, Functor, MonadState (St m))

type RefWriterT m = RefWriterOf_ (RefReaderT m)

-- collecting handlers
-- invariant property: the St state is only exteded, not changed
newtype RefCreatorT m a
    = RefCreatorT { unRefCreator :: WriterT (Handler m) (StateT (St m) m) a }
        deriving (Monad, Applicative, Functor, MonadFix)

-------------------------------------

newReference :: forall m a . (Monad m, Applicative m) => a -> RefCreatorT m (RefHandler m a)
newReference a = RefCreatorT $ do
    ir <- use $ _1 . to nextKey

    let
        getVal = asks $ unsafeGet . fromMaybe (error "fatal: cant find ref value") . Map.lookup ir
        setVal :: MonadState (St m) n => a -> n ()
        setVal a = _1 %= Map.insert ir (Dyn a)

    setVal a

    pure $ RefHandler $ \ff -> RefReaderT $ do

        lift . tell $ Set.singleton ir
        aold <- getVal

        return $ case runRefFunctor $ ff aold of
          (b, rep, _) -> (,,) b rep $ \init -> RefCreatorT $ do

            let upd = (^. _3) . runRefFunctor . ff
            let gv = mapStateT (fmap (\((a,st),ids) -> ((a,ids),st)) . runWriterT)
                        $ liftRefReader' (RefReaderT getVal) >>= upd

            (a, ih) <- lift gv

            when init $ lift $ runRefWriterT $ do

                st_ <- use _2
                revmap <- use _3

                let st = Map.insert (-1) (UpdateFunState True (ir, mempty) $ setVal a) st_

                    gr = children . _dependencies . (st Map.!)

                    children :: (Id m, Ids m) -> [TId m]
                    children (b, db) =
                         [ na
                         | na <- maybe [] Set.toList $ Map.lookup b revmap
                         , let (UpdateFunState alive (a, _) _) = st Map.! na
                         , alive
                         , a `Set.notMember` db
                         ]

                l <- maybe (fail "cycle") pure $ topSortComponent gr (-1)
    --            when (not $ allUnique $ map (fst . _dependencies . (st Map.!)) l) $ fail "cycle"
                sequence_ $ map (_updateFun . (st Map.!)) l

            when rep $ do

                ri <- use $ _2 . to nextKey

                -- needed only for efficiency
                let changeRev f = Map.unionWith f . Map.fromSet (const $ Set.singleton ri)

                let modReg = do
                        (a, ih) <- RefWriterT gv
                        setVal a

                        -- needed only for efficiency
                        ih' <- use $ _2 . to (Map.! ri) . dependencies . _2
                        _3 %= changeRev (flip Set.difference) (ih' `Set.difference` ih)
                        _3 %= changeRev Set.union (ih `Set.difference` ih')

                        _2 %= Map.adjust (set dependencies (ir, ih)) ri

                _2 %= Map.insert ri (UpdateFunState True (ir, ih) modReg)

                -- needed only for efficiency
                _3 %= changeRev Set.union ih

                let f Kill    = Nothing
                    f Block   = Just $ set alive False
                    f Unblock = Just $ set alive True

                tell $ \msg -> MonadMonoid $ do

                        -- needed only for efficiency
                        when (msg == Kill) $ do
                            ih' <- use $ _2 . to (fromMaybe mempty . fmap (^. dependencies . _2) . Map.lookup ri)
                            _3 %= changeRev (flip Set.difference) ih'

                        _2 %= Map.update ((f msg <*>) . pure) ri


instance (Monad m, Applicative m) => RefClass (RefHandler m) where
    type RefReaderSimple (RefHandler m) = RefReaderT m

    unitRef = RefHandler $ \x -> pure $ case runRefFunctor $ x () of
        (b, rep, _) -> (,,) b rep $ const $ pure ()

    readRefSimple = readRef_

    writeRefSimple r a = writeRef_ r a

    lensMap k (RefHandler r) = RefHandler $ r . k

    joinRef mr = RefHandler $ \ff -> do

        ref0 <- mr
        runRefHandler ref0 ff <&> \(b, rep, cr) -> (,,) b rep $ \init -> case rep of
          False -> cr init
          True -> do

            r <- newReference mempty
            register r True $ \kill -> do
                runHandler $ kill Kill
                ref <- liftRefReader' mr
                fmap fst $ getHandler $ liftRefReader (runRefHandler ref ff) >>= ($ init) . (^. _3)
            RefCreatorT $ tell $ \msg -> MonadMonoid $ do
                h <- runRefWriterT $ liftRefReader $ readRef_ r
                runMonadMonoid $ h msg


instance (SimpleRefClass m) => MonadRefCreator (RefCreatorT m) where

    newRef = newReference

    extendRef m k a0 = do
        r <- newReference a0
        -- TODO: remove dropHandler?
        dropHandler $ register m False $ \_ -> liftRefReader' $ fmap (^. k) $ readRef_ r
        dropHandler $ register r True $ \a -> liftRefReader' $ fmap (\b -> set k b a) $ readRefSimple m
        return r

    onChange m f = do
        r <- newReference (mempty, error "impossible #4")
        register r True $ \(h, _) -> do
            runHandler $ h Kill
            liftRefReader' m >>= getHandler . f
        RefCreatorT $ tell $ \msg -> MonadMonoid $ do
            (h, _) <- runRefWriterT $ liftRefReader $ readRef_ r
            runMonadMonoid $ h msg
        return $ fmap snd $ readRef r

    onChangeEq_ m f = do
        r <- newReference (const False, (mempty, error "impossible #3"))
        register r True $ \it@(p, (h', _)) -> do
            a <- liftRefReader' m
            if p a
              then return it
              else do
                runHandler $ h' Kill
                (h, b) <- getHandler $ f a
                return ((== a), (h, b))
        RefCreatorT $ tell $ \msg -> MonadMonoid $ do
            (_, (h, _)) <- runRefWriterT $ liftRefReader $ readRef_ r
            runMonadMonoid $ h msg
        return $ lensMap (_2 . _2) r

    onChangeMemo mr f = do
        r <- newReference ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
        register r True upd
        RefCreatorT $ tell $ \msg -> MonadMonoid $ do
            ((_, ((_, h1, h2), _)), _) <- runRefWriterT $ liftRefReader $ readRef_ r
            runMonadMonoid $ h1 msg >> h2 msg
        return $ fmap (snd . snd . fst) $ readRef_ r
      where
        upd st@((p, ((m'',h1'',h2''), _)), memo) = do
            let it = (p, (m'', h1''))
            a <- liftRefReader' mr
            if p a
              then return st
              else do
                runHandler $ h2'' Kill
                runHandler $ h1'' Block
                case listToMaybe [ b | (p, b) <- memo, p a] of
                  Just (m',h1') -> do
                    runHandler $ h1' Unblock
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
                  Nothing -> do
                    (h1, m') <- getHandler $ f a
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1,h2), b')), it: memo)

    onRegionStatusChange h
        = RefCreatorT $ tell $ MonadMonoid . runRefWriterT . liftEffectM . h

runRefCreatorT :: forall m a . SimpleRefClass m => ((forall b . RefWriterT m b -> m b) -> RefCreatorT m a) -> m a
runRefCreatorT f = do
    r <- newSimpleRef mempty
    let run :: StateT (St m) m b -> m b
        run = modSimpleRef r
    run . fmap fst . runWriterT . unRefCreator $ f $ run . runRefWriterT


----------------------------------- aux

readRef_ :: (Monad m, Applicative m) => RefHandler m a -> RefReaderT m a
readRef_ r = runRefHandler r (\a -> RefFunctor (a, error "impossible #10", error "impossible #11")) <&> (^. _1)

writeRef_ :: (Monad m, Applicative m) => RefHandler m a -> a -> RefWriterT m ()
writeRef_ r a = liftRefReader (runRefHandler r $ \_ -> RefFunctor ((), False, pure a))
    >>= RefWriterT . fmap fst . runWriterT . unRefCreator . ($ True) . (^. _3)

register
    :: (Monad m, Applicative m)
    => RefHandler m a
    -> Bool                 -- True: run the following function initially
    -> (a -> HandT m a)     -- trigger to be registered
    -> RefCreatorT m ()     -- emits a handler
register r init k = liftRefReader (runRefHandler r $ \a -> RefFunctor ((), True, k a)) >>= ($ init) . (^. _3)

liftRefReader' :: (Monad m, Applicative m) => RefReaderT m a -> HandT m a
liftRefReader' = readerToState (^. _1) . mapReaderT (mapWriterT $ return . runIdentity) . runRefReaderT

dropHandler :: (Monad m, Applicative m) => RefCreatorT m a -> RefCreatorT m a
dropHandler = mapRefCreator $ lift . fmap fst . runWriterT

getHandler :: (Monad m, Applicative m) => RefCreatorT m a -> HandT m (Handler m, a)
getHandler = mapStateT (lift . fmap (\((a,h),st)->((h,a),st))) . runWriterT . unRefCreator

mapRefCreator f = RefCreatorT . f . unRefCreator

unsafeGet :: Dyn -> a
unsafeGet (Dyn a) = unsafeCoerce a

runHandler :: (Monad m, Applicative m) => MonadMonoid (StateT (St m) m) () -> HandT m ()
runHandler = mapStateT lift . runMonadMonoid

----------------------------------------- lenses

dependencies :: Lens' (UpdateFunState m) (Id m, Ids m)
dependencies k (UpdateFunState a b c) = k b <&> \b' -> UpdateFunState a b' c

alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c) = k a <&> \a' -> UpdateFunState a' b c

-------------------------------------------------------

instance (Monad m, Applicative m) => MonadRefReader (RefCreatorT m) where
    type BaseRef (RefCreatorT m) = RefHandler m
    liftRefReader = RefCreatorT . lift . readerToState (^. _1) . mapReaderT (return . fst . runWriter) . runRefReaderT

instance (Monad m, Applicative m) => MonadRefReader (RefReaderT m) where
    type BaseRef (RefReaderT m) = RefHandler m
    liftRefReader = id

instance (Monad m, Applicative m) => MonadRefReader (RefWriterOf_ (RefReaderT m)) where
    type BaseRef (RefWriterOf_ (RefReaderT m)) = RefHandler m
    liftRefReader = RefWriterT . readerToState (^. _1) . mapReaderT (return . fst . runWriter) . runRefReaderT

instance (Monad m, Applicative m) => MonadRefWriter (RefWriterOf_ (RefReaderT m)) where
    liftRefWriter = id

instance (SimpleRefClass m) => MonadMemo (RefCreatorT m) where
    memoRead = memoRead_ $ \r -> RefCreatorT . lift . runRefWriterT . writeRefSimple r

instance (Monad m, Applicative m) => MonadEffect (RefWriterOf_ (RefReaderT m)) where
    type EffectM (RefWriterOf_ (RefReaderT m)) = m
    liftEffectM = RefWriterT . lift

instance (Monad m, Applicative m) => MonadEffect (RefCreatorT m) where
    type EffectM (RefCreatorT m) = m
    liftEffectM = RefCreatorT . lift . lift

-------------------------- aux

-- | topological sorting on component
topSortComponent
    :: (Int -> [Int])   -- ^ children
    -> Int              -- ^ starting point
    -> Maybe [Int]
topSortComponent ch a = topSort (walk a) [a]
  where
    topSort par []
        | Map.null par = Just []
        | otherwise = Nothing
    topSort par (p:ps) = fmap (p:) $ topSort par' $ merge ps ys
      where
        xs = ch p
        par' = foldr (Map.adjust $ filter (/= p)) (Map.delete p par) xs
        ys = filter (null . (par' Map.!)) xs

    walk v = execState (collects v) $ Map.singleton v []

    collects v = mapM_ (collect v) $ ch v
    collect p v = do
        visited <- gets $ Map.member v
        modify $ Map.alter (Just . (p:) . fromMaybe []) v
        when (not visited) $ collects v
{-
allUnique :: [Int] -> Bool
allUnique = and . flip evalState mempty . mapM f where
    f x = state $ \s -> (Set.notMember x s, Set.insert x s)
-}
readerToState :: (Monad m, Applicative m) => (s -> r) -> ReaderT r m a -> StateT s m a
readerToState g (ReaderT f) = StateT $ \s -> fmap (flip (,) s) $ f $ g s


