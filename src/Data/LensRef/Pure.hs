{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Reference implementation for the "Data.LensRef.Class" interface.

The implementation uses @unsafeCoerce@ internally, but its effect cannot escape.
-}


module Data.LensRef.Pure
    ( RefReader
    , RefCreator
    , RefWriter
    , runRefCreator
    , liftRefWriter'
    ) where

-- import Data.Monoid
import Data.Maybe
import Data.List
import qualified Data.IntSet as Set
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Trans.Control
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
    , _updateFun :: RefWriter m ()    -- what to run if at least one of the dependency changes
    }

data Reference m a = Reference
    { readRef_  :: RefReader m a        
    , writeRef_ :: a -> RefWriter m ()
    , register
        :: Bool                 -- True: run the following function initially
        -> (a -> HandT m a)     -- trigger to be registered
        -> RefCreator m ()         -- emits a handler
    }

----------

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid (StateT (St m) m))

-- collecting identifiers of references on whose values the return value depends on
newtype RefReader (m :: * -> *) a
    = RefReader { runRefReaderT :: ReaderT ValSt (Writer (Ids m)) a }
        deriving (Monad, Applicative, Functor, MonadReader ValSt)

-- invariant property: the values in St state are not changed, the state may be extended
type HandT m = StateT (St m) (WriterT (Ids m) m)

newtype instance RefWriterOf_ (RefReader m) a
    = RefWriter { runRefWriterT :: StateT (St m) m a }
        deriving (Monad, Applicative, Functor, MonadState (St m))

type RefWriter m = RefWriterOf_ (RefReader m)

-- collecting handlers
-- invariant property: the St state is only exteded, not changed
newtype RefCreator m a
    = RefCreator { unRefCreator :: WriterT (Handler m) (StateT (St m) m) a }
        deriving (Monad, Applicative, Functor, MonadFix)

-------------------------------------

newReference :: forall m a . (Monad m, Applicative m) => a -> RefCreator m (Reference m a)
newReference a = RefCreator $ do
    ir <- use $ _1 . to nextKey
{- show resource info
    (aa,bb,cc) <- get
    let info m = Map.size m
    traceShowM (info aa, (info bb, sum $ map (Set.size . snd . _dependencies) $ Map.elems bb), (info cc, sum $ map Set.size $ Map.elems cc))
-}
    let
        getVal = asks $ unsafeGet . fromMaybe (error "fatal: cant find ref value") . Map.lookup ir
        setVal :: MonadState (St m) n => a -> n ()
        setVal a = _1 %= Map.insert ir (Dyn a)

    setVal a

    pure Reference
        { readRef_ = RefReader $ do
            lift . tell $ Set.singleton ir
            getVal

        , writeRef_ = \a -> do
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

        , register = \init upd -> RefCreator $ do

            let gv = mapStateT (fmap (\((a,st),ids) -> ((a,ids),st)) . runWriterT)
                        $ liftRefReader' (RefReader getVal) >>= upd

            (a, ih) <- lift gv
            when init $ setVal a

            ri <- use $ _2 . to nextKey

            -- needed only for efficiency
            let changeRev f = Map.unionWith f . Map.fromSet (const $ Set.singleton ri)

            let modReg = do
                    (a, ih) <- RefWriter gv
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
        }


joinReg :: (Monad m, Applicative m) => RefReader m (Reference m a) -> Bool -> (a -> HandT m a) -> RefCreator m ()
joinReg m init a = do
    r <- newReference mempty
    register r True $ \kill -> do
        runHandler $ kill Kill
        ref <- liftRefReader' m
        fmap fst $ getHandler $ register ref init a
    RefCreator $ tell $ \msg -> MonadMonoid $ do
        h <- runRefWriterT $ liftRefReader $ readRef_ r
        runMonadMonoid $ h msg

instance (Monad m, Applicative m) => RefClass (Reference m) where
    type RefReaderSimple (Reference m) = RefReader m

    unitRef = pure $ Reference
        { readRef_  = pure ()
        , writeRef_ = const $ pure ()
        , register  = const $ const $ pure ()
        }

    readRefSimple = join . fmap readRef_

    writeRefSimple mr a = do
        r <- liftRefReader mr
        writeRef_ r a

    lensMap k mr = pure $ Reference
        { readRef_  = fmap (^. k) $ readRefSimple mr
        , writeRef_ = \b -> do
            r <- liftRefReader mr
            a <- liftRefReader $ readRef_ r
            writeRef_ r $ set k b a
        , register = \init f -> joinReg mr init $ \a -> fmap (\b -> set k b a) $ f (a ^. k)
        }

instance (NewRef m) => MonadRefCreator (RefCreator m) where

    newRef = fmap pure . newReference

    extRef m k a0 = do
        r <- newReference a0
        -- TODO: remove dropHandler?
        dropHandler $ joinReg m False $ \_ -> liftRefReader' $ fmap (^. k) $ readRef_ r
        dropHandler $ register r True $ \a -> liftRefReader' $ fmap (\b -> set k b a) $ readRefSimple m
        return $ pure r

    onChange m f = do
        r <- newReference (mempty, error "impossible #4")
        register r True $ \(h, _) -> do
            runHandler $ h Kill
            liftRefReader' m >>= getHandler . f
        return $ fmap snd $ readRef $ pure r

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

        return $ lensMap (_2 . _2) $ pure r

    onChangeMemo mr f = do
        r <- newReference ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
        register r True upd
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
        = RefCreator $ tell $ MonadMonoid . runRefWriterT . liftEffectM . h

runRefCreator :: forall m a . NewRef m => ((forall b . RefWriter m b -> m b) -> RefCreator m a) -> m a
runRefCreator f = do
    r <- newRef' mempty
    let run :: StateT (St m) m b -> m b
        run = modRef' r
    run . fmap fst . runWriterT . unRefCreator $ f $ run . runRefWriterT


----------------------------------- aux

liftRefReader' :: (Monad m, Applicative m) => RefReader m a -> HandT m a
liftRefReader' = readerToState (^. _1) . mapReaderT (mapWriterT $ return . runIdentity) . runRefReaderT

dropHandler :: (Monad m, Applicative m) => RefCreator m a -> RefCreator m a
dropHandler = mapRefCreator $ lift . fmap fst . runWriterT

getHandler :: (Monad m, Applicative m) => RefCreator m a -> HandT m (Handler m, a)
getHandler = mapStateT (lift . fmap (\((a,h),st)->((h,a),st))) . runWriterT . unRefCreator

mapRefCreator f = RefCreator . f . unRefCreator

unsafeGet :: Dyn -> a
unsafeGet (Dyn a) = unsafeCoerce a

runHandler :: (Monad m, Applicative m) => MonadMonoid (StateT (St m) m) () -> HandT m ()
runHandler = mapStateT lift . runMonadMonoid

liftRefWriter' :: (Monad m, Applicative m) => RefWriterOf (RefCreator m) a -> RefCreator m a
liftRefWriter' = RefCreator . lift . runRefWriterT

----------------------------------------- lenses

dependencies :: Lens' (UpdateFunState m) (Id m, Ids m)
dependencies k (UpdateFunState a b c) = k b <&> \b' -> UpdateFunState a b' c

alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c) = k a <&> \a' -> UpdateFunState a' b c

updateFun :: Lens' (UpdateFunState m) (RefWriter m ())
updateFun k (UpdateFunState a b c) = k c <&> \c' -> UpdateFunState a b c'

-------------------------------------------------------

instance (Monad m, Applicative m) => MonadRefReader (RefCreator m) where
    type BaseRef (RefCreator m) = Reference m
    liftRefReader = RefCreator . lift . readerToState (^. _1) . mapReaderT (return . fst . runWriter) . runRefReaderT

instance (Monad m, Applicative m) => MonadRefReader (RefReader m) where
    type BaseRef (RefReader m) = Reference m
    liftRefReader = id

instance (Monad m, Applicative m) => MonadRefReader (RefWriterOf_ (RefReader m)) where
    type BaseRef (RefWriterOf_ (RefReader m)) = Reference m
    liftRefReader = RefWriter . readerToState (^. _1) . mapReaderT (return . fst . runWriter) . runRefReaderT

instance (Monad m, Applicative m) => MonadRefWriter (RefWriterOf_ (RefReader m)) where
    liftRefWriter = id

instance (NewRef m) => MonadMemo (RefCreator m) where
    memoRead = memoRead_ $ \r -> RefCreator . lift . runRefWriterT . writeRefSimple r

instance (Monad m, Applicative m) => MonadEffect (RefWriterOf_ (RefReader m)) where
    type EffectM (RefWriterOf_ (RefReader m)) = m
    liftEffectM = RefWriter . lift

instance (Monad m, Applicative m) => MonadEffect (RefCreator m) where
    type EffectM (RefCreator m) = m
    liftEffectM = RefCreator . lift . lift

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

allUnique :: [Int] -> Bool
allUnique = and . flip evalState mempty . mapM f where
    f x = state $ \s -> (Set.notMember x s, Set.insert x s)

readerToState :: (Monad m, Applicative m) => (s -> r) -> ReaderT r m a -> StateT s m a
readerToState g (ReaderT f) = StateT $ \s -> fmap (flip (,) s) $ f $ g s

nextKey :: Map.IntMap a -> Int
nextKey = maybe 0 ((+1) . fst . fst) . Map.maxViewWithKey

