{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Ref implementation for the "Data.LensRef.Class" interface.

The implementation uses @unsafeCoerce@ internally, but its effect cannot escape.
-}


module Data.LensRef.Pure
    ( RefReaderT            -- RefReader
    , RefCreatorT           -- RefCreator
    , RefWriterT            -- RefWriter
    , currentValue
    , readerToWriter
    , readerToCreator
    , runRefCreatorT        -- runRefCreator
    , Ref
    , readRef
    , writeRef
    , modRef
    , joinRef
    , lensMap
    , unitRef
    , newRef
    , RegionStatusChange (..)
    , onRegionStatusChange

    -- * composed with register
    , memoRead
    , extendRef
    , onChange
    , onChangeEq
    , onChangeEq_
    , onChangeMemo
    ) where

-- import Data.Monoid
import Data.Maybe
--import Data.List
import qualified Data.IntSet as Set
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State.Strict
--import qualified Control.Monad.State.Strict
import Control.Monad.Writer
import Control.Monad.Identity
--import Control.Monad.Trans.Control
import Control.Lens.Simple

--import Debug.Trace
import Unsafe.Coerce

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


-----------------------------------------------

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChangeHandler (MonadMonoid (StateT (St m) m))

-- collecting identifiers of references on whose values the return value depends on
newtype RefReaderT (m :: * -> *) a
    = RefReaderT { runRefReaderT :: ReaderT ValSt (Writer (Ids m)) a }
        deriving (Monad, Applicative, Functor, MonadReader ValSt)

-- invariant property: the values in St state are not changed, the state may be extended
newtype HandT m a = HandT { runHandT :: StateT (St m) (WriterT (Ids m) m) a }
        deriving (Monad, Applicative, Functor) --, MonadReader ValSt)

newtype RefWriterT m a
    = RefWriterT { runRefWriterT :: StateT (St m) m a }
        deriving (Monad, Applicative, Functor, MonadState (St m))

-- collecting handlers
-- invariant property: the St state is only exteded, not changed
newtype RefCreatorT m a
    = RefCreatorT { unRefCreator :: WriterT (Handler m) (StateT (St m) m) a }
        deriving (Monad, Applicative, Functor, MonadFix)

-------------------- register action

newtype RegisterAction m a = RegisterAction { runRegisterAction :: Bool -> RefCreatorT m a }

instance (Monad m, Applicative m) => RefAction (RegisterAction m) where
    type RefActionFunctor (RegisterAction m) = HandT m
    type RefActionCreator (RegisterAction m) = m

    buildRefAction f _ _ g = RegisterAction $ \init -> g init f
    buildUnitRefAction _ = RegisterAction $ const $ pure ()
    joinRefAction m = RegisterAction $ \init -> do
        r <- newRef mempty
        register r True $ \kill -> do
            runHandler $ kill Kill
            fmap fst . getHandler . ($ init) . runRegisterAction =<< currentValue' m
        RefCreatorT $ tell $ \msg -> MonadMonoid $ do
            h <- runRefWriterT $ readerToWriter $ readRef r
            runMonadMonoid $ h msg


         

-------------------------------------

newRef :: forall m a . (Monad m, Applicative m) => a -> RefCreatorT m (Ref m a)
newRef a = RefCreatorT $ do
    ir <- use $ _1 . to nextKey

    let getVal :: RefReaderT m a
        getVal = RefReaderT $ asks $ unsafeGet . fromMaybe (error "fatal: cant find ref value") . Map.lookup ir
        setVal :: MonadState (St m) n => a -> n ()
        setVal a = _1 %= Map.insert ir (Dyn a)

    setVal a

    let am = do
            RefReaderT $ lift . tell $ Set.singleton ir
            getVal

    let wr rep init upd = RefCreatorT $ do

            let gv = mapStateT (fmap (\((a,st),ids) -> ((a,ids),st)) . runWriterT)
                        $ runHandT $ currentValue' getVal >>= upd

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

    pure $ Ref $ \ff ->
        buildRefAction ff
            am
            (RefWriterT . fmap fst . runWriterT . unRefCreator . wr False True . (return .))
            (wr True)


extendRef :: (Applicative m, Monad m) => Ref m b -> Lens' a b -> a -> RefCreatorT m (Ref m a)
extendRef m k a0 = do
    r <- newRef a0
    -- TODO: remove dropHandler?
    dropHandler $ do
        register r True $ \a -> currentValue' $ fmap (\b -> set k b a) $ readRef m
        register m False $ \_ -> currentValue' $ fmap (^. k) $ readRef r
    return r

onChange :: (Applicative m, Monad m) => RefReaderT m a -> (a -> RefCreatorT m b) -> RefCreatorT m (RefReaderT m b)
onChange m f = do
    r <- newRef (mempty, error "impossible #4")
    register r True $ \(h, _) -> do
        runHandler $ h Kill
        currentValue' m >>= getHandler . f
    RefCreatorT $ tell $ \msg -> MonadMonoid $ do
        (h, _) <- runRefWriterT $ readerToWriter $ readRef r
        runMonadMonoid $ h msg
    return $ fmap snd $ readRef r

onChangeEq_ :: (Eq a, Monad m, Applicative m) => RefReaderT m a -> (a -> RefCreatorT m b) -> RefCreatorT m (Ref m b)
onChangeEq_ m f = do
    r <- newRef (const False, (mempty, error "impossible #3"))
    register r True $ \it@(p, (h, _)) -> do
        a <- currentValue' m
        if p a
          then return it
          else do
            runHandler $ h Kill
            hb <- getHandler $ f a
            return ((== a), hb)
    RefCreatorT $ tell $ \msg -> MonadMonoid $ do
        (_, (h, _)) <- runRefWriterT $ readerToWriter $ readRef r
        runMonadMonoid $ h msg
    return $ lensMap (_2 . _2) r

onChangeMemo :: (Eq a, Applicative m, Monad m) => RefReaderT m a -> (a -> RefCreatorT m (RefCreatorT m b)) -> RefCreatorT m (RefReaderT m b)
onChangeMemo mr f = do
    r <- newRef ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
    register r True upd
    RefCreatorT $ tell $ \msg -> MonadMonoid $ do
        ((_, ((_, h1, h2), _)), _) <- runRefWriterT $ readerToWriter $ readRef r
        runMonadMonoid $ h1 msg >> h2 msg
    return $ fmap (snd . snd . fst) $ readRef r
  where
    upd st@((p, ((m'',h1'',h2''), _)), memo) = do
        let it = (p, (m'', h1''))
        a <- currentValue' mr
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

onRegionStatusChange :: (Applicative m, Monad m) => RegionStatusChangeHandler m -> RefCreatorT m ()
onRegionStatusChange h
    = RefCreatorT $ tell $ MonadMonoid . runRefWriterT . lift . h

runRefCreatorT :: forall m a . SimpleRefClass m => ((forall b . RefWriterT m b -> m b) -> RefCreatorT m a) -> m a
runRefCreatorT f = do
    r <- newSimpleRef mempty
    let run :: StateT (St m) m b -> m b
        run = modSimpleRef r
    run . fmap fst . runWriterT . unRefCreator $ f $ run . runRefWriterT


----------------------------------- aux

register
    :: (Monad m, Applicative m)
    => Ref m a
    -> Bool                 -- True: run the following function initially
    -> (a -> HandT m a)     -- trigger to be registered
    -> RefCreatorT m ()     -- emits a handler
register r init k = runRegisterAction (runRef r k) init

currentValue' :: (Monad m, Applicative m) => RefReaderT m a -> HandT m a
currentValue' = HandT . readerToState (^. _1) . mapReaderT (mapWriterT $ return . runIdentity) . runRefReaderT

dropHandler :: (Monad m, Applicative m) => RefCreatorT m a -> RefCreatorT m a
dropHandler = mapRefCreator $ lift . fmap fst . runWriterT

getHandler :: (Monad m, Applicative m) => RefCreatorT m a -> HandT m (Handler m, a)
getHandler = HandT . mapStateT (lift . fmap (\((a,h),st)->((h,a),st))) . runWriterT . unRefCreator

mapRefCreator f = RefCreatorT . f . unRefCreator

unsafeGet :: Dyn -> a
unsafeGet (Dyn a) = unsafeCoerce a

runHandler :: (Monad m, Applicative m) => MonadMonoid (StateT (St m) m) () -> HandT m ()
runHandler = HandT . mapStateT lift . runMonadMonoid

----------------------------------------- lenses

dependencies :: Lens' (UpdateFunState m) (Id m, Ids m)
dependencies k (UpdateFunState a b c) = k b <&> \b' -> UpdateFunState a b' c

alive :: Lens' (UpdateFunState m) Bool
alive k (UpdateFunState a b c) = k a <&> \a' -> UpdateFunState a' b c

-------------------------------------------------------

currentValue :: (Monad m, Applicative m) => RefReaderT m a -> RefReaderT m a
currentValue = RefReaderT . mapReaderT (return . fst . runWriter) . runRefReaderT

readRef :: (Monad m, Applicative m) => Ref m a -> RefReaderT m a
readRef r = runReaderAction $ runRef r Const

readerToCreator :: (Monad m, Applicative m) => RefReaderT m a -> RefCreatorT m a
readerToCreator = RefCreatorT . lift . readerToState (^. _1) . mapReaderT (return . fst . runWriter) . runRefReaderT

readerToWriter :: (Monad m, Applicative m) => RefReaderT m a -> RefWriterT m a
readerToWriter = RefWriterT . readerToState (^. _1) . mapReaderT (return . fst . runWriter) . runRefReaderT

instance MonadTrans RefWriterT where
    lift = RefWriterT . lift

instance MonadTrans RefCreatorT where
    lift = RefCreatorT . lift . lift

wr :: (Monad m, Applicative m) => RefWriterT m a -> RefCreatorT m a
wr = RefCreatorT . lift . runRefWriterT

-------------------------- aux

-- | topological sorting on component
topSortComponent
    :: (Int -> [Int])   -- ^ children
    -> Int              -- ^ starting point
    -> Maybe [Int]
topSortComponent ch a = topSort (execState (collects a) mempty) [a]
  where
    topSort par []
        | Map.null par = Just []
        | otherwise = Nothing
    topSort par (p:ps) = fmap (p:) $ topSort par' $ merge ps ys
      where
        xs = ch p
        par' = foldr (Map.adjust $ filter (/= p)) (Map.delete p par) xs
        ys = filter (null . (par' Map.!)) xs

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


------------------------


newtype Ref m a = Ref { runRef :: Ref_ m a }

type Ref_ m a =
        forall f
        .  (RefAction f, RefActionCreator f ~ m)
        => (a -> RefActionFunctor f a)
        -> f ()

class ( Functor (RefActionFunctor f)
      , Applicative (RefActionCreator f)
      , Monad (RefActionCreator f)
      )
    => RefAction (f :: * -> *) where

    type RefActionFunctor f :: * -> *
    type RefActionCreator f :: * -> *

    buildRefAction
        :: (a -> RefActionFunctor f a)
        -> RefReaderT (RefActionCreator f) a
        -> ((a -> a) -> RefWriterT (RefActionCreator f) ())
        -> (Bool -> (a -> HandT (RefActionCreator f) a) -> RefCreatorT (RefActionCreator f) ())
        -> f ()

    joinRefAction :: RefReaderT (RefActionCreator f) (f ()) -> f ()

    buildUnitRefAction :: (() -> RefActionFunctor f ()) -> f ()


-------------------- reader action

newtype ReaderAction b m a = ReaderAction { runReaderAction :: RefReaderT m b }

instance
    ( Applicative m, Monad m
    ) => RefAction (ReaderAction b m) where

    type RefActionFunctor (ReaderAction b m) = Const b
    type RefActionCreator (ReaderAction b m) = m

    buildRefAction f a _ _ = ReaderAction $ a <&> getConst . f
    joinRefAction m      = ReaderAction $ m >>= runReaderAction
    buildUnitRefAction f = ReaderAction $ pure $ getConst $ f ()


-------------------- writer action

newtype WriterAction m a = WriterAction { runWriterAction :: RefWriterT m a }

instance
    ( Applicative m, Monad m
    ) => RefAction (WriterAction m) where

    type RefActionFunctor (WriterAction m) = Identity
    type RefActionCreator (WriterAction m) = m

    buildRefAction f _ g _ = WriterAction $ g $ runIdentity . f
    joinRefAction m = WriterAction $ readerToWriter m >>= runWriterAction
    buildUnitRefAction _ = WriterAction $ pure ()

infixr 8 `lensMap`

{- | Apply a lens on a reference.
-}
lensMap :: Lens' a b -> Ref m a -> Ref m b
lensMap k (Ref r) = Ref $ r . k

{- | unit reference
-}
unitRef :: Ref m ()
unitRef = Ref buildUnitRefAction

joinRef :: RefReaderT m (Ref m a) -> Ref m a
joinRef mr = Ref $ \f -> joinRefAction (mr <&> \r -> runRef r f)

----------------------

-- | TODO
data RegionStatusChange = Kill | Block | Unblock deriving (Eq, Ord, Show)

-- | TODO
type RegionStatusChangeHandler m = RegionStatusChange -> m ()

------------------

writeRef :: (Monad m, Applicative m) => Ref m a -> a -> RefWriterT m ()
writeRef (Ref r) = runWriterAction . r . const . Identity

--    -- | @modRef r f@ === @readRef r >>= writeRef r . f@
modRef :: (Monad m, Applicative m) => Ref m a -> (a -> a) -> RefWriterT m ()
r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

onChangeEq :: (Eq a, Monad m, Applicative m) => RefReaderT m a -> (a -> RefCreatorT m b) -> RefCreatorT m (RefReaderT m b)
onChangeEq r f = fmap readRef $ onChangeEq_ r f



memoRead :: (Monad m, Applicative m) => RefCreatorT m a -> RefCreatorT m (RefCreatorT m a) 
memoRead g = do
    s <- newRef Nothing
    pure $ readerToCreator (readRef s) >>= \x -> case x of
        Just a -> pure a
        _ -> g >>= \a -> do
            wr $ writeRef s $ Just a
            pure a



