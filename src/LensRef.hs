{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{- |
lensref core API
-}
module LensRef
    ( -- * Monads
      RefReader            -- RefReader
    , RefCreator           -- RefCreator
    , RefWriter            -- RefWriter
    , readerToWriter
    , readerToCreator
    , runRefCreator        -- runRefCreator

    -- * References
    , Ref
    , readRef
    , writeRef
    , modRef
    , joinRef
    , lensMap
    , unitRef
    , newRef

    -- * composed with register
    , memoRead
    , extendRef
    , onChange
    , onChangeEq
    , onChangeEq_
    , onChangeMemo

    -- * Other
    , currentValue
    , RegionStatusChange (..)
    , onRegionStatusChange
    , onRegionStatusChange_

    -- * Reference context
    , RefContext

    , engine
    ) where

import Data.Maybe
import Data.String
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Identity
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.State.Strict

import Unsafe.Coerce

import LensRef.Context

--------------------------------------------------------------------------------
#ifdef __PURE__
--------------------------------------------------------------------------------

import qualified Data.IntSet as Set
import qualified Data.IntMap as Map
import Control.Monad.Reader
import Control.Monad.Writer

engine = "pure"
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

-----------------------------------------------

-- Handlers are added on trigger registration.
-- The registered triggers may be killed, blocked and unblocked via the handler.
-- invariant property: in the St state the ... is changed only
type Handler m = RegionStatusChange -> MonadMonoid (StateT (St m) m) ()

-- collecting identifiers of references on whose values the return value depends on
newtype RefReader (m :: * -> *) a
    = RefReader { runRefReaderT :: ReaderT ValSt (Writer (Ids m)) a }
        deriving (Monad, Applicative, Functor, MonadReader ValSt)

-- invariant property: the values in St state are not changed, the state may be extended
newtype HandT m a = HandT { runHandT :: StateT (St m) (WriterT (Ids m) m) a }
        deriving (Monad, Applicative, Functor) --, MonadReader ValSt)

newtype RefWriter m a
    = RefWriter { runRefWriterT :: StateT (St m) m a }
        deriving (Monad, Applicative, Functor, MonadState (St m))

-- collecting handlers
-- invariant property: the St state is only extended, not changed
newtype RefCreator m a
    = RefCreator { unRefCreator :: WriterT (Handler m) (StateT (St m) m) a }
        deriving (Monad, Applicative, Functor, MonadFix)

-------------------- register action

newtype RegisterAction m a = RegisterAction { runRegisterAction :: Bool -> RefCreator m a }

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
        RefCreator $ tell $ \msg -> MonadMonoid $ do
            h <- runRefWriterT $ readerToWriter $ readRef r
            runMonadMonoid $ h msg


         

-------------------------------------

newRef :: forall m a . (Monad m, Applicative m) => a -> RefCreator m (Ref m a)
newRef a = RefCreator $ do
    ir <- use $ _3_1 . to nextKey

    let getVal :: RefReader m a
        getVal = RefReader $ asks $ unsafeGet . fromMaybe (error "fatal: cant find ref value") . Map.lookup ir
        setVal :: MonadState (St m) n => a -> n ()
        setVal a = _3_1 %= Map.insert ir (Dyn a)

    setVal a

    let am = do
            RefReader $ lift . tell $ Set.singleton ir
            getVal

    let wr rep init upd = RefCreator $ do

            let gv = mapStateT (fmap (\((a,st),ids) -> ((a,ids),st)) . runWriterT)
                        $ runHandT $ currentValue' getVal >>= upd

            (a, ih) <- lift gv

            when init $ lift $ runRefWriterT $ do

                st_ <- use _3_2
                revmap <- use _3_3

                let st = Map.insert (-1) (UpdateFunState True (ir, mempty) $ setVal a) st_

                    gr = children . _dependencies . (st Map.!)

                    children :: (Id m, Ids m) -> [TId m]
                    children (b, db) =
                         [ na
                         | na <- maybe [] Set.toList $ Map.lookup b revmap
                         , let (UpdateFunState alive (a, _) _) = st Map.! na
--                         , alive
                         , a `Set.notMember` db
                         ]

                l <- maybe (fail "cycle") pure $ topSortComponent gr (-1)
    --            when (not $ allUnique $ map (fst . _dependencies . (st Map.!)) l) $ fail "cycle"
                sequence_ $ map (_updateFun . (st Map.!)) l

            when rep $ do

                ri <- use $ _3_2 . to nextKey

                -- needed only for efficiency
                let changeRev f = Map.unionWith f . Map.fromSet (const $ Set.singleton ri)

                let modReg = do
                        (a, ih) <- RefWriter gv
                        setVal a

                        -- needed only for efficiency
                        ih' <- use $ _3_2 . to (Map.! ri) . dependencies . _2
                        _3_3 %= changeRev (flip Set.difference) (ih' `Set.difference` ih)
                        _3_3 %= changeRev Set.union (ih `Set.difference` ih')

                        _3_2 %= Map.adjust (set dependencies (ir, ih)) ri

                _3_2 %= Map.insert ri (UpdateFunState True (ir, ih) modReg)

                -- needed only for efficiency
                _3_3 %= changeRev Set.union ih

                let f Kill    = Nothing
                    f Block   = Just $ set alive False
                    f Unblock = Just $ set alive True

                tell $ \msg -> MonadMonoid $ do

                        -- needed only for efficiency
                        when (msg == Kill) $ do
                            ih' <- use $ _3_2 . to (fromMaybe mempty . fmap (^. dependencies . _2) . Map.lookup ri)
                            _3_3 %= changeRev (flip Set.difference) ih'

                        _3_2 %= Map.update ((f msg <*>) . pure) ri

    pure $ Ref $ \ff ->
        buildRefAction ff
            am
            (RefWriter . fmap fst . runWriterT . unRefCreator . wr False True . (return .))
            (wr True)


extendRef :: (Applicative m, Monad m) => Ref m b -> Lens' a b -> a -> RefCreator m (Ref m a)
extendRef m k a0 = do
    r <- newRef a0
    -- TODO: remove dropHandler?
    dropHandler $ do
        register r True $ \a -> currentValue' $ fmap (\b -> set k b a) $ readRef m
        register m False $ \_ -> currentValue' $ fmap (^. k) $ readRef r
    return r

onChange :: (Applicative m, Monad m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChange m f = do
    r <- newRef (mempty, error "impossible #4")
    register r True $ \(h, _) -> do
        runHandler $ h Kill
        currentValue' m >>= getHandler . f
    RefCreator $ tell $ \msg -> MonadMonoid $ do
        (h, _) <- runRefWriterT $ readerToWriter $ readRef r
        runMonadMonoid $ h msg
    return $ fmap snd $ readRef r

onChangeEq_ :: (Eq a, Monad m, Applicative m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
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
    RefCreator $ tell $ \msg -> MonadMonoid $ do
        (_, (h, _)) <- runRefWriterT $ readerToWriter $ readRef r
        runMonadMonoid $ h msg
    return $ lensMap (_2 . _2) r

onChangeMemo :: (Eq a, Applicative m, Monad m) => RefReader m a -> (a -> RefCreator m (RefCreator m b)) -> RefCreator m (RefReader m b)
onChangeMemo mr f = do
    r <- newRef ((const False, ((error "impossible #2", mempty, mempty) , error "impossible #1")), [])
    register r True upd
    RefCreator $ tell $ \msg -> MonadMonoid $ do
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

onRegionStatusChange_ :: (Applicative m, Monad m) => (RegionStatusChange -> RefReader m (m ())) -> RefCreator m ()
onRegionStatusChange_ h
    = RefCreator $ tell $ MonadMonoid . runRefWriterT . join . readerToWriter . fmap lift . h

onRegionStatusChange :: (Applicative m, Monad m) => (RegionStatusChange -> m ()) -> RefCreator m ()
onRegionStatusChange h
    = RefCreator $ tell $ MonadMonoid . runRefWriterT . lift . h

runRefCreator :: forall m a . RefContext m => ((forall b . RefWriter m b -> m b) -> RefCreator m a) -> m a
runRefCreator f = do
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
    -> RefCreator m ()     -- emits a handler
register r init k = runRegisterAction (runRef r k) init

currentValue' :: (Monad m, Applicative m) => RefReader m a -> HandT m a
currentValue' = HandT . readerToState (^. _3_1) . mapReaderT (mapWriterT $ return . runIdentity) . runRefReaderT

dropHandler :: (Monad m, Applicative m) => RefCreator m a -> RefCreator m a
dropHandler = mapRefCreator $ lift . fmap fst . runWriterT

getHandler :: (Monad m, Applicative m) => RefCreator m a -> HandT m (Handler m, a)
getHandler = HandT . mapStateT (lift . fmap (\((a,h),st)->((h,a),st))) . runWriterT . unRefCreator

mapRefCreator f = RefCreator . f . unRefCreator

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

currentValue :: (Monad m, Applicative m) => RefReader m a -> RefReader m a
currentValue = RefReader . mapReaderT (return . fst . runWriter) . runRefReaderT

readRef :: (Monad m, Applicative m) => Ref m a -> RefReader m a
readRef r = runReaderAction $ runRef r Const

readerToCreator :: (Monad m, Applicative m) => RefReader m a -> RefCreator m a
readerToCreator = RefCreator . lift . readerToState (^. _3_1) . mapReaderT (return . fst . runWriter) . runRefReaderT

readerToWriter :: (Monad m, Applicative m) => RefReader m a -> RefWriter m a
readerToWriter = RefWriter . readerToState (^. _3_1) . mapReaderT (return . fst . runWriter) . runRefReaderT

instance MonadTrans RefWriter where
    lift = RefWriter . lift

instance MonadTrans RefCreator where
    lift = RefCreator . lift . lift

wr :: (Monad m, Applicative m) => RefWriter m a -> RefCreator m a
wr = RefCreator . lift . runRefWriterT

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
        -> RefReader (RefActionCreator f) a
        -> ((a -> a) -> RefWriter (RefActionCreator f) ())
        -> (Bool -> (a -> HandT (RefActionCreator f) a) -> RefCreator (RefActionCreator f) ())
        -> f ()

    joinRefAction :: RefReader (RefActionCreator f) (f ()) -> f ()

    buildUnitRefAction :: (() -> RefActionFunctor f ()) -> f ()


-------------------- reader action

newtype ReaderAction b m a = ReaderAction { runReaderAction :: RefReader m b }

instance
    ( Applicative m, Monad m
    ) => RefAction (ReaderAction b m) where

    type RefActionFunctor (ReaderAction b m) = Const b
    type RefActionCreator (ReaderAction b m) = m

    buildRefAction f a _ _ = ReaderAction $ a <&> getConst . f
    joinRefAction m      = ReaderAction $ m >>= runReaderAction
    buildUnitRefAction f = ReaderAction $ pure $ getConst $ f ()


-------------------- writer action

newtype WriterAction m a = WriterAction { runWriterAction :: RefWriter m a }

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

joinRef :: RefReader m (Ref m a) -> Ref m a
joinRef mr = Ref $ \f -> joinRefAction (mr <&> \r -> runRef r f)

writeRef :: (Monad m, Applicative m) => Ref m a -> a -> RefWriter m ()
writeRef (Ref r) = runWriterAction . r . const . Identity

--    -- | @modRef r f@ === @readRef r >>= writeRef r . f@
modRef :: (Monad m, Applicative m) => Ref m a -> (a -> a) -> RefWriter m ()
r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

onChangeEq :: (Eq a, Monad m, Applicative m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEq r f = fmap readRef $ onChangeEq_ r f



memoRead :: (Monad m, Applicative m) => RefCreator m a -> RefCreator m (RefCreator m a)
memoRead g = do
    s <- newRef Nothing
    pure $ readerToCreator (readRef s) >>= \x -> case x of
        Just a -> pure a
        _ -> g >>= \a -> do
            wr $ writeRef s $ Just a
            pure a

------------- aux

newtype MonadMonoid m a = MonadMonoid
    { runMonadMonoid :: m a }
        deriving (Monad, Applicative, Functor)

instance MonadTrans MonadMonoid where
    lift = MonadMonoid

-- Applicative would be enough
instance (Monad m, Monoid a) => Monoid (MonadMonoid m a) where
    mempty = MonadMonoid $ return mempty
    MonadMonoid a `mappend` MonadMonoid b = MonadMonoid $ liftM2 mappend a b

merge :: Ord a => [a] -> [a] -> [a]
merge [] xs = xs
merge xs [] = xs
merge (x:xs) (y:ys) = case compare x y of
    LT -> x: merge xs (y:ys)
    GT -> y: merge (x:xs) ys
    EQ -> x: merge xs ys

nextKey :: Map.IntMap a -> Int
nextKey = maybe 0 ((+1) . fst . fst) . Map.maxViewWithKey

--------------

_3_1 :: Lens (a,b,c) (a',b,c) a a'
_3_1 k ~(a,b,c) = k a <&> \a' -> (a',b,c)

_3_2 :: Lens (a,b,c) (a,b',c) b b'
_3_2 k ~(a,b,c) = k b <&> \b' -> (a,b',c)

_3_3 :: Lens (a,b,c) (a,b,c') c c'
_3_3 k ~(a,b,c) = k c <&> \c' -> (a,b,c')

--------------------------------------------------------------------------------
#else
--------------------------------------------------------------------------------

import Data.Monoid
import qualified Data.IntMap.Strict as Map

engine = "fast"
----------------------------------- data types

-- | reference temporal state
data RefState m where
    RefState
        :: a        -- reference value
        -> TIds m   -- registered triggers (run them if the value changes)
        -> RefState m

-- | trigger temporal state
data TriggerState m = TriggerState
    { _alive        :: Bool
    , _targetid     :: (Id m)     -- ^ target reference id
    , _dependencies :: (Ids m)    -- ^ source reference ids
    , _updateFun    :: (m ())     -- ^ what to run if at least one of the source ids changes
    , _reverseDeps  :: (TIds m)   -- ^ reverse dependencies (temporarily needed during topological sorting)
    }


-----------------------

-- | global variables
data GlobalVars m = GlobalVars
    { _handlercollection  :: !(SimpleRef m (Handler m))  -- ^ collected handlers
    , _dependencycoll     :: !(SimpleRef m (Ids m))      -- ^ collected dependencies
    , _postpone           :: !(SimpleRef m (m ()))       -- ^ postponed actions
    , _counter            :: !(SimpleRef m Int)          -- ^ increasing counter
    }

-- | reference identifier
type Id  m = OrdRef m (RefState m)
-- | reference identifiers
type Ids m = OrdRefSet m (RefState m)

-- | trigger identifier
type TId  m = OrdRef m (TriggerState m)
-- | trigger identifiers
type TIds m = OrdRefSet m (TriggerState m)

-- | IORef with Ord instance
type OrdRef    m a = (Int, SimpleRef m a)
-- | IORefs with Ord instance
type OrdRefSet m a = Map.IntMap (SimpleRef m a)

------------- data types for computations

-- reference reader monad
data RefReader m a
    = RefReader !(RefCreator m a)
    | RefReaderTPure a

-- reference creator monad
newtype RefCreator m a
    = RefCreator { unRefCreator :: GlobalVars m -> m a }

-- reference writer monad
newtype RefWriter m a
    = RefWriter { runRefWriterT :: RefCreator m a }
        deriving (Monad, Applicative, Functor, MonadFix)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handler.
type Handler m = RegionStatusChange -> m ()

type HandT (m :: * -> *) = m

------------------------------

newReadReference :: forall m a . RefContext m => GlobalVars m -> a -> (a -> m a) -> m (m a)
newReadReference st a0 ma = do

    (ih, a1) <- getDependency st $ ma a0

    if Map.null ih
      then return $ pure a1
      else do
        i <- newId st
        oir <- newSimpleRef $ RefState a1 mempty

        regTrigger st (i, oir) ih ma

        return $ getVal st oir i

getVal st oir i = do
    RefState a' _ <- readSimpleRef oir
    dp <- readSimpleRef (_dependencycoll st)
    writeSimpleRef (_dependencycoll st) $ Map.insert i oir dp
    return $ unsafeCoerce a'


newReference :: forall m a . RefContext m => GlobalVars m -> a -> m (Ref m a)
newReference st a0 = do

    i <- newId st
    oir <- newSimpleRef $ RefState a0 mempty

    let am :: RefReader m a
        am = RefReader $ RefCreator $ \st -> getVal st oir i

    let wr rep init upd = RefCreator $ \st -> do

            RefState aold_ nas <- readSimpleRef oir
            let aold = unsafeCoerce aold_ :: a

            let ma = upd

            (ih, a) <- getDependency st $ ma aold

            when init $ do

                writeSimpleRef oir $ RefState a nas

                when (not $ Map.null nas) $ do

                    let ch :: TId m -> m [TId m]
                        ch (_, n) = do
                            TriggerState _ (_, w) dep _ _ <- readSimpleRef n
                            RefState _ revDep <- readSimpleRef w
                            ls <- flip filterM (Map.toList revDep) $ \(_, na) -> do
                                TriggerState alive (i, _) _ _ _ <- readSimpleRef na
                                pure $ {-alive &&-} not (Map.member i dep)
                            return ls

                        collects p = mapM_ (collect p) =<< ch p

                        collect (i, op) v@(_, ov) = do
                            ts <- readSimpleRef ov
                            writeSimpleRef ov $ ts { _reverseDeps = Map.insert i op $ _reverseDeps ts }
                            when (Map.null $ _reverseDeps ts) $ collects v

                    let as = Map.toList nas
--                    as <- (`filterM` Map.toList nas) $ \(_, na) -> readSimpleRef na <&> _alive
                    mapM_ collects as

                    let topSort [] = return $ pure ()
                        topSort (p@(i, op):ps) = do
                            act <- readSimpleRef op <&> _updateFun

                            let del (_, n) = do
                                    ts <- readSimpleRef n
                                    let rd = Map.delete i $ _reverseDeps ts
                                    writeSimpleRef n $ ts { _reverseDeps = rd }
                                    return $ Map.null rd
                            ys <- filterM del =<< ch p
                            acts <- topSort $ mergeBy (\(i, _) (j, _) -> compare i j) ps ys
                            return $ act >> acts

                        del' (_, n) = readSimpleRef n <&> Map.null . _reverseDeps

                    join $ topSort =<< filterM del' as

                    p <- readSimpleRef (_postpone st)
                    writeSimpleRef (_postpone st) $ return ()
                    p

            when (rep && not (Map.null ih)) $ regTrigger st (i, oir) ih ma

    pure $ Ref $ \ff ->
        buildRefAction ff am
            (RefWriter . wr False True . (return .))
            (wr True)


regTrigger :: forall m a . RefContext m => GlobalVars m -> Id m -> Ids m -> (a -> m a) -> m ()
regTrigger st (i, oir) ih ma = do

    j <- newId st
    ori <- newSimpleRef $ error "impossible"

    let addRev, delRev :: SimpleRef m (RefState m) -> m ()
        addRev x = modSimpleRef x $ revDep %= Map.insert j ori
        delRev x = modSimpleRef x $ revDep %= Map.delete j

        modReg = do

            RefState aold nas <- readSimpleRef oir

            (ih, a) <- getDependency st $ ma $ unsafeCoerce aold

            writeSimpleRef oir $ RefState a nas

            ts <- readSimpleRef ori
            writeSimpleRef ori $ ts { _dependencies = ih }
            let ih' = _dependencies ts

            mapM_ delRev $ Map.elems $ ih' `Map.difference` ih
            mapM_ addRev $ Map.elems $ ih `Map.difference` ih'

    writeSimpleRef ori $ TriggerState True (i, oir) ih modReg mempty

    mapM_ addRev $ Map.elems ih

    tellHand st $ \msg -> do

        ts <- readSimpleRef ori
        writeSimpleRef ori $ ts { _alive = msg == Unblock }

        when (msg == Kill) $
            mapM_ delRev $ Map.elems $ _dependencies ts

        -- TODO
        when (msg == Unblock) $
            modSimpleRef (_postpone st) $ modify (>> _updateFun ts)

readRef__ :: RefContext m => GlobalVars m -> Ref m a -> m a
readRef__ st r = runRefReaderT' st $ readRef r

newRef :: RefContext m => a -> RefCreator m (Ref m a)
newRef a = RefCreator $ \st -> newReference st a

extendRef :: RefContext m => Ref m b -> Lens' a b -> a -> RefCreator m (Ref m a)
extendRef m k a0 = RefCreator $ \st -> do
    r <- newReference st a0
    -- TODO: remove getHandler?
    _ <- getHandler st $ do
        register st r True $ \a -> runRefReaderT' st $ readRef m <&> \b -> set k b a
        register st m False $ \_ -> readRef__ st r <&> (^. k)
    return r

onChange (RefReaderTPure a) f = RefReaderTPure <$> f a
onChange m f = RefCreator $ \st -> do
    r <- newReadReference st (const $ pure (), error "impossible #4") $ \(h, _) -> do
        a <- runRefReaderT' st m
        noDependency st $ do
            h Kill
            getHandler st . flip unRefCreator st $ f a
    tellHand st $ \msg -> do
        (h, _) <- r
        h msg
    return $ RefReader $ RefCreator $ \_ -> r <&> snd

onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
onChangeEq m f = RefCreator $ \st -> do
    r <- newReadReference st (const False, (const $ pure (), error "impossible #3")) $ \it@(p, (h, _)) -> do
        a <- runRefReaderT' st m
        noDependency st $ if p a
          then return it
          else do
            h Kill
            hb <- getHandler st $ flip unRefCreator st $ f a
            return ((== a), hb)
    tellHand st $ \msg -> do
        (_, (h, _)) <- r
        h msg

    return $ RefReader $ RefCreator $ \_ -> r <&> snd . snd

onChangeEq_ :: (Eq a, RefContext m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChangeEq_ m f = RefCreator $ \st -> do
    r <- newReference st (const False, (const $ pure (), error "impossible #3"))
    register st r True $ \it@(p, (h', _)) -> do
        a <- runRefReaderT' st m
        noDependency st $ if p a
          then return it
          else do
            h' Kill
            (h, b) <- getHandler st $ flip unRefCreator st $ f a
            return ((== a), (h, b))
    tellHand st $ \msg -> do
        (_, (h, _)) <- readRef__ st r
        h msg

    return $ lensMap (_2 . _2) r

onChangeMemo (RefReaderTPure a) f = fmap RefReaderTPure $ join $ f a
onChangeMemo (RefReader mr) f = RefCreator $ \st -> do
    r <- newReadReference st ((const False, ((error "impossible #2", const $ pure (), const $ pure ()) , error "impossible #1")), [])
      $ \st'@((p, ((m'',h1'',h2''), _)), memo) -> do
        let it = (p, (m'', h1''))
        a <- flip unRefCreator st mr
        noDependency st $ if p a
          then return st'
          else do
            h2'' Kill
            h1'' Block
            case listToMaybe [ b | (p, b) <- memo, p a] of
              Just (m',h1') -> do
                h1' Unblock
                (h2, b') <- getHandler st m'
                return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
              Nothing -> do
                (h1, m_) <- getHandler st $ flip unRefCreator st $ f a
                let m' = flip unRefCreator st m_
                (h2, b') <- getHandler st m'
                return (((== a), ((m',h1,h2), b')), it: memo)

    tellHand st $ \msg -> do
        ((_, ((_, h1, h2), _)), _) <- r
        h1 msg >> h2 msg

    return $ RefReader $ RefCreator $ \_ -> r <&> snd . snd . fst

onRegionStatusChange :: RefContext m => (RegionStatusChange -> m ()) -> RefCreator m ()
onRegionStatusChange h
    = RefCreator $ \st -> tellHand st h

onRegionStatusChange_ :: RefContext m => (RegionStatusChange -> RefReader m (m ())) -> RefCreator m ()
onRegionStatusChange_ h
    = RefCreator $ \st -> tellHand st $ join . runRefReaderT' st . h


runRefCreator
    :: RefContext m
    => ((forall b . RefWriter m b -> m b) -> RefCreator m a)
    -> m a
runRefCreator f = do
    s <- GlobalVars
            <$> newSimpleRef (const $ pure ())
            <*> newSimpleRef mempty
            <*> newSimpleRef (return ())
            <*> newSimpleRef 0
    flip unRefCreator s $ f $ flip unRefCreator s . runRefWriterT

-------------------- aux

register :: RefContext m => GlobalVars m -> Ref m a -> Bool -> (a -> HandT m a) -> m ()
register st r init k = flip unRefCreator st $ runRegisterAction (runRef r k) init

runRefReaderT :: RefContext m => RefReader m a -> RefCreator m a
runRefReaderT (RefReaderTPure a) = return a
runRefReaderT (RefReader x) = x

{-# INLINE runRefReaderT' #-}
runRefReaderT' st = flip unRefCreator st . runRefReaderT

--tellHand :: RefContext m => Handler m -> m ()
tellHand st h = modSimpleRef (_handlercollection st) $ modify $ \f msg -> f msg >> h msg

--getHandler :: RefContext m => RefCreator m a -> RefCreator m (Handler m, a)
getHandler st m = do
    let r = _handlercollection st
    h' <- readSimpleRef r
    writeSimpleRef r $ const $ pure ()
    a <- m
    h <- readSimpleRef r
    writeSimpleRef r h'
    return (h, a)

noDependency :: RefContext m => GlobalVars m -> m a -> m a
noDependency st m = do
    ih <- readSimpleRef $ _dependencycoll st
    a <- m
    writeSimpleRef (_dependencycoll st) ih
    return a



getDependency :: RefContext m => GlobalVars m -> m a -> m (Ids m, a)
getDependency st m = do
    ih' <- readSimpleRef $ _dependencycoll st       -- TODO: remove this
    writeSimpleRef (_dependencycoll st) mempty
    a <- m
    ih <- readSimpleRef $ _dependencycoll st
    writeSimpleRef (_dependencycoll st) ih'       -- TODO: remove this
    return (ih, a)

newId :: RefContext m => GlobalVars m -> m Int
newId (GlobalVars _ _ _ st) = do
    c <- readSimpleRef st
    writeSimpleRef st $ succ c
    return c

revDep :: Lens' (RefState m) (TIds m)
revDep k (RefState a b) = k b <&> \b' -> RefState a b'

------------------------------------------------------- type class instances

instance RefContext m => Monoid (RefCreator m ()) where
    mempty = return ()
    m `mappend` n = m >> n

instance RefContext m => Monad (RefCreator m) where
    return = RefCreator . const . return
    RefCreator m >>= f = RefCreator $ \r -> m r >>= \a -> unRefCreator (f a) r

instance RefContext m => Applicative (RefCreator m) where
    pure = RefCreator . const . pure
    RefCreator f <*> RefCreator g = RefCreator $ \r -> f r <*> g r

instance RefContext m => Functor (RefCreator m) where
    fmap f (RefCreator m) = RefCreator $ fmap f . m

instance (RefContext m, MonadFix m) => MonadFix (RefCreator m) where
    mfix f = RefCreator $ \r -> mfix $ \a -> unRefCreator (f a) r

instance RefContext m => Functor (RefReader m) where
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f (RefReader m) = RefReader $ fmap f m

instance RefContext m => Applicative (RefReader m) where
    pure = RefReaderTPure
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReader $ runRefReaderT mf <*> runRefReaderT ma
      where
        runRefReaderT (RefReaderTPure a) = pure a
        runRefReaderT (RefReader x) = x

instance RefContext m => Monad (RefReader m) where
    return = RefReaderTPure
    RefReaderTPure r >>= f = f r
    RefReader mr >>= f = RefReader $ mr >>= runRefReaderT . f



currentValue (RefReaderTPure a) = RefReaderTPure a
currentValue (RefReader (RefCreator m)) = RefReader $ RefCreator $ \st -> noDependency st $ m st

readRef :: RefContext m => Ref m a -> RefReader m a
readRef r = runReaderAction $ runRef r Const

readerToCreator :: RefContext m => RefReader m a -> RefCreator m a
readerToCreator = runRefReaderT

readerToWriter :: RefContext m => RefReader m a -> RefWriter m a
readerToWriter = RefWriter . runRefReaderT

instance MonadTrans RefWriter where
    lift = RefWriter . lift

instance MonadTrans RefCreator where
    lift m = RefCreator $ \_ -> m

wr = runRefWriterT

------------------------


newtype Ref m a = Ref { runRef :: Ref_ m a }

type Ref_ m a =
        forall f
        .  (RefAction f, RefActionCreator f ~ m)
        => (a -> RefActionFunctor f a)
        -> f ()

class ( Functor (RefActionFunctor f)
      , RefContext (RefActionCreator f)
      )
    => RefAction (f :: * -> *) where

    type RefActionFunctor f :: * -> *
    type RefActionCreator f :: * -> *

    buildRefAction
        :: (a -> RefActionFunctor f a)
        -> RefReader (RefActionCreator f) a
        -> ((a -> a) -> RefWriter (RefActionCreator f) ())
        -> RefRegOf (RefActionCreator f) a
        -> f ()

    joinRefAction :: RefReader (RefActionCreator f) (f ()) -> f ()

    buildUnitRefAction :: (() -> RefActionFunctor f ()) -> f ()

type RefRegOf m a = Bool -> (a -> HandT m a) -> RefCreator m ()


-------------------- reader action

newtype ReaderAction b m a = ReaderAction { runReaderAction :: RefReader m b }

instance
    ( RefContext m
    ) => RefAction (ReaderAction b m) where

    type RefActionFunctor (ReaderAction b m) = Const b
    type RefActionCreator (ReaderAction b m) = m

    buildRefAction f a _ _ = ReaderAction $ a <&> getConst . f
    joinRefAction m      = ReaderAction $ m >>= runReaderAction
    buildUnitRefAction f = ReaderAction $ pure $ getConst $ f ()


-------------------- writer action

newtype WriterAction m a = WriterAction { runWriterAction :: RefWriter m () }

instance
    ( RefContext m
    ) => RefAction (WriterAction m) where

    type RefActionFunctor (WriterAction m) = Identity
    type RefActionCreator (WriterAction m) = m

    buildRefAction f _ g _ = WriterAction $ g $ runIdentity . f
    joinRefAction m = WriterAction $ readerToWriter m >>= runWriterAction
    buildUnitRefAction _ = WriterAction $ pure ()

-------------------- register action

newtype RegisterAction m a = RegisterAction { runRegisterAction :: Bool -> RefCreator m a }

instance RefContext m => RefAction (RegisterAction m) where
    type RefActionFunctor (RegisterAction m) = HandT m
    type RefActionCreator (RegisterAction m) = m

    buildRefAction f _ _ g = RegisterAction $ \init -> g init f
    joinRefAction m = RegisterAction $ \init -> RefCreator $ \st -> do

        r <- newReadReference st (const $ pure ()) $ \kill -> do
            kill Kill
            noDependency st . fmap fst . getHandler st . flip unRefCreator st . ($ init) . runRegisterAction
                =<< runRefReaderT' st m
        tellHand st $ \msg -> r >>= ($ msg)

    buildUnitRefAction _ = RegisterAction $ const $ pure ()



infixr 8 `lensMap`

{- | Apply a lens on a reference.
-}
lensMap :: Lens' a b -> Ref m a -> Ref m b
lensMap k (Ref r) = Ref $ r . k

{- | unit reference
-}
unitRef :: RefContext m => Ref m ()
unitRef = Ref buildUnitRefAction

joinRef :: RefContext m => RefReader m (Ref m a) -> Ref m a
joinRef mr = Ref $ \f -> joinRefAction (mr <&> \r -> runRef r f)

----------------------

writeRef :: RefContext m => Ref m a -> a -> RefWriter m ()
writeRef (Ref r) = id . runWriterAction . r . const . Identity

modRef :: RefContext m => Ref m a -> (a -> a) -> RefWriter m ()
r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

memoRead :: RefContext m => RefCreator m a -> RefCreator m (RefCreator m a)
memoRead g = do
    s <- newRef Nothing
    pure $ readerToCreator (readRef s) >>= \x -> case x of
        Just a -> pure a
        _ -> g >>= \a -> do
            wr $ writeRef s $ Just a
            pure a

---------------- aux

mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy _ [] xs = xs
mergeBy _ xs [] = xs
mergeBy p (x:xs) (y:ys) = case p x y of
    LT -> x: mergeBy p xs (y:ys)
    GT -> y: mergeBy p (x:xs) ys
    EQ -> x: mergeBy p xs ys

--------------------------------------------------------------------------------
#endif
--------------------------------------------------------------------------------

-- | TODO
data RegionStatusChange = Kill | Block | Unblock deriving (Eq, Ord, Show)


instance (IsString str, RefContext s) => IsString (RefReader s str) where
    fromString = pure . fromString

instance (RefContext s, Num a) => Num (RefReader s a) where
    (+) = liftA2 (+)
    (*) = liftA2 (*)
    negate = fmap negate
    abs    = fmap abs
    signum = fmap signum
    fromInteger = pure . fromInteger

instance (RefContext s, Fractional a) => Fractional (RefReader s a) where
    recip  = fmap recip
    fromRational = pure . fromRational

