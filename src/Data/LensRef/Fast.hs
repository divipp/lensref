{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Fast implementation for the @MonadRefCreator@ interface.

TODO
- optimiziation: do not remember values
- optimiziation: equality check
-}
module Data.LensRef.Fast
    ( RefReaderT
    , RefCreatorT
    , RefWriterT
    , currentValue
    , readerToWriter
    , readerToCreator
    , runRefCreatorT
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

--import Debug.Trace
import Data.Maybe
import Data.Monoid
--import Data.IORef
import qualified Data.IntMap.Strict as Map
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Lens.Simple

import Unsafe.Coerce

--import Data.LensRef.Class
import Data.LensRef.Common

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
data RefReaderT m a
    = RefReaderT !(RefCreatorT m a)
    | RefReaderTPure a

-- reference creator monad
newtype RefCreatorT m a
    = RefCreatorT { unRefCreator :: GlobalVars m -> m a }

-- reference writer monad
newtype RefWriterT m a
    = RefWriterT { runRefWriterT :: RefCreatorT m a }
        deriving (Monad, Applicative, Functor, MonadFix)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handler.
type Handler m = RegionStatusChangeHandler m

type HandT (m :: * -> *) = m

------------------------------

newReadReference :: forall m a . SimpleRefClass m => GlobalVars m -> a -> (a -> m a) -> m (m a)
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


newReference :: forall m a . SimpleRefClass m => GlobalVars m -> a -> m (Ref m a)
newReference st a0 = do

    i <- newId st
    oir <- newSimpleRef $ RefState a0 mempty

    let am :: RefReaderT m a
        am = RefReaderT $ RefCreatorT $ \st -> getVal st oir i

    let wr rep init upd = RefCreatorT $ \st -> do

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
                                pure $ alive && not (Map.member i dep)
                            return ls

                        collects p = mapM_ (collect p) =<< ch p

                        collect (i, op) v@(_, ov) = do
                            ts <- readSimpleRef ov
                            writeSimpleRef ov $ ts { _reverseDeps = Map.insert i op $ _reverseDeps ts }
                            when (Map.null $ _reverseDeps ts) $ collects v

                    as <- (`filterM` Map.toList nas) $ \(_, na) -> readSimpleRef na <&> _alive
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
            (RefWriterT . wr False True . (return .))
            (wr True)


regTrigger :: forall m a . SimpleRefClass m => GlobalVars m -> Id m -> Ids m -> (a -> m a) -> m ()
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

readRef__ :: SimpleRefClass m => GlobalVars m -> Ref m a -> m a
readRef__ st r = runRefReaderT' st $ readRef r


--instance SimpleRefClass m => MonadRefCreator (RefCreatorT m) where
--    {-# SPECIALIZE instance MonadRefCreator (RefCreatorT IO) #-}

--    type RefReaderSimple (RefCreatorT m) = RefReaderT m
--    type RefRegOf (RefCreatorT m) a = Bool -> (a -> HandT m a) -> RefCreatorT m ()

newRef a = RefCreatorT $ \st -> newReference st a

extendRef :: SimpleRefClass m => Ref m b -> Lens' a b -> a -> RefCreatorT m (Ref m a)
extendRef m k a0 = RefCreatorT $ \st -> do
    r <- newReference st a0
    -- TODO: remove getHandler?
    _ <- getHandler st $ do
        register st r True $ \a -> runRefReaderT' st $ readRef m <&> \b -> set k b a
        register st m False $ \_ -> readRef__ st r <&> (^. k)
    return r

onChange (RefReaderTPure a) f = RefReaderTPure <$> f a
onChange m f = RefCreatorT $ \st -> do
    r <- newReadReference st (const $ pure (), error "impossible #4") $ \(h, _) -> do
        a <- runRefReaderT' st m
        noDependency st $ do
            h Kill
            getHandler st . flip unRefCreator st $ f a
    tellHand st $ \msg -> do
        (h, _) <- r
        h msg
    return $ RefReaderT $ RefCreatorT $ \_ -> r <&> snd

onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
onChangeEq m f = RefCreatorT $ \st -> do
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

    return $ RefReaderT $ RefCreatorT $ \_ -> r <&> snd . snd

onChangeEq_ m f = RefCreatorT $ \st -> do
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
onChangeMemo (RefReaderT mr) f = RefCreatorT $ \st -> do
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

    return $ RefReaderT $ RefCreatorT $ \_ -> r <&> snd . snd . fst

onRegionStatusChange h
    = RefCreatorT $ \st -> tellHand st h

runRefCreatorT :: SimpleRefClass m => ((forall b . RefWriterT m b -> m b) -> RefCreatorT m a) -> m a
runRefCreatorT f = do
    s <- GlobalVars
            <$> newSimpleRef (const $ pure ())
            <*> newSimpleRef mempty
            <*> newSimpleRef (return ())
            <*> newSimpleRef 0
    flip unRefCreator s $ f $ flip unRefCreator s . runRefWriterT

-------------------- aux

register :: SimpleRefClass m => GlobalVars m -> Ref m a -> Bool -> (a -> HandT m a) -> m ()
register st r init k = flip unRefCreator st $ runRegisterAction (runRef r k) init

runRefReaderT :: Monad m => RefReaderT m a -> RefCreatorT m a
runRefReaderT (RefReaderTPure a) = return a
runRefReaderT (RefReaderT x) = x

{-# INLINE runRefReaderT' #-}
runRefReaderT' st = flip unRefCreator st . runRefReaderT

--tellHand :: (SimpleRefClass m) => Handler m -> m ()
tellHand st h = modSimpleRef (_handlercollection st) $ modify $ \f msg -> f msg >> h msg

--getHandler :: SimpleRefClass m => RefCreatorT m a -> RefCreatorT m (Handler m, a)
getHandler st m = do
    let r = _handlercollection st
    h' <- readSimpleRef r
    writeSimpleRef r $ const $ pure ()
    a <- m
    h <- readSimpleRef r
    writeSimpleRef r h'
    return (h, a)

noDependency :: SimpleRefClass m => GlobalVars m -> m a -> m a
noDependency st m = do
    ih <- readSimpleRef $ _dependencycoll st
    a <- m
    writeSimpleRef (_dependencycoll st) ih
    return a



getDependency :: SimpleRefClass m => GlobalVars m -> m a -> m (Ids m, a)
getDependency st m = do
    ih' <- readSimpleRef $ _dependencycoll st       -- TODO: remove this
    writeSimpleRef (_dependencycoll st) mempty
    a <- m
    ih <- readSimpleRef $ _dependencycoll st
    writeSimpleRef (_dependencycoll st) ih'       -- TODO: remove this
    return (ih, a)

newId :: SimpleRefClass m => GlobalVars m -> m Int
newId (GlobalVars _ _ _ st) = do
    c <- readSimpleRef st
    writeSimpleRef st $ succ c
    return c

revDep :: Lens' (RefState m) (TIds m)
revDep k (RefState a b) = k b <&> \b' -> RefState a b'

------------------------------------------------------- type class instances

instance Monad m => Monoid (RefCreatorT m ()) where
    mempty = return ()
    m `mappend` n = m >> n

instance Monad m => Monad (RefCreatorT m) where
    return = RefCreatorT . const . return
    RefCreatorT m >>= f = RefCreatorT $ \r -> m r >>= \a -> unRefCreator (f a) r

instance Applicative m => Applicative (RefCreatorT m) where
    pure = RefCreatorT . const . pure
    RefCreatorT f <*> RefCreatorT g = RefCreatorT $ \r -> f r <*> g r

instance Functor m => Functor (RefCreatorT m) where
    fmap f (RefCreatorT m) = RefCreatorT $ fmap f . m

instance MonadFix m => MonadFix (RefCreatorT m) where
    mfix f = RefCreatorT $ \r -> mfix $ \a -> unRefCreator (f a) r

instance Functor m => Functor (RefReaderT m) where
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f (RefReaderT m) = RefReaderT $ fmap f m

instance Applicative m => Applicative (RefReaderT m) where
    pure = RefReaderTPure
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReaderT $ runRefReaderT mf <*> runRefReaderT ma
      where
        runRefReaderT (RefReaderTPure a) = pure a
        runRefReaderT (RefReaderT x) = x

instance Monad m => Monad (RefReaderT m) where
    return = RefReaderTPure
    RefReaderTPure r >>= f = f r
    RefReaderT mr >>= f = RefReaderT $ mr >>= runRefReaderT . f



currentValue (RefReaderTPure a) = RefReaderTPure a
currentValue (RefReaderT (RefCreatorT m)) = RefReaderT $ RefCreatorT $ \st -> noDependency st $ m st

readRef r = runReaderAction $ runRef r Const

readerToCreator = runRefReaderT

readerToWriter = RefWriterT . runRefReaderT

instance MonadTrans RefWriterT where
    lift = RefWriterT . lift

instance MonadTrans RefCreatorT where
    lift m = RefCreatorT $ \_ -> m

wr = runRefWriterT

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
        -> RefRegOf (RefActionCreator f) a
        -> f ()

    joinRefAction :: RefReaderT (RefActionCreator f) (f ()) -> f ()

    buildUnitRefAction :: (() -> RefActionFunctor f ()) -> f ()

type RefRegOf m a = Bool -> (a -> HandT m a) -> RefCreatorT m ()


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

newtype WriterAction m a = WriterAction { runWriterAction :: RefWriterT m () }

instance
    ( Applicative m, Monad m
    ) => RefAction (WriterAction m) where

    type RefActionFunctor (WriterAction m) = Identity
    type RefActionCreator (WriterAction m) = m

    buildRefAction f _ g _ = WriterAction $ g $ runIdentity . f
    joinRefAction m = WriterAction $ readerToWriter m >>= runWriterAction
    buildUnitRefAction _ = WriterAction $ pure ()

-------------------- register action

newtype RegisterAction m a = RegisterAction { runRegisterAction :: Bool -> RefCreatorT m a }

instance SimpleRefClass m => RefAction (RegisterAction m) where
    type RefActionFunctor (RegisterAction m) = HandT m
    type RefActionCreator (RegisterAction m) = m

    buildRefAction f _ _ g = RegisterAction $ \init -> g init f
    joinRefAction m = RegisterAction $ \init -> RefCreatorT $ \st -> do

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

--    id :: RefWriterT m a -> m a

writeRef (Ref r) = id . runWriterAction . r . const . Identity

r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

--onChangeEq r f = fmap readRef $ onChangeEq_ r f


memoRead :: SimpleRefClass m => RefCreatorT m a -> RefCreatorT m (RefCreatorT m a) 
memoRead g = do
    s <- newRef Nothing
    pure $ readerToCreator (readRef s) >>= \x -> case x of
        Just a -> pure a
        _ -> g >>= \a -> do
            wr $ writeRef s $ Just a
            pure a



