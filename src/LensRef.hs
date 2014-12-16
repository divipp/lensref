{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{- |
lensref core API
-}
module LensRef
    ( -- * Monads
      RefReader
    , RefCreator
    , RefWriter
    , readerToWriter
    , readerToCreator
    , runRefCreator

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
    , onChange_
    , onChangeEq
    , onChangeEq_
    , onChangeEqOld
    , onChangeEqOld'
    , onChangeMemo

    -- * Other
    , currentValue
    , RegionStatusChange (..)
    , onRegionStatusChange
    , onRegionStatusChange_

    -- * Reference context
    , RefContext (..)
    ) where

import Data.Function
import Data.Maybe
import Data.String
import Data.IORef
import Data.STRef
import qualified Data.IntMap.Strict as Map
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.ST (ST)
import Lens.Family2
import Lens.Family2.Stock (_2)
import Debug.Trace

import qualified Unsafe.Coerce

infixr 8 `lensMap`

----------------------------------- data types

-- | reference temporal state
data RefState m where
    RefState
        :: a        -- reference value
        -> Int      -- in which write cycle was the value read or written last time
        -> TIds m   -- registered triggers (run them if the value changes)
        -> RefState m

-- | trigger temporal state
data TriggerState m = TriggerState
    { _alive        :: Bool       -- ^ the trigger is not in the inactive part of the network
    , _targetid     :: (Id m)     -- ^ target reference id
    , _dependencies :: (Ids m)    -- ^ source reference ids
    , _updateFun    :: (RefCreator m ())     -- ^ what to run if at least one of the source ids changes
    , _reverseDeps  :: (TIds m)   -- ^ reverse dependencies (temporarily needed during topological sorting)
    }
{-
    , _scheduleInfo :: ScheduleInfo m   -- ^ temporarily needed during topological sorting
    }

-- if 
data ScheduleInfo m = ScheduleInfo
    { _reverseDeps  :: TIds m   -- ^ reverse dependencies
    , _children     :: TIds m   -- ^ dependencies
    }
-}
-- | global variables
data GlobalVars m = GlobalVars
    { _handlercollection  :: !(SimpleRef m (Handler m))  -- ^ collected handlers
    , _dependencycoll     :: !(SimpleRef m (Ids m))      -- ^ collected dependencies
    , _postpone           :: !(SimpleRef m (RefCreator m ()))       -- ^ postponed actions
    , _counter            :: !(SimpleRef m Int)          -- ^ increasing counter
    , _writeCounter       :: !(SimpleRef m Int)
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
data OrdRef m a = OrdRef
    { _ordRefId  :: !Int
    , _ordRefRef :: SimpleRef m a
    }
-- | IORefs with Ord instance
type OrdRefSet m a = Map.IntMap (SimpleRef m a)

-- | reference reader monad
newtype RefReader m a
    = RefReader { readerToCreator :: RefCreator m a }
        deriving (Monad, Applicative, Functor, MonadFix)

-- | reference creator monad
newtype RefCreator m a
    = RefCreator { unRefCreator :: GlobalVars m -> m a }

-- | reference writer monad
newtype RefWriter m a
    = RefWriter { unsafeWriterToCreator :: RefCreator m a }
        deriving (Monad, Applicative, Functor, MonadFix)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handler.
type Handler m = RegionStatusChange -> RefCreator m ()

-- | TODO
data RegionStatusChange = Kill | Block | Unblock deriving (Eq, Ord, Show)

------------------------------

newReadReference :: forall m a . RefContext m => a -> (a -> RefCreator m a) -> RefCreator m (RefReader m a)
newReadReference a0 ma = do
    (ih, a1) <- getDependency $ ma a0
    if Map.null ih
      then return $ pure a1
      else do
        i <- newId' a1
        regTrigger i ih ma
        return $ getVal i

newRef :: forall m a . RefContext m => a -> RefCreator m (Ref m a)
newRef a0 = snd <$> newRef_ a0

newRef_ :: forall m a . RefContext m => a -> RefCreator m (OrdRef m (RefState m), Ref m a)
newRef_ a0 = do
    p@(OrdRef _ oir) <- newId' a0

    let am :: RefReader m a
        am = getVal p

        ff rep upd init = do

            ih <- case init of
              Just ih -> return ih
              Nothing -> do

                rs@(RefState _ _ nas) <- RefCreator $ \st -> do
                    wr <- readSimpleRef (_writeCounter st)
                    modSimpleRef'' oir (setWr wr)               -- (setWr wr) is not needed, id is enough

                (ih, a) <- getDependency $ upd (unsafeGetVal rs :: a)

                RefCreator $ \st -> do
                    wr <- modSimpleRef'' (_writeCounter st) succ
                    writeSimpleRef oir $ RefState a wr nas

                when (not $ Map.null nas) $ do

                    let ch :: TId m -> RefCreator m [TId m]
                        ch (OrdRef _ n) = do
                            TriggerState { _targetid = OrdRef _ w, _dependencies } <- readSimpleRef n
                            RefState _ _ revDep <- readSimpleRef w
                            flip filterM (uncurry OrdRef <$> Map.toList revDep) $ \(OrdRef _ na) -> do
                                TriggerState { _alive, _targetid = OrdRef i _ } <- readSimpleRef na
                                pure $ {-alive &&-} Map.notMember i _dependencies

                        collects p@(OrdRef i op) = mapM_ collect =<< ch p
                          where
                            collect v@(OrdRef _ ov) = do
                                ts <- modSimpleRef' ov $ \ts -> ts { _reverseDeps = Map.insert i op $ _reverseDeps ts }
                                when (Map.null $ _reverseDeps ts) $ collects v

                    let as = uncurry OrdRef <$> Map.toList nas
--                    as <- (`filterM` Map.toList nas) $ \(_, na) -> _alive <$> readSimpleRef na
                    mapM_ collects as

                    let topSort [] = return $ pure ()
                        topSort (p@(OrdRef i op):ps) = do
                            act <- _updateFun <$> readSimpleRef op
                            ys <- filterM del =<< ch p      -- TODO: don't use ch here again, cache it
                            acts <- topSort $ mergeBy (compare `on` _ordRefId) ps ys
                            return $ act >> acts
                          where
                            del (OrdRef _ n) = do
                                ts <- modSimpleRef'' n $ \ts -> ts { _reverseDeps = Map.delete i $ _reverseDeps ts }
                                return $ Map.null $ _reverseDeps ts

                    join $ topSort =<< filterM (fmap (Map.null . _reverseDeps) . readSimpleRef . _ordRefRef) as

                    join $ RefCreator $ \st -> modSimpleRef' (_postpone st) $ const $ return ()

                return ih

            when (rep && not (Map.null ih)) $ regTrigger p ih upd

    pure (p, Ref $ buildRefAction am ff)


regTrigger :: forall m a . RefContext m => Id m -> Ids m -> (a -> RefCreator m a) -> RefCreator m ()
regTrigger p@(OrdRef _ oir) ih ma = do

    j <- newId
    ori <- newSimpleRef $ error "impossible"

    let addRev x = modSimpleRef x $ revDep %~ Map.insert j ori
        delRev x = modSimpleRef x $ revDep %~ Map.delete j

        modReg = do
            rs@(RefState _ wr nas) <- RefCreator $ \st -> do
                wr <- readSimpleRef (_writeCounter st)
                modSimpleRef'' oir (setWr' wr)
            (ih, a) <- getDependency $ ma $ unsafeGetVal rs
            writeSimpleRef oir $ RefState a wr nas

            ts <- modSimpleRef' ori $ \ts -> ts { _dependencies = ih }
            let ih' = _dependencies ts

            mapM_ delRev $ Map.elems $ ih' `Map.difference` ih
            mapM_ addRev $ Map.elems $ ih `Map.difference` ih'

    writeSimpleRef ori $ TriggerState
        { _alive        = True
        , _targetid     = p
        , _dependencies = ih
        , _updateFun    = modReg
        , _reverseDeps  = mempty
        }

    mapM_ addRev $ Map.elems ih

    tellHandler $ \msg -> do
        ts <- modSimpleRef' ori $ \ts -> ts { _alive = msg == Unblock }
        when (msg == Kill) $ mapM_ delRev $ Map.elems $ _dependencies ts

        -- TODO
        when (msg == Unblock) $ RefCreator $ \st ->
            modSimpleRef (_postpone st) (>> _updateFun ts)

extendRef :: RefContext m => Ref m b -> Lens' a b -> a -> RefCreator m (Ref m a)
extendRef m k a0 = do
    (OrdRef i p, r) <- newRef_ a0
    -- TODO: remove getHandler?
    _ <- getHandler $ do
        register r $ \a -> readerToCreator $ (\b -> set k b a) <$> readRef m
        register' m (Map.singleton i p) $ readerToCreator $ (^. k) <$> readRef r
    return r

onChange :: RefContext m => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChange m f = do
    r <- newReadReference (const $ pure (), error "impossible #4") $ \(h, _) -> do
        a <- readerToCreator m
        noDependency $ do
            h Kill
            getHandler $ f a
    tellHandler $ \msg -> do
        (h, _) <- readerToCreator r
        h msg
    return $ snd <$> r


onChange_ :: RefContext m => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChange_ m f = do
    r <- newRef (const $ pure (), error "impossible #3")
    register r $ \(h', _) -> do
        a <- readerToCreator m
        noDependency $ do
            h' Kill
            (h, b) <- getHandler $ f a
            return (h, b)
    tellHandler $ \msg -> do
        (h, _) <- readerToCreator $ readRef r
        h msg

    return $ lensMap _2 r

onChangeEq :: (Eq a, RefContext m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEq m f = do
    r <- newReadReference (const False, (const $ pure (), error "impossible #3")) $ \it@(p, (h, _)) -> do
        a <- readerToCreator m
        noDependency $ if p a
          then return it
          else do
            h Kill
            hb <- getHandler $ f a
            return ((== a), hb)
    tellHandler $ \msg -> do
        (_, (h, _)) <- readerToCreator r
        h msg

    return $ snd . snd <$> r

onChangeEqOld :: (Eq a, RefContext m) => RefReader m a -> (a -> a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEqOld m f = do
    x <- readerToCreator m
    r <- newReadReference ((x, const False), (const $ pure (), error "impossible #3")) $ \it@((x, p), (h, _)) -> do
        a <- readerToCreator m
        noDependency $ if p a
          then return it
          else do
            h Kill
            hb <- getHandler $ f x a
            return ((a, (== a)), hb)
    tellHandler $ \msg -> do
        (_, (h, _)) <- readerToCreator r
        h msg

    return $ snd . snd <$> r

onChangeEqOld' :: (Eq a, RefContext m) => RefReader m a -> b -> (Ref m b -> a -> b -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEqOld' m b0 f = do
    r <- newRef ((const False), (const $ pure (), b0))
    register r $ \it@(p, (h, b)) -> do
        a <- readerToCreator m
        noDependency $ if p a
          then return it
          else do
            h Kill
            hb <- getHandler $ f (lensMap (_2 . _2) r) a b
            return ((== a), hb)
    tellHandler $ \msg -> do
        (_, (h, _)) <- readerToCreator $ readRef r
        h msg

    return $ snd . snd <$> readRef r

onChangeEq_ :: (Eq a, RefContext m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChangeEq_ m f = do
    r <- newRef (const False, (const $ pure (), error "impossible #3"))
    register r $ \it@(p, (h', _)) -> do
        a <- readerToCreator m
        noDependency $ if p a
          then return it
          else do
            h' Kill
            (h, b) <- getHandler $ f a
            return ((== a), (h, b))
    tellHandler $ \msg -> do
        (_, (h, _)) <- readerToCreator $ readRef r
        h msg

    return $ lensMap (_2 . _2) r

onChangeMemo :: (RefContext m, Eq a) => RefReader m a -> (a -> RefCreator m (RefCreator m b)) -> RefCreator m (RefReader m b)
onChangeMemo mr f = do
    r <- newReadReference ((const False, ((error "impossible #2", const $ pure (), const $ pure ()) , error "impossible #1")), [])
      $ \st'@((p, ((m'',h1'',h2''), _)), memo) -> do
        let it = (p, (m'', h1''))
        a <- readerToCreator mr
        noDependency $ if p a
          then return st'
          else do
            h2'' Kill
            h1'' Block
            case listToMaybe [ b | (p, b) <- memo, p a] of
              Just (m',h1') -> do
                h1' Unblock
                (h2, b') <- getHandler m'
                return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
              Nothing -> do
                (h1, m_) <- getHandler $ f a
                let m' = m_
                (h2, b') <- getHandler m'
                return (((== a), ((m',h1,h2), b')), it: memo)

    tellHandler $ \msg -> do
        ((_, ((_, h1, h2), _)), _) <- readerToCreator r
        h1 msg >> h2 msg

    return $ snd . snd . fst <$> r

onRegionStatusChange :: RefContext m => (RegionStatusChange -> m ()) -> RefCreator m ()
onRegionStatusChange h
    = onRegionStatusChange_ (return . h)

onRegionStatusChange_ :: RefContext m => (RegionStatusChange -> RefReader m (m ())) -> RefCreator m ()
onRegionStatusChange_ h
    = tellHandler $ join . fmap lift . readerToCreator . h

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
            <*> newSimpleRef 0
    flip unRefCreator s $ f $ flip unRefCreator s . unsafeWriterToCreator

-------------------- aux

tellHandler :: RefContext m => Handler m -> RefCreator m ()
tellHandler h = RefCreator $ \st -> modSimpleRef (_handlercollection st) (`mappend` h)

getHandler :: RefContext m => RefCreator m a -> RefCreator m (Handler m, a)
getHandler (RefCreator m) = RefCreator $ \st -> do
    h' <- modSimpleRef' (_handlercollection st) $ const $ const $ pure ()
    a <- m st
    h <- modSimpleRef' (_handlercollection st) $ const h'
    return (h, a)

getDependency :: RefContext m => RefCreator m a -> RefCreator m (Ids m, a)
getDependency (RefCreator m) = RefCreator $ \st -> do
    ih' <- modSimpleRef' (_dependencycoll st) $ const mempty
    a <- m st
    ih <- modSimpleRef' (_dependencycoll st) $ const ih'
    return (ih, a)

noDependency :: RefContext m => RefCreator m a -> RefCreator m a
noDependency = fmap snd . getDependency

newId' a = do
    wr <- RefCreator $ \st -> readSimpleRef (_writeCounter st)
    liftA2 OrdRef newId $ newSimpleRef $ RefState a wr mempty

newId :: RefContext m => RefCreator m Int
newId = RefCreator $ \st -> modSimpleRef' (_counter st) succ

revDep :: Lens' (RefState m) (TIds m)
revDep k (RefState a wr b) = RefState a wr <$> k b

currentValue :: RefContext m => RefReader m a -> RefReader m a
currentValue = RefReader . noDependency . readerToCreator

readerToWriter :: RefContext m => RefReader m a -> RefWriter m a
readerToWriter = RefWriter . readerToCreator

getVal (OrdRef i oir) = RefReader $ RefCreator $ \st -> do
    modSimpleRef (_dependencycoll st) $ Map.insert i oir
    wr <- readSimpleRef (_writeCounter st)
    unsafeGetVal <$> modSimpleRef'' oir (setWr wr)

setWr wr (RefState a _ x) = RefState a wr x

setWr' wr r@(RefState _ wr' _)
    | wr > wr' = setWr wr r
    | otherwise = error $ "I can't schedule this trigger network; " ++ show wr' ++ " >= " ++ show wr

unsafeGetVal :: RefState m -> a
unsafeGetVal (RefState a _ _) = Unsafe.Coerce.unsafeCoerce a

--------------------------------------------------------------------------------

newtype Ref m a
    = Ref { runRef :: forall f . (RefAction f, Functor (RefActionFunctor f), RefActionCreator f ~ m)
                   => (a -> RefActionFunctor f a) -> f ()
          }

class RefAction f where
    type RefActionFunctor f :: * -> *
    type RefActionCreator f :: * -> *

    joinRefAction :: RefReader (RefActionCreator f) (f ()) -> f ()
    buildRefAction
        :: RefReader (RefActionCreator f) a
        -> (Bool -> (a -> RefCreator (RefActionCreator f) a) -> Maybe (Ids (RefActionCreator f)) -> RefCreator (RefActionCreator f) ())
        -> (a -> RefActionFunctor f a) -> f ()

-- | Apply a lens on a reference.
lensMap :: Lens' a b -> Ref m a -> Ref m b
lensMap k r = Ref $ runRef r . k

-- | unit reference
unitRef :: RefContext m => Ref m ()
unitRef = Ref $ buildRefAction (pure ()) (\_ _ _ -> pure ())

joinRef :: RefContext m => RefReader m (Ref m a) -> Ref m a
joinRef mr = Ref $ joinRefAction . (<$> mr) . flip runRef

writeRef :: RefContext m => Ref m a -> a -> RefWriter m ()
writeRef r = runWriterAction . runRef r . const . Identity

newtype WriterAction m a = WriterAction { runWriterAction :: RefWriter m () }

instance RefContext m => RefAction (WriterAction m) where
    type RefActionFunctor (WriterAction m) = Identity
    type RefActionCreator (WriterAction m) = m
    buildRefAction _   g = WriterAction . (\f -> RefWriter $ g False (pure . runIdentity . f) Nothing)
    joinRefAction        = WriterAction . (>>= runWriterAction) . readerToWriter

readRef :: RefContext m => Ref m a -> RefReader m a
readRef r = runReaderAction $ runRef r Const

newtype ReaderAction m b a = ReaderAction { runReaderAction :: RefReader m b }

instance RefContext m => RefAction (ReaderAction m b) where
    type RefActionFunctor (ReaderAction m b) = Const b
    type RefActionCreator (ReaderAction m b) = m
    buildRefAction a   _ = ReaderAction . (<$> a) . (getConst .)
    joinRefAction        = ReaderAction . (>>= runReaderAction)

-- TODO: optimize this
-- | > modRef r f = readerToWriter (readRef r) >>= writeRef r . f
modRef :: RefContext m => Ref m a -> (a -> a) -> RefWriter m ()
r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

register :: RefContext m => Ref m a -> (a -> RefCreator m a) -> RefCreator m ()
register r k = runRegisterAction (runRef r k) Nothing

register' :: RefContext m => Ref m a -> Ids m -> RefCreator m a -> RefCreator m ()
register' r dep k = runRegisterAction (runRef r $ const k) (Just dep)

newtype RegisterAction m a = RegisterAction { runRegisterAction :: Maybe (Ids m) -> RefCreator m a }

instance RefContext m => RefAction (RegisterAction m) where
    type RefActionFunctor (RegisterAction m) = RefCreator m
    type RefActionCreator (RegisterAction m) = m
    buildRefAction _   g = RegisterAction . g True
    joinRefAction m      = RegisterAction $ \init -> do
        r <- newReadReference (const $ pure ()) $ \kill -> do
            kill Kill
            noDependency . fmap fst . getHandler . ($ init) . runRegisterAction =<< readerToCreator m
        tellHandler $ \msg -> readerToCreator r >>= ($ msg)

--------------------------------------------------------------------------------

memoRead :: RefContext m => RefCreator m a -> RefCreator m (RefCreator m a)
memoRead g = do
    s <- newRef Nothing
    pure $ readerToCreator (readRef s) >>= \case
        Just a -> pure a
        Nothing -> g >>= \a -> a <$ unsafeWriterToCreator (writeRef s $ Just a)

------------------------------------------------------- type class instances

instance MonadTrans RefWriter  where lift = RefWriter . lift
instance MonadTrans RefCreator where lift = RefCreator . const

instance RefContext m => Functor (RefCreator m) where
    fmap f (RefCreator m) = RefCreator $ fmap f . m

instance RefContext m => Applicative (RefCreator m) where
    pure = RefCreator . const . pure
    RefCreator f <*> RefCreator g = RefCreator $ \r -> f r <*> g r

instance RefContext m => Monad (RefCreator m) where
    return = RefCreator . const . return
    RefCreator m >>= f = RefCreator $ \r -> m r >>= \a -> unRefCreator (f a) r

-- TODO: move MonadFix instances to Unsafe module
instance (RefContext m, MonadFix m) => MonadFix (RefCreator m) where
    mfix f = RefCreator $ \r -> mfix $ \a -> unRefCreator (f a) r

-- TODO: remove this
instance RefContext m => Monoid (RefCreator m ()) where
    mempty = pure ()
    m `mappend` n = m >> n

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

class (Monad m, Applicative m) => RefContext m where
    type SimpleRef m :: * -> *   -- simple reference
    newSimpleRef   :: a -> m (SimpleRef m a)
    readSimpleRef  :: SimpleRef m a -> m a
    writeSimpleRef :: SimpleRef m a -> a -> m ()

modSimpleRef :: RefContext m => SimpleRef m a -> (a -> a) -> m ()
modSimpleRef r f = readSimpleRef r >>= writeSimpleRef r . f

modSimpleRef' :: RefContext m => SimpleRef m a -> (a -> a) -> m a
modSimpleRef' r f = readSimpleRef r >>= \a -> writeSimpleRef r (f a) >> return a

modSimpleRef'' :: RefContext m => SimpleRef m a -> (a -> a) -> m a
modSimpleRef'' r f = readSimpleRef r >>= \a -> let fa = f a in writeSimpleRef r fa >> return fa

instance RefContext IO where
    type SimpleRef IO = IORef
--    {-# INLINE newSimpleRef #-}
    newSimpleRef x = newIORef x
--    {-# INLINE readSimpleRef #-}
    readSimpleRef r = readIORef r
--    {-# INLINE writeSimpleRef #-}
    writeSimpleRef r a = writeIORef r a

instance RefContext (ST s) where
    type SimpleRef (ST s) = STRef s
    newSimpleRef    = newSTRef
    readSimpleRef   = readSTRef
    writeSimpleRef  = writeSTRef

instance RefContext m => RefContext (ReaderT r m) where
    type SimpleRef (ReaderT r m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

instance (RefContext m, Monoid w) => RefContext (WriterT w m) where
    type SimpleRef (WriterT w m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

-- TODO: Is this needed? If not, move to Extra module
instance RefContext m => RefContext (RefCreator m) where
    type SimpleRef (RefCreator m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

-------------------------------------------------------------------------------- aux

mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy p (x:xs) (y:ys) = case p x y of
    LT -> x: mergeBy p xs (y:ys)
    GT -> y: mergeBy p (x:xs) ys
    EQ -> x: mergeBy p xs ys
mergeBy _ xs ys = xs ++ ys

