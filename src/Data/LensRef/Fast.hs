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
    , runRefCreatorT
    ) where

--import Debug.Trace
import Data.Maybe
import Data.Monoid
--import Data.IORef
import qualified Data.IntMap.Strict as Map
import Control.Applicative
import Control.Monad.State.Strict
--import Control.Monad.Identity
import Control.Lens.Simple

import Unsafe.Coerce

import Data.LensRef.Class
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

-- | reference handler
newtype RefHandler m a = RefHandler
    { runRefHandler
        :: forall b
        .  (a -> RefFunctor m b a)
        -> m (b, Bool -> m ()) -- True: run the trigger initially also
    }

newtype RefFunctor m b a = RefFunctor { runRefFunctor :: (b, m a) }

instance Functor m => Functor (RefFunctor m b) where
    fmap f (RefFunctor (b, m)) = RefFunctor (b, fmap f m)

-- | global variables
data GlobalVars m = GlobalVars
    { _handlercollection  :: !(SimpleRefOf m (Handler m))  -- ^ collected handlers
    , _dependencycoll     :: !(SimpleRefOf m (Ids m))      -- ^ collected dependencies
    , _postpone           :: !(SimpleRefOf m (m ()))       -- ^ postponed actions
    , _counter            :: !(SimpleRefOf m Int)          -- ^ increasing counter
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
type OrdRef    m a = (Int, SimpleRefOf m a)
-- | IORefs with Ord instance
type OrdRefSet m a = Map.IntMap (SimpleRefOf m a)


------------- data types for computations

-- reference reader monad
data RefReaderT m a
    = RefReaderT !(RefCreatorT m a)
    | RefReaderTPure a

-- reference creator monad
newtype RefCreatorT m a
    = RefCreatorT { unRefCreator :: GlobalVars m -> m a }

-- reference writer monad
newtype instance RefWriterOf_ (RefReaderT m) a
    = RefWriterT { runRefWriterT :: RefCreatorT m a }
        deriving (Monad, Applicative, Functor, MonadFix)

type RefWriterT m = RefWriterOf_ (RefReaderT m)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handler.
type Handler m = RegionStatusChangeHandler m

------------------------------

{-
conv :: (SimpleRefClass m, Functor f) => RefHandler m a -> (a -> f (a -> RefCreatorT m a)) -> RefReaderT m (f (RefWriterT m ()))
conv r f = RefReaderT $ RefCreatorT $ \st ->
        fmap (fmap (RefWriterT . RefCreatorT . const)) $ runRefHandler r (fmap (\g -> flip unRefCreator st . g) . f)
-}

newReadReference :: forall m a . SimpleRefClass m => GlobalVars m -> a -> (a -> m a) -> m (m a)
newReadReference st a0 ma = do

    writeSimpleRef (_dependencycoll st) mempty
    a1 <- ma a0
    ih <- readSimpleRef $ _dependencycoll st

    if Map.null ih
      then return $ pure a1
      else do
        i <- newId st
        oir <- newSimpleRef $ RefState a1 mempty

        regTrigger st (i, oir) ih ma

        return $ do
            RefState a' _ <- readSimpleRef oir
            dp <- readSimpleRef (_dependencycoll st)
            writeSimpleRef (_dependencycoll st) $ Map.insert i oir dp
            return $ unsafeCoerce a'


newReference :: forall m a . SimpleRefClass m => GlobalVars m -> a -> m (RefHandler m a)
newReference st a0 = do

    i <- newId st
    oir <- newSimpleRef $ RefState a0 mempty

    return $ RefHandler $ \ff -> do

        RefState a' nas <- readSimpleRef oir
        let aold = unsafeCoerce a'
        dp <- readSimpleRef (_dependencycoll st)
        writeSimpleRef (_dependencycoll st) $ Map.insert i oir dp

        return $ (,) (fst $ runRefFunctor $ ff aold) $ \init -> do
            let ma = snd . runRefFunctor . ff

            writeSimpleRef (_dependencycoll st) mempty
            a <- ma aold
            ih <- readSimpleRef $ _dependencycoll st

            when init $ do

                writeSimpleRef oir $ RefState a nas

                when (not $ Map.null nas) $ do

                    let ch :: TId m -> m [TId m]
                        ch (_, n) = do
                            TriggerState _ (_, w) dep _ _ <- readSimpleRef n
                            RefState _ revDep <- readSimpleRef w
                            flip filterM (Map.toList revDep) $ \(_, na) -> do
                                TriggerState alive (i, _) _ _ _ <- readSimpleRef na
                                pure $ alive && not (Map.member i dep)

                        collects p = mapM_ (collect p) =<< ch p

                        collect (i, op) v@(_, ov) = do
                            ts <- readSimpleRef ov
                            writeSimpleRef ov $ ts { _reverseDeps = Map.insert i op $ _reverseDeps ts }
                            when (Map.null $ _reverseDeps ts) $ collects v

                    as <- (`filterM` Map.toList nas) $ \(_, na) -> readSimpleRef na <&> _alive
                    mapM_ collects as

                    let topSort [] = pure ()
                        topSort (p@(i, op):ps) = do
                            readSimpleRef op >>= _updateFun

                            let del (_, n) = do
                                    ts <- readSimpleRef n
                                    let rd = Map.delete i $ _reverseDeps ts
                                    writeSimpleRef n $ ts { _reverseDeps = rd }
                                    return $ Map.null rd
                            ys <- filterM del =<< ch p
                            topSort $ mergeBy (\(i, _) (j, _) -> compare i j) ps ys

                    topSort as

                    p <- readSimpleRef (_postpone st)
                    writeSimpleRef (_postpone st) $ return ()
                    p

            when (not $ Map.null ih) $ regTrigger st (i, oir) ih ma


regTrigger :: forall m a . SimpleRefClass m => GlobalVars m -> Id m -> Ids m -> (a -> m a) -> m ()
regTrigger st (i, oir) ih ma = do

    j <- newId st
    ori <- newSimpleRef $ error "impossible"

    let addRev, delRev :: SimpleRefOf m (RefState m) -> m ()
        addRev x = modSimpleRef x $ revDep %= Map.insert j ori
        delRev x = modSimpleRef x $ revDep %= Map.delete j

        modReg = do

            RefState aold nas <- readSimpleRef oir

            writeSimpleRef (_dependencycoll st) mempty
            a <- ma $ unsafeCoerce aold
            ih <- readSimpleRef $ _dependencycoll st

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


joinRefHandler :: (SimpleRefClass m) => GlobalVars m -> RefReaderT m (RefHandler m a) -> RefHandler m a
joinRefHandler _ (RefReaderTPure r) = r
joinRefHandler st (RefReaderT (RefCreatorT m)) = RefHandler $ \f -> do
    ref <- m st
    readRef__ ref <&> \v -> (,) (fst $ runRefFunctor $ f v) $ \init -> do

        r <- newReadReference st (const $ pure ()) $ \kill -> do
            kill Kill
            ref <- m st
            noDependency st $ fmap fst $ getHandler st $ writeRef_ ref init $ snd . runRefFunctor . f

        tellHand st $ \msg -> r >>= ($ msg)


instance SimpleRefClass m => RefClass (RefHandler m) where
    type RefReaderSimple (RefHandler m) = RefReaderT m

    unitRef = pure $ RefHandler $ \x -> pure (fst $ runRefFunctor $ x (), const $ pure ())

--    {-# INLINE readRefSimple #-}
    readRefSimple = (>>= readRef_)

    writeRefSimple x a = RefWriterT $ runRefReaderT x >>= \r -> RefCreatorT $ \_st ->
        writeRef_ r True $ \_ -> pure a

    lensMap k (RefReaderTPure r) = pure $ lensMap_ r k
    lensMap k x = RefReaderT $ RefCreatorT $ \st -> pure $ joinRefHandler st $ x <&> \r -> lensMap_ r k

lensMap_ :: SimpleRefClass m => RefHandler m a -> Lens' a b -> RefHandler m b
lensMap_ (RefHandler r) k = RefHandler $ r . k


instance SimpleRefClass m => MonadRefCreator (RefCreatorT m) where
    {-# SPECIALIZE instance MonadRefCreator (RefCreatorT IO) #-}

    newRef a = RefCreatorT $ \st -> pure <$> newReference st a

    extendRef m k a0 = RefCreatorT $ \st -> do
        r <- newReference st a0
        -- TODO: remove getHandler?
        _ <- getHandler st $ do
            writeRef_ r True $ \a -> runRefReaderT' st $ readRefSimple m <&> \b -> set k b a
            writeRef_ (joinRefHandler st m) False $ \_ -> readRef__ r <&> (^. k)
        return $ pure r

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
        writeRef_ r True $ \it@(p, (h', _)) -> do
            a <- runRefReaderT' st m
            noDependency st $ if p a
              then return it
              else do
                h' Kill
                (h, b) <- getHandler st $ flip unRefCreator st $ f a
                return ((== a), (h, b))
        tellHand st $ \msg -> do
            (_, (h, _)) <- readRef__ r
            h msg

        return $ lensMap (_2 . _2) $ pure r

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

writeRef_ :: SimpleRefClass m => RefHandler m a -> Bool -> (a -> m a) -> m ()
writeRef_ r init k = runRefHandler r (\a -> RefFunctor ((), k a)) >>= ($ init) . snd

readRef__ :: SimpleRefClass m => RefHandler m a -> m a
readRef__ r = runRefHandler r (\a -> RefFunctor (a, error "impossible")) <&> fst

readRef_ :: SimpleRefClass m => RefHandler m a -> RefReaderT m a
readRef_ = RefReaderT . RefCreatorT . const . readRef__

runRefReaderT :: Monad m => RefReaderT m a -> RefCreatorT m a
runRefReaderT (RefReaderTPure a) = return a
runRefReaderT (RefReaderT x) = x

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

instance SimpleRefClass m => MonadRefReader (RefCreatorT m) where
    type BaseRef (RefCreatorT m) = RefHandler m
    liftRefReader = runRefReaderT

instance SimpleRefClass m => MonadRefReader (RefReaderT m) where
    type BaseRef (RefReaderT m) = RefHandler m
    liftRefReader (RefReaderTPure a) = RefReaderTPure a
    liftRefReader (RefReaderT (RefCreatorT m)) = RefReaderT $ RefCreatorT $ \st -> noDependency st $ m st
    readRef = readRefSimple

instance SimpleRefClass m => MonadRefReader (RefWriterOf_ (RefReaderT m)) where
    type BaseRef (RefWriterOf_ (RefReaderT m)) = RefHandler m
    liftRefReader = RefWriterT . runRefReaderT

instance SimpleRefClass m => MonadRefWriter (RefWriterOf_ (RefReaderT m)) where
    liftRefWriter = id

instance SimpleRefClass m => MonadMemo (RefCreatorT m) where
    memoRead = memoRead_ $ \r -> runRefWriterT . writeRefSimple r

instance SimpleRefClass m => MonadEffect (RefWriterOf_ (RefReaderT m)) where
    type EffectM (RefWriterOf_ (RefReaderT m)) = m
    liftEffectM = RefWriterT . RefCreatorT . const

instance SimpleRefClass m => MonadEffect (RefCreatorT m) where
    type EffectM (RefCreatorT m) = m
    liftEffectM = RefCreatorT . const

