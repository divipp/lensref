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
    ( RefReader
    , RefCreator
    , RefWriter
    , runRefCreator
    , liftRefWriter'
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
        :: forall f . Functor f
        => (a -> f (a -> m a)) -> m (f (Bool -> m ())) -- True: run the trigger initially also
    }
-- possible alternative: m (a, Bool -> m a -> m ())

-- | global variables
data GlobalVars m = GlobalVars
    { _handlercollection  :: !(SRef m (Handler m))  -- ^ collected handlers
    , _dependencycoll     :: !(SRef m (Ids m))      -- ^ collected dependencies
    , _postpone           :: !(SRef m (m ()))       -- ^ postponed actions
    , _counter            :: !(SRef m Int)          -- ^ increasing counter
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
type OrdRef    m a = (Int, SRef m a)
-- | IORefs with Ord instance
type OrdRefSet m a = Map.IntMap (SRef m a)


------------- data types for computations

-- reference reader monad
data RefReader m a
    = RefReader !(RefCreator m a)
    | RefReaderTPure a

-- reference creator monad
newtype RefCreator m a
    = RefCreator { unRefCreator :: GlobalVars m -> m a }

-- reference writer monad
newtype instance RefWriterOf_ (RefReader m) a
    = RefWriter { runRefWriterT :: RefCreator m a }
        deriving (Monad, Applicative, Functor, MonadFix)

type RefWriter m = RefWriterOf_ (RefReader m)

-- trigger handlers
-- The registered triggers may be killed, blocked and unblocked via the handler.
type Handler m = RegionStatusChangeHandler m

------------------------------

{-
conv :: (NewRef m, Functor f) => RefHandler m a -> (a -> f (a -> RefCreator m a)) -> RefReader m (f (RefWriter m ()))
conv r f = RefReader $ RefCreator $ \st ->
        fmap (fmap (RefWriter . RefCreator . const)) $ runRefHandler r (fmap (\g -> flip unRefCreator st . g) . f)
-}

newReadReference :: forall m a . NewRef m => GlobalVars m -> a -> (a -> m a) -> m (m a)
newReadReference st a0 ma = do

    writeRef' (_dependencycoll st) mempty
    a1 <- ma a0
    ih <- readRef' $ _dependencycoll st

    if Map.null ih
      then return $ pure a1
      else do
        i <- newId st
        oir <- newRef' $ RefState a1 mempty

        regTrigger st (i, oir) ih ma

        return $ do
            RefState a' _ <- readRef' oir
            dp <- readRef' (_dependencycoll st)
            writeRef' (_dependencycoll st) $ Map.insert i oir dp
            return $ unsafeCoerce a'


newReference :: forall m a . NewRef m => GlobalVars m -> a -> m (RefHandler m a)
newReference st a0 = do

    i <- newId st
    oir <- newRef' $ RefState a0 mempty

    return $ RefHandler $ \ff -> do

        RefState a' nas <- readRef' oir
        let aold = unsafeCoerce a'
        dp <- readRef' (_dependencycoll st)
        writeRef' (_dependencycoll st) $ Map.insert i oir dp

        return $ ff aold <&> \ma init -> do

            writeRef' (_dependencycoll st) mempty
            a <- ma aold
            ih <- readRef' $ _dependencycoll st

            when init $ do

                writeRef' oir $ RefState a nas

                when (not $ Map.null nas) $ do

                    let ch :: TId m -> m [TId m]
                        ch (_, n) = do
                            TriggerState _ (_, w) dep _ _ <- readRef' n
                            RefState _ revDep <- readRef' w
                            flip filterM (Map.toList revDep) $ \(_, na) -> do
                                TriggerState alive (i, _) _ _ _ <- readRef' na
                                pure $ alive && not (Map.member i dep)

                        collects p = mapM_ (collect p) =<< ch p

                        collect (i, op) v@(_, ov) = do
                            ts <- readRef' ov
                            writeRef' ov $ ts { _reverseDeps = Map.insert i op $ _reverseDeps ts }
                            when (Map.null $ _reverseDeps ts) $ collects v

                    as <- (`filterM` Map.toList nas) $ \(_, na) -> readRef' na <&> _alive
                    mapM_ collects as

                    let topSort [] = pure ()
                        topSort (p@(i, op):ps) = do
                            readRef' op >>= _updateFun

                            let del (_, n) = do
                                    ts <- readRef' n
                                    let rd = Map.delete i $ _reverseDeps ts
                                    writeRef' n $ ts { _reverseDeps = rd }
                                    return $ Map.null rd
                            ys <- filterM del =<< ch p
                            topSort $ mergeBy (\(i, _) (j, _) -> compare i j) ps ys

                    topSort as

                    p <- readRef' (_postpone st)
                    writeRef' (_postpone st) $ return ()
                    p

            when (not $ Map.null ih) $ regTrigger st (i, oir) ih ma


regTrigger :: forall m a . NewRef m => GlobalVars m -> Id m -> Ids m -> (a -> m a) -> m ()
regTrigger st (i, oir) ih ma = do

    j <- newId st
    ori <- newRef' $ error "impossible"

    let addRev, delRev :: SRef m (RefState m) -> m ()
        addRev x = modRef' x $ revDep %= Map.insert j ori
        delRev x = modRef' x $ revDep %= Map.delete j

        modReg = do

            RefState aold nas <- readRef' oir

            writeRef' (_dependencycoll st) mempty
            a <- ma $ unsafeCoerce aold
            ih <- readRef' $ _dependencycoll st

            writeRef' oir $ RefState a nas

            ts <- readRef' ori
            writeRef' ori $ ts { _dependencies = ih }
            let ih' = _dependencies ts

            mapM_ delRev $ Map.elems $ ih' `Map.difference` ih
            mapM_ addRev $ Map.elems $ ih `Map.difference` ih'

    writeRef' ori $ TriggerState True (i, oir) ih modReg mempty

    mapM_ addRev $ Map.elems ih

    tellHand st $ \msg -> do

        ts <- readRef' ori
        writeRef' ori $ ts { _alive = msg == Unblock }

        when (msg == Kill) $
            mapM_ delRev $ Map.elems $ _dependencies ts

        -- TODO
        when (msg == Unblock) $
            modRef' (_postpone st) $ modify (>> _updateFun ts)


joinRefHandler :: (NewRef m) => GlobalVars m -> RefReader m (RefHandler m a) -> RefHandler m a
joinRefHandler _ (RefReaderTPure r) = r
joinRefHandler st (RefReader (RefCreator m)) = RefHandler $ \a -> do
    ref <- m st
    readRef__ ref <&> \v -> a v <&> \reg init -> do

        r <- newReadReference st (const $ pure ()) $ \kill -> do
            kill Kill
            ref <- m st
            fmap fst $ getHandler st $ writeRef_ ref init reg

        tellHand st $ \msg -> r >>= ($ msg)


instance NewRef m => RefClass (RefHandler m) where
    type RefReaderSimple (RefHandler m) = RefReader m

    unitRef = pure $ RefHandler $ \x -> pure $ x () <&> \_ _ -> pure ()

--    {-# INLINE readRefSimple #-}
    readRefSimple = (>>= readRef_)

    writeRefSimple x a = RefWriter $ runRefReaderT x >>= \r -> RefCreator $ \_st ->
        writeRef_ r True $ \_ -> pure a

    lensMap k (RefReaderTPure r) = pure $ lensMap_ r k
    lensMap k x = RefReader $ RefCreator $ \st -> pure $ joinRefHandler st $ x <&> \r -> lensMap_ r k

lensMap_ :: NewRef m => RefHandler m a -> Lens' a b -> RefHandler m b
lensMap_ r k = lensMap__ r $ tr' k

lensMap__ :: NewRef m => RefHandler m a -> MLens' a b -> RefHandler m b
lensMap__ (RefHandler r) k = RefHandler $ r . k

--type MLens s t a b = forall k . Functor k => Lens s (s -> k t) a (a -> k b)
type MLens s t a b = forall f k . (Functor f, Functor k) => (a -> f (a -> k b)) -> s -> f (s -> k t)

type MLens' s a = MLens s s a a

tr' :: Lens s t a b -> MLens s t a b
tr' l f a = l <$> f (getConst $ l Const a)

{-
type Optic p f s t a b = p a (f b) -> p s (f t) 

type MLens s t a b = forall f k . (Functor f, Functor k) => Optic (P k) f s t a b

newtype P f a b = P { unP :: a -> f (a -> b) }

tr :: Lens s t a b -> MLens s t a b
tr l f = P $ \a -> l <$> unP f (getConst $ l Const a)
-}

instance NewRef m => MonadRefCreator (RefCreator m) where
    {-# SPECIALIZE instance MonadRefCreator (RefCreator IO) #-}

    newRef a = RefCreator $ \st -> pure <$> newReference st a

    extRef m k a0 = RefCreator $ \st -> do
        r <- newReference st a0
        -- TODO: remove getHandler?
        _ <- getHandler st $ do
            writeRef_ r True $ \a -> runRefReaderT' st $ readRefSimple m <&> \b -> set k b a
            writeRef_ (joinRefHandler st m) False $ \_ -> readRef__ r <&> (^. k)
        return $ pure r

    onChange (RefReaderTPure a) f = RefReaderTPure <$> f a
    onChange m f = RefCreator $ \st -> do
        r <- newReadReference st (const $ pure (), error "impossible #4") $ \(h, _) -> do
            h Kill
            runRefReaderT' st m >>= getHandler st . flip unRefCreator st . f
        return $ fmap snd $ RefReader $ RefCreator $ \_ -> r

    onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChangeEq m f = RefCreator $ \st -> do
        r <- newReadReference st (const False, (const $ pure (), error "impossible #3"))
          $ \it@(p, (h', _)) -> do
            a <- runRefReaderT' st m
            if p a
              then return it
              else do
                h' Kill
                (h, b) <- getHandler st $ flip unRefCreator st $ f a
                return ((== a), (h, b))

        return $ fmap (snd . snd) $ RefReader $ RefCreator $ \_ -> r

    onChangeEq_ m f = RefCreator $ \st -> do
        r <- newReference st (const False, (const $ pure (), error "impossible #3"))
        writeRef_ r True $ \it@(p, (h', _)) -> do
            a <- runRefReaderT' st m
            if p a
              then return it
              else do
                h' Kill
                (h, b) <- getHandler st $ flip unRefCreator st $ f a
                return ((== a), (h, b))

        return $ lensMap (_2 . _2) $ pure r

    onChangeMemo (RefReaderTPure a) f = fmap RefReaderTPure $ join $ f a
    onChangeMemo (RefReader mr) f = RefCreator $ \st -> do
        r <- newReference st ((const False, ((error "impossible #2", const $ pure (), const $ pure ()) , error "impossible #1")), [])
        writeRef_ r True $ \st'@((p, ((m'',h1'',h2''), _)), memo) -> do
            let it = (p, (m'', h1''))
            a <- flip unRefCreator st mr
            if p a
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
        return $ readRef_ r <&> snd . snd . fst

    onRegionStatusChange h
        = RefCreator $ \st -> tellHand st h

runRefCreator :: NewRef m => ((forall b . RefWriter m b -> m b) -> RefCreator m a) -> m a
runRefCreator f = do
    s <- GlobalVars
            <$> newRef' (const $ pure ())
            <*> newRef' mempty
            <*> newRef' (return ())
            <*> newRef' 0
    flip unRefCreator s $ f $ flip unRefCreator s . runRefWriterT

-------------------- aux

writeRef_ :: NewRef m => RefHandler m a -> Bool -> (a -> m a) -> m ()
writeRef_ r init k = runRefHandler r (\_ -> Identity k) >>= ($ init) . runIdentity

readRef__ :: NewRef m => RefHandler m a -> m a
readRef__ r = runRefHandler r Const <&> getConst

readRef_ :: NewRef m => RefHandler m a -> RefReader m a
readRef_ = RefReader . RefCreator . const . readRef__

runRefReaderT :: Monad m => RefReader m a -> RefCreator m a
runRefReaderT (RefReaderTPure a) = return a
runRefReaderT (RefReader x) = x

runRefReaderT' st = flip unRefCreator st . runRefReaderT

liftRefWriter' :: RefWriterOf_ (RefReader m) a -> RefCreator m a
liftRefWriter' = runRefWriterT

--tellHand :: (NewRef m) => Handler m -> m ()
tellHand st h = modRef' (_handlercollection st) $ modify $ \f msg -> f msg >> h msg

--getHandler :: NewRef m => RefCreator m a -> RefCreator m (Handler m, a)
getHandler st m = do
    let r = _handlercollection st
    h' <- readRef' r
    writeRef' r $ const $ pure ()
    a <- m
    h <- readRef' r
    writeRef' r h'
    return (h, a)

newId :: NewRef m => GlobalVars m -> m Int
newId (GlobalVars _ _ _ st) = do
    c <- readRef' st
    writeRef' st $ succ c
    return c

revDep :: Lens' (RefState m) (TIds m)
revDep k (RefState a b) = k b <&> \b' -> RefState a b'

------------------------------------------------------- type class instances

instance Monad m => Monoid (RefCreator m ()) where
    mempty = return ()
    m `mappend` n = m >> n

instance Monad m => Monad (RefCreator m) where
    return = RefCreator . const . return
    RefCreator m >>= f = RefCreator $ \r -> m r >>= \a -> unRefCreator (f a) r

instance Applicative m => Applicative (RefCreator m) where
    pure = RefCreator . const . pure
    RefCreator f <*> RefCreator g = RefCreator $ \r -> f r <*> g r

instance Functor m => Functor (RefCreator m) where
    fmap f (RefCreator m) = RefCreator $ fmap f . m

instance MonadFix m => MonadFix (RefCreator m) where
    mfix f = RefCreator $ \r -> mfix $ \a -> unRefCreator (f a) r

instance Functor m => Functor (RefReader m) where
    fmap f (RefReaderTPure x) = RefReaderTPure $ f x
    fmap f (RefReader m) = RefReader $ fmap f m

instance Applicative m => Applicative (RefReader m) where
    pure = RefReaderTPure
    RefReaderTPure f <*> RefReaderTPure a = RefReaderTPure $ f a
    mf <*> ma = RefReader $ runRefReaderT mf <*> runRefReaderT ma
      where
        runRefReaderT (RefReaderTPure a) = pure a
        runRefReaderT (RefReader x) = x

instance Monad m => Monad (RefReader m) where
    return = RefReaderTPure
    RefReaderTPure r >>= f = f r
    RefReader mr >>= f = RefReader $ mr >>= runRefReaderT . f

instance NewRef m => MonadRefReader (RefCreator m) where
    type BaseRef (RefCreator m) = RefHandler m
    liftRefReader = runRefReaderT

instance NewRef m => MonadRefReader (RefReader m) where
    type BaseRef (RefReader m) = RefHandler m
    liftRefReader = RefReader . protect . runRefReaderT
      where
        protect (RefCreator m)
            = RefCreator $ \st -> do
                ih <- readRef' $ _dependencycoll st
                a <- m st
                writeRef' (_dependencycoll st) ih
                return a
    readRef = readRefSimple

instance NewRef m => MonadRefReader (RefWriterOf_ (RefReader m)) where
    type BaseRef (RefWriterOf_ (RefReader m)) = RefHandler m
    liftRefReader = RefWriter . runRefReaderT

instance NewRef m => MonadRefWriter (RefWriterOf_ (RefReader m)) where
    liftRefWriter = id

instance NewRef m => MonadMemo (RefCreator m) where
    memoRead = memoRead_ $ \r -> runRefWriterT . writeRefSimple r

instance NewRef m => MonadEffect (RefWriterOf_ (RefReader m)) where
    type EffectM (RefWriterOf_ (RefReader m)) = m
    liftEffectM = RefWriter . RefCreator . const

instance NewRef m => MonadEffect (RefCreator m) where
    type EffectM (RefCreator m) = m
    liftEffectM = RefCreator . const

