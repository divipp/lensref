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
        -> TIds m   -- reverse dependency
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
    = RefCreator { unRegister :: GlobalVars m -> m a }

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
        fmap (fmap (RefWriter . RefCreator . const)) $ runRefHandler r (fmap (\g -> flip unRegister st . g) . f)
-}

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

                modRef' oir $ modify $ \(RefState _ s) -> RefState a s

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
                            notvisited <- modRef' ov $ do
                                reverseDeps %= Map.insert i op
                                use $ reverseDeps . to Map.null
                            when notvisited $ collects v

                    as <- (`filterM` Map.toList nas) $ \(_, na) -> readRef' na <&> (^. alive)
                    mapM_ collects as

                    let topSort [] = pure ()
                        topSort (p@(i, op):ps) = do
                            readRef' op >>= _updateFun

                            let del (_, n) = modRef' n $ do
                                    reverseDeps %= Map.delete i
                                    use $ reverseDeps . to Map.null
                            ys <- filterM del =<< ch p
                            topSort $ mergeBy (\(i, _) (j, _) -> compare i j) ps ys

                    topSort as

                    p <- readRef' (_postpone st)
                    writeRef' (_postpone st) $ return ()
                    p

            when (not $ Map.null ih) $ do

                j <- newId st
                ori <- newRef' $ error "impossible"

                let addRev, delRev :: SRef m (RefState m) -> m ()
                    addRev x = modRef' x $ revDep %= Map.insert j ori
                    delRev x = modRef' x $ revDep %= Map.delete j

                    modReg = do

                        aold <- readRef' oir <&> unsafeGet

                        writeRef' (_dependencycoll st) mempty
                        a <- ma aold
                        ih <- readRef' $ _dependencycoll st

                        ih' <- readRef' ori <&> (^. dependencies)
                        mapM_ delRev $ Map.elems $ ih' `Map.difference` ih
                        mapM_ addRev $ Map.elems $ ih `Map.difference` ih'

                        modRef' oir $ modify $ \(RefState _ s) -> RefState a s
                        modRef' ori $ dependencies .= ih

                writeRef' ori $ TriggerState True (i, oir) ih modReg mempty

                mapM_ addRev $ Map.elems ih

                flip unRegister st $ tellHand $ \msg -> do

                    modRef' ori $ alive .= (msg == Unblock)

                    when (msg == Kill) $ do
                        ih' <- readRef' ori
                        mapM_ delRev $ Map.elems $ ih' ^. dependencies

                    -- TODO
                    when (msg == Unblock) $ do
                        TriggerState _ _ _ x _ <- readRef' ori
                        modRef' (_postpone st) $ modify (>> x)


joinRefHandler :: (NewRef m) => GlobalVars m -> RefReader m (RefHandler m a) -> RefHandler m a
joinRefHandler _ (RefReaderTPure r) = r
joinRefHandler st (RefReader m) = RefHandler $ \a -> do
    ref <- flip unRegister st m
    runRefHandler ref (Const . a) <&> \fm -> getConst fm <&> \reg init -> do

        -- TODO: don't do this on simple write
        r <- newReference st $ const $ pure ()

        flip (registerTrigger r) True $ \kill -> flip unRegister st $ do
            runM kill Kill
            ref <- m
            fmap fst $ getHandler $ RefCreator $ \_st -> registerTrigger ref reg init

        flip unRegister st $ tellHand $ \msg -> do
            h <- flip unRegister st $ runRefReaderT $ readRef_ r
            flip unRegister st $ runM h msg


registerTrigger :: NewRef m => RefHandler m a -> (a -> m a) -> Bool -> m ()
registerTrigger r k init = runRefHandler r (\_ -> Identity k) >>= ($ init) . runIdentity

instance NewRef m => RefClass (RefHandler m) where
    type RefReaderSimple (RefHandler m) = RefReader m

    unitRef = pure $ RefHandler $ \x -> pure $ x () <&> \_ _ -> pure ()

    {-# INLINE readRefSimple #-}
    readRefSimple x = x >>= \r -> RefReader $ RefCreator $ \_st -> runRefHandler r Const <&> getConst

    writeRefSimple x a = RefWriter $ runRefReaderT x >>= \r -> RefCreator $ \_st ->
        runRefHandler r (const $ Identity $ const $ pure a) >>= ($ True) . runIdentity

    lensMap k (RefReaderTPure r) = pure $ lensMap_ r k
    lensMap k x = RefReader $ RefCreator $ \st -> pure $ joinRefHandler st $ x <&> \r -> lensMap_ r k

lensMap_ :: NewRef m => RefHandler m a -> Lens' a b -> RefHandler m b
lensMap_ r k = lensMap__ r $ tr' k

lensMap__ :: NewRef m => RefHandler m a -> MLens' a b -> RefHandler m b
lensMap__ (RefHandler r) k = RefHandler $ r . k

type MLens s t a b = forall k . Functor k => Lens s (s -> k t) a (a -> k b)
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

    extRef m k a0 = do
        r <- RefCreator $ \st -> newReference st a0
        -- TODO: remove dropHandler?
        dropHandler $ RefCreator $ \st -> do
            flip (registerTrigger r) True $ \a -> flip unRegister st $ runRefReaderT $ readRefSimple m <&> \b -> set k b a
            flip (registerTrigger $ joinRefHandler st m) False $ \_ -> flip unRegister st $ runRefReaderT $ readRef_ r <&> (^. k)
        return $ pure r

    onChange (RefReaderTPure a) f = RefReaderTPure <$> f a
    onChange m f = RefCreator $ \st -> do
        r <- newReference st (const $ pure (), error "impossible #4")
        flip (registerTrigger r) True $ \(h, _) -> flip unRegister st $ do
            runM h Kill
            runRefReaderT m >>= getHandler . f
        return $ fmap snd $ readRef $ pure r

    onChangeEq (RefReaderTPure a) f = fmap RefReaderTPure $ f a
    onChangeEq r f = fmap readRef $ onChangeEq_ r f

    onChangeEq_ m f = RefCreator $ \st -> do
        r <- newReference st (const False, (const $ pure (), error "impossible #3"))
        flip (registerTrigger r) True $ \it@(p, (h', _)) -> flip unRegister st $ do
            a <- runRefReaderT m
            if p a
              then return it
              else do
                runM h' Kill
                (h, b) <- getHandler $ f a
                return ((== a), (h, b))

        return $ lensMap (_2 . _2) $ pure r

    onChangeMemo (RefReaderTPure a) f = fmap RefReaderTPure $ join $ f a
    onChangeMemo (RefReader mr) f = RefCreator $ \st -> do
        r <- newReference st ((const False, ((error "impossible #2", const $ pure (), const $ pure ()) , error "impossible #1")), [])
        flip (registerTrigger r) True $ \st'@((p, ((m'',h1'',h2''), _)), memo) -> flip unRegister st $ do
            let it = (p, (m'', h1''))
            a <- mr
            if p a
              then return st'
              else case listToMaybe [ b | (p, b) <- memo, p a] of
                Just (m',h1') -> do
                    runM h2'' Kill
                    runM h1'' Block
                    runM h1' Unblock
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1',h2), b')), it: filter (not . ($ a) . fst) memo)
                Nothing -> do
                    runM h2'' Kill
                    (h1, m') <- getHandler $ f a
                    (h2, b') <- getHandler m'
                    return (((== a), ((m',h1,h2), b')), it: memo)
        return $ readRef_ r <&> snd . snd . fst

    onRegionStatusChange h
        = tellHand h

runRefCreator :: NewRef m => ((RefWriter m () -> m ()) -> RefCreator m a) -> m a
runRefCreator f = do
    s <- GlobalVars
            <$> newRef' (const $ pure ())
            <*> newRef' mempty
            <*> newRef' (return ())
            <*> newRef' 0
    flip unRegister s $ f $ flip unRegister s . runRefWriterT

-------------------- aux

readRef_ :: NewRef m => RefHandler m a -> RefReader m a
readRef_ r = RefReader $ RefCreator $ \_st -> runRefHandler r Const <&> getConst

runRefReaderT :: Monad m => RefReader m a -> RefCreator m a
runRefReaderT (RefReaderTPure a) = return a
runRefReaderT (RefReader x) = x

runM m k = RefCreator . const $ m k

liftRefWriter' :: RefWriterOf_ (RefReader m) a -> RefCreator m a
liftRefWriter' = runRefWriterT

tellHand :: (NewRef m) => Handler m -> RefCreator m ()
tellHand h = RefCreator $ \st -> modRef' (_handlercollection st) $ modify $ \f msg -> f msg >> h msg

dropHandler :: NewRef m => RefCreator m a -> RefCreator m a
dropHandler m = RefCreator $ \st -> do
    x <- readRef' $ _handlercollection st
    a <- unRegister m st
    writeRef' (_handlercollection st) x
    return a

getHandler :: NewRef m => RefCreator m a -> RefCreator m (Handler m, a)
getHandler m = RefCreator $ \st -> do
    let r = _handlercollection st
    h' <- readRef' r
    writeRef' r $ const $ pure ()
    a <- unRegister m st
    h <- readRef' r
    writeRef' r h'
    return (h, a)

unsafeGet :: RefState m -> a
unsafeGet (RefState a _) = unsafeCoerce a

newId :: NewRef m => GlobalVars m -> m Int
newId (GlobalVars _ _ _ st) = do
    c <- readRef' st
    writeRef' st $ succ c
    return c

-------------- lenses

dependencies :: Lens' (TriggerState m) (Ids m)
dependencies k (TriggerState a b c d e) = k c <&> \c' -> TriggerState a b c' d e

alive :: Lens' (TriggerState m) Bool
alive k (TriggerState a b c d e) = k a <&> \a' -> TriggerState a' b c d e

reverseDeps :: Lens' (TriggerState m) (TIds m)
reverseDeps k (TriggerState a b c d e) = k e <&> \e' -> TriggerState a b c d e'

revDep :: Lens' (RefState m) (TIds m)
revDep k (RefState a b) = k b <&> \b' -> RefState a b'

------------------------------------------------------- type class instances

instance Monad m => Monoid (RefCreator m ()) where
    mempty = return ()
    m `mappend` n = m >> n

instance Monad m => Monad (RefCreator m) where
    return = RefCreator . const . return
    RefCreator m >>= f = RefCreator $ \r -> m r >>= \a -> unRegister (f a) r

instance Applicative m => Applicative (RefCreator m) where
    pure = RefCreator . const . pure
    RefCreator f <*> RefCreator g = RefCreator $ \r -> f r <*> g r

instance Functor m => Functor (RefCreator m) where
    fmap f (RefCreator m) = RefCreator $ fmap f . m

instance MonadFix m => MonadFix (RefCreator m) where
    mfix f = RefCreator $ \r -> mfix $ \a -> unRegister (f a) r

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
    liftRefReader m = RefReader $ protect' $ runRefReaderT m
      where
        protect' (RefCreator m)
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

