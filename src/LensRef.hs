{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE LambdaCase #-}
--{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
--{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}  -- not really needed
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module LensRef
    ( -- * Reference context
      Monad'
    , MonadTrace (..), TraceT, runTraceT
    , Reversible (..), ReversibleT, postponed, reversible, neut, runRev
    , SimpleRefs (..), modSimpleRef, memoRead
    , RefContext

    -- * References
    , Ref
    , unitRef
    , joinRef
    , lensMap

    -- * RefReader
    , RefReader
    , readRef

    -- * RefCreator
    , RefCreator
    , readerToCreator
    , runRefCreator
    , extendRef,            newRef
    , stabilize_,           stabilize
    , delayPrev,            delay_          -- uses previous
    , generator_,           onChange', joinCreator, generator', onChangeMemo'

    -- * RefWriter
    , RefWriter
    , creatorToWriter,      readerToWriter
    , writeRef,             modRef
    ) where

import Data.Monoid
--import Data.Function
import Data.Maybe
import Data.String
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
--import Control.Monad.Identity
import Control.Monad.Except
import Lens.Family2
import Lens.Family2.State
import Lens.Family2.Stock

import Unsafe.Coerce

import Utils

infixr 8 `lensMap`

-------------------------------------------------------------------------------- timed values

data Value a
    = Value Time{-known present-} a{-past value-} (Maybe a){-present value; Nothing: past value propagated-}

createValue :: Time -> a -> Value a
createValue t v = Value t (error $ "undefined past value created at " ++ show t) $ Just v

getValue :: MonadError String m => Time -> Value a -> m (a, Time, Value a)
getValue time v@(Value t v1 v2)
    | time == prevTime t = return (v1, prevTime t, v)
    | time == t          = return (v2', maybe (prevTime t) (const t) v2, v)
    | time >  t          = return (v2', prevTime time, Value time v2' Nothing)      -- automatic value propagation
    | otherwise = throwError $ "undefined past value read at " ++ show time ++ "; minimum was " ++ show (prevTime t)
  where
    v2' = fromMaybe v1 v2

setValue :: MonadError String m => Time -> a -> Value a -> m (Value a)
setValue time v3 (Value t v1 v2)
    | time > t  = return $ Value time (fromMaybe v1 v2) $ Just v3      -- automatic value propagation
    | otherwise = throwError $ "past value set at " ++ show time ++ "; minimum was " ++ show (nextTime t)

-------------------------------------------------------------------------------- RefReader --> Signal

-- TODO: rename to Signal?
newtype RefReader m a = RefReader { runRefReader_ :: ReaderT Bool (WriterT (Time, Set.Set PathId) (Backtrack m)) a }
    deriving (Functor, Applicative, Monad)

instance (IsString str, Monad' s) => IsString (RefReader s str) where
    fromString      = pure . fromString

instance (Monad' s, Num a) => Num (RefReader s a) where
    (+)             = liftA2 (+)
    (*)             = liftA2 (*)
    negate          = fmap negate
    abs             = fmap abs
    signum          = fmap signum
    fromInteger     = pure . fromInteger

instance (Monad' s, Fractional a) => Fractional (RefReader s a) where
    recip           = fmap recip
    fromRational    = pure . fromRational

instance (Monad' s, Floating a) => Floating (RefReader s a) where
    pi      = pure pi
    exp     = fmap exp
    sqrt    = fmap sqrt
    log     = fmap log
    (**)    = liftA2 (**)
    logBase = liftA2 logBase
    sin     = fmap sin
    tan     = fmap tan
    cos     = fmap cos
    asin    = fmap asin
    atan    = fmap atan
    acos    = fmap acos
    sinh    = fmap sinh
    tanh    = fmap tanh
    cosh    = fmap cosh
    asinh   = fmap asinh
    atanh   = fmap atanh
    acosh   = fmap acosh

-----------

runRefReader :: Monad' m => RefReader m a -> Backtrack m (a, Time)
runRefReader (RefReader m) = (id *** fst) <$> runWriterT (flip runReaderT True{- TODO!!!-} m)

simpleRead :: Monad' m => RefReader m a -> Backtrack m a
simpleRead = fmap fst . runRefReader

readRef :: Monad' m => Ref m a -> RefReader m a
readRef (Ref (r, _)) = r

whenChanged :: (Monad' m, Monoid b) => Bool -> RefReader m a -> (a -> Backtrack m b) -> Backtrack m b
whenChanged check r m = do
    present <- lift $ getTime
    (a, t) <- runRefReader r
    when' (not check || t == present) $ m a

-- TODO: make safer (make idempotent)
previous :: Monad' m => RefReader m a -> RefReader m a
previous m = RefReader $ ReaderT $ \r -> mapWriterT (mapExceptT inPast) $ flip runReaderT r $ runRefReader_ m
  where
    inPast :: Monad m => RefCreator m b -> RefCreator m b
    inPast (RefCreator m) = RefCreator $ local (prevTime *** id) m

previousValue :: Monad' m => RefReader m a -> Backtrack m a
previousValue = simpleRead . previous

-------------------------------------------------------------------------------- Ref

-- TODO: change to Laarhoven style (inside a newtype wrapper)?
newtype Ref m a = Ref (RefReader m a, a -> Backtrack m ())

unitRef :: Monad' m => Ref m ()
unitRef = Ref (return (), \() -> return ())

lensMap :: Monad' m => Lens' a b -> Ref m a -> Ref m b
lensMap k (Ref (g, s)) = Ref ((^. k) <$> g, (previousValue g >>=) . (s .) . (k .~))

joinRef :: Monad' m => RefReader m (Ref m a) -> Ref m a
joinRef rr = Ref (join $ readRef <$> rr, (simpleRead rr >>=) . (. writeRefSafe) . flip ($))

writeRefSafe :: Ref m a -> a -> Backtrack m ()
writeRefSafe (Ref (_, w)) = w

writeRefSafe' r v = writeRefSafe r v >> return (Just ())

-------------------------------------------------------------------------------- RefCreator

newtype RefCreator m a = RefCreator { runRefCreator'' :: StateT (TriggerList m) (ReaderT (Time, Context_ m) m) a }
    deriving (Functor, Applicative, Monad, MonadFix)

deriving instance MonadWriter w m => MonadWriter w (RefCreator m)
--deriving instance MonadReader r m => MonadReader r (RefCreator m)
--deriving instance MonadState s m => MonadState s (RefCreator m)

instance MonadTrans RefCreator where
    lift = RefCreator . lift . lift

instance MonadTrace m => MonadTrace (RefCreator m) where
    traceM = RefCreator . traceM

instance Reversible m => Reversible (RefCreator m) where
    restore m = RefCreator $ restore $ runRefCreator'' m <&> (runRefCreator'' +++ id)

instance SimpleRefs m => SimpleRefs (RefCreator m) where
    type SimpleRef (RefCreator m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

type Backtrack m = Exc (RefCreator m)

getTime :: Monad m => RefCreator m Time
getTime = RefCreator $ asks fst

createVal :: Monad m => a -> RefCreator m (Value a)
createVal x = liftM (flip createValue x) getTime

-- may fail
readerToCreator :: Monad' m => RefReader m a -> RefCreator m a
readerToCreator = assert "rToC" . simpleRead

runRefCreator :: forall a m . SimpleRefs m => ((forall b . RefWriter m b -> m b) -> RefCreator m a) -> m a
runRefCreator f = do
    st <- newSimpleRef (nextTime mempty, mempty)

    let g :: forall b . RefWriter m b -> m b
        g x = modSimpleRef st $ \s -> do
            (y, s') <- flip runReaderT inMain $ flip runStateT s $ runRefWriter x
            return (s', y)

    modSimpleRef st $ \(t, trs) -> do
        (x, trs') <- flip runReaderT (t, inMain) $ flip runStateT trs $ runRefCreator'' $ f g
        return ((t, trs'), x)

-------------------------------------------------------------------------------- RefWriter

newtype RefWriter m a = RefWriter { runRefWriter :: StateT (Time, TriggerList m) (ReaderT (Context_ m) m) a }
    deriving (Functor, Applicative, Monad, MonadFix)

deriving instance MonadWriter w m => MonadWriter w (RefWriter m)

instance MonadTrans RefWriter where
    lift = RefWriter . lift . lift

instance MonadTrace m => MonadTrace (RefWriter m) where
    traceM = RefWriter . traceM

instance SimpleRefs m => SimpleRefs (RefWriter m) where
    type SimpleRef (RefWriter m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

creatorToWriter :: Monad' m => RefCreator m a -> RefWriter m a
creatorToWriter = RefWriter . (\f -> StateT $ \(time, st) -> ReaderT $ \i -> fmap (id *** (,) time) $ flip runReaderT (time, i) $ runStateT f st) . runRefCreator''

writeRef :: forall m a . (Reversible m, MonadTrace m, MonadFix m) => Ref m a -> a -> RefWriter m ()
writeRef r x = do
    traceM "  write"
    RefWriter $ _1 %= nextTime
    creatorToWriter $ do
        assert "impossible" $ writeRefSafe r x
        assert "can't schedule network" $ runTriggers 1
  where
    runTriggers :: Int -> Backtrack m ()
    runTriggers k = do
        present <- lift $ getTime
        trs <- activeTriggers
        void $ foldr (orElse $ show k) (return Nothing) $ trs <&> \t -> do
            lift $ RefCreator $ tpTime t .= present
            traceM $ "    run " ++ show t
            runTrigger t >>= \case
                Nothing -> return Nothing
                Just () -> runTriggers (k + 1) >> return (Just ())

-- | derived
readerToWriter :: Monad' m => RefReader m a -> RefWriter m a
readerToWriter = creatorToWriter . readerToCreator

-- | derived
modRef :: (Reversible m, MonadTrace m, MonadFix m) => Ref m a -> (a -> a) -> RefWriter m ()
r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f


-------------------------------------------------------------------------------- Context

data Context_ m = Context_
    { cName :: String   -- TODO: make it more efficient?
    , _contextTriggers :: Lens' (TriggerList m) (TriggerList m)
    }

instance Show (Context_ m) where show = cName

inMain :: Context_ m
inMain = Context_ "I" id

inContext :: (MonadTrace m, IsTrigger t) => String -> Lens' (t m) (TriggerList m) -> TPath t m -> RefCreator m b -> RefCreator m b
inContext sh k tp (RefCreator m) = do
    let i = Context_ (show tp ++ sh) (tpSnd tp . k)
    traceM $ "    context " ++ show i
    b <- RefCreator $ local (id *** const i) m
    traceM $ "    end contex " ++ show i
    return b

-------------------------------------------------------------------------------- triggers

class IsTrigger t where
    type Val t :: *
    val :: Lens' (t m) (Value (Val t))
    collectChildren :: t m -> [Trigger_ m]
    runTrigger_ :: (MonadTrace m, MonadFix m) => (forall b . RefReader m b -> (b -> Backtrack m (Maybe ())) -> e) -> (e -> e -> e) -> TPath t m -> t m -> e

runTrigger :: (Reversible m, MonadTrace m, MonadFix m) => Trigger_ m -> Backtrack m (Maybe ())
runTrigger (Trg _ i tr) = runTrigger_ (whenChanged True) (orElse $ show i) i tr

-- TODO: make it more efficient
type PathId = String

data TPath t m = TPath
    { tpFst :: PathId
    , _tpSnd1 :: Lens' (TriggerList m) (Trigger_ m)
    , _tpSnd2 :: Lens' (Trigger_ m) (t m)
    }

instance Show (TPath t m) where show = tpFst

tpSnd :: TPath t m -> Lens' (TriggerList m) (t m)
tpSnd (TPath _ i j) = i . j

data Trigger_ m = forall t . IsTrigger t => Trg Time (TPath t m) (t m)      -- Time: mikor futtattuk utoljára

type TriggerList m = Seq (Trigger_ m)

tpTime :: Trigger_ m -> Lens' (TriggerList m) Time 
tpTime (Trg _ ~(TPath _ i _) _) = i . (\tr (Trg ti p x) -> tr ti <&> \ti -> Trg ti p x)

instance Show (Trigger_ m) where show (Trg _ p _) = show p

{-
filterTriggers :: Reversible m => [(Path, Trigger_ m)] -> Backtrack m [(Path, Trigger_ m)]
filterTriggers trs = return trs -- do
    take' . map snd . filter (fst) <$> mapM f trs
  where
    take' [] = trs
    take' x = take 1 x

    f (i, tr) = do
        present <- getTime
        (x, (t, ids)) <- runWriterT $ flip runReaderT False $ runRefReader_ $ runTrigger' i tr
        let active = t == present
        return (active, (i, tr))
-}

{-
       infó gyűjtés minden triggerről:
          (mit olvasna először ha most következne, mit olvasott, {- mire volt érzékeny -})  ->  mit ír

  =>   topologikus rendezés 'mit olvasott' szerint
  =>   kiválasztani a forrás nélkülieket
  =>   kiválasztani a forrás nélkülieket 'mit olvasna' alapján
  =>   kiválasztani a legkisebbet
  =>   végrehajtani
  =>   újra elölről
-}

activeTriggers :: Monad' m => Backtrack m [Trigger_ m]
activeTriggers = do
    present <- lift $ getTime

    let g :: [Time] -> Trigger_ m -> [([Time], Trigger_ m)]
        g ts x@(Trg t _ tr) = (t', x): concatMap (g t') (collectChildren tr)
          where
            t' = t: ts

        ok _ts@(t:_) = t < present -- && all (zipWith () ts $ tail ts)
        ok _ = error "impossible"

    trs <- lift $ RefCreator get
    return $ map snd $ filter (ok . fst) $ concatMap (g []) $ toList' trs

addTrigger' :: forall m t x . (MonadTrace m, MonadFix m, IsTrigger t)
    => (x -> t m) -> (TPath t m -> RefCreator m x) -> RefCreator m (Ref m (Val t))
addTrigger' mk ft = do
    Context_ rn r <- RefCreator $ asks snd
    i <- RefCreator $ length' <$> use r
    let p = TPath (rn ++ "_" ++ show i) (r . at' i) trg_
    present <- getTime
    traceM $ "    create " ++ show p
    void $ mfix $ \ta -> do
        RefCreator $ r %= (`snoc'` Trg present p (mk ta))
        ft p
    return $ refOf p
  where
    trg_ :: Lens' (Trigger_ m) (t m)
    trg_ tr (Trg time p t) = tr (unsafeCoerce t) <&> \t -> Trg time (unsafeCoerce p) t

addTrigger'' :: forall m t . (MonadTrace m, IsTrigger t)
    => t m -> RefCreator m (Ref m (Val t))
addTrigger'' mk = do
    Context_ rn r <- RefCreator $ asks snd
    i <- RefCreator $ length' <$> use r
    let p = TPath (rn ++ "_" ++ show i) (r . at' i) trg_
    present <- getTime
    traceM $ "    create " ++ show p
    RefCreator $ r %= (`snoc'` Trg present p mk)
    return $ refOf p
  where
    trg_ :: Lens' (Trigger_ m) (t m)
    trg_ tr (Trg time p t) = tr (unsafeCoerce t) <&> \t -> Trg time (unsafeCoerce p) t


refOf :: (MonadTrace m, IsTrigger t) => TPath t m -> Ref m (Val t)
refOf i = Ref (get', set') where

    get' = RefReader $ ReaderT $ \_setTime -> (mapWriterT $ fmap (fmap $ flip (,) $ Set.singleton $ tpFst i) . mapExceptT RefCreator) $
                (mapWriterT . mapExceptT . zoom) (tpSnd i . val) $ do
        time <- asks fst
        v <- get
        (val, creation, v') <- getValue time v
        put v'      -- TODO: use setTime
        tell creation
        return val

    set' a = do
        traceM $ "     wr " ++ show i
        mapExceptT RefCreator $ (mapExceptT . zoom) (tpSnd i . val) $ do
            time <- asks fst
            v <- get
            put =<< setValue time a v

-------------------------------------------------------------------------------- concrete triggers
--------------------------------------------------------------------------------

data ExtendRef b a m = ExtendRef
    { _erValue      :: Value a
    , _erRef        :: Ref m b
    , _erLens       :: Lens' a b
    }

instance IsTrigger (ExtendRef b a) where
    type Val (ExtendRef b a) = a
    val tr ~ExtendRef{..} = tr _erValue <&> \_erValue -> ExtendRef{..}
    collectChildren _ = mempty
    runTrigger_ whenChanged orElse i ~ExtendRef{..} =
            do whenChanged (readRef $ refOf i) $ writeRefSafe' _erRef . (^. _erLens)
        `orElse`
            do whenChanged (readRef _erRef) $ \b -> writeRefSafe' (refOf i) . (_erLens .~ b) =<< previousValue (readRef $ refOf i)

extendRef :: (MonadTrace m, MonadFix m) => Ref m b -> Lens' a b -> a -> RefCreator m (Ref m a)
extendRef _erRef _erLens a = do
    _erValue <- createVal . flip (set _erLens) a =<< readerToCreator (readRef _erRef)
    addTrigger'' ExtendRef{..}

---------- derived

newRef :: (MonadTrace m, MonadFix m) => a -> RefCreator m (Ref m a)
newRef = extendRef unitRef (\tr a -> tr () <&> \() -> a)


--------------------------------------------------------------------------------

data Stabilize a m = Stabilize
    { _sValue       :: Value a
    , _sRefR        :: RefReader m a
    , _ocEq         :: a -> a -> Bool
    }

instance IsTrigger (Stabilize a) where
    type Val (Stabilize a) = a
    val tr ~Stabilize{..} = tr _sValue <&> \_sValue -> Stabilize{..}
    collectChildren _ = mempty
    runTrigger_ whenChanged _ i ~Stabilize{..} = whenChanged _sRefR $ \a -> do
        old <- previousValue $ readRef $ refOf i
        when' (not $ _ocEq a old) $ writeRefSafe' (refOf i) a

stabilize_ :: (MonadTrace m, MonadFix m) => (a -> a -> Bool) -> a -> RefReader m a -> RefCreator m (Ref m a)
stabilize_ _ocEq a _sRefR = do
    _sValue <- createVal a
    addTrigger'' Stabilize{..}

-- | derived, but uses internal function 'previous'
delayPrev :: (MonadTrace m, MonadFix m) => a -> RefReader m (b -> a) -> RefReader m b -> RefCreator m (RefReader m a)
delayPrev a f r = readRef <$> stabilize_ (\_ _ -> False) a (f <*> previous r)

---------- derived

stabilize :: (MonadTrace m, MonadFix m, Eq a) => RefReader m a -> RefCreator m (RefReader m a)
stabilize r = readerToCreator r >>= \a -> readRef <$> stabilize_ (==) a r

delay_ :: (MonadTrace m, MonadFix m) => a -> RefReader m a -> RefCreator m (RefReader m a)
delay_ v1 r = delayPrev v1 (const id <$> r) r


--------------------------------------------------------------------------------
-- TODO: bidirectional stabilize for Ref

--------------------------------------------------------------------------------
-- TODO: relay


--------------------------------------------------------------------------------

data OnChange c a m = OnChange
    { _ocValue     :: Value a
    , _ocRefR      :: RefReader m (RefCreator m a)
    , _ocChildren  :: c (TriggerList m)
    }

ocChildren :: Lens' (OnChange c a m) (c (TriggerList m))
ocChildren tr ~OnChange{..} = tr _ocChildren <&> \_ocChildren -> OnChange{..}

ocBody_ :: (MonadTrace m, IsSeq c) => Int -> TPath (OnChange c a) m -> RefCreator m b -> RefCreator m b
ocBody_ idx = inContext ("C" ++ show idx) (ocChildren . at' idx)

instance IsSeq c => IsTrigger (OnChange c a) where
    type Val (OnChange c a) = a
    val tr ~OnChange{..} = tr _ocValue <&> \_ocValue -> OnChange{..}
    collectChildren ~OnChange{..} = concatMap toList' $ toList' _ocChildren
    runTrigger_ whenChanged _ i ~OnChange{..}
        = whenChanged _ocRefR $ writeRefSafe' (refOf i) <=< lift . ocBody
      where
        ocBody a = do
            idx <- RefCreator $ tpSnd i . ocChildren %%= \ch -> if (==0) $ length' $ last' ch
                then (length' ch - 1, ch)
                else (length' ch, ch `snoc'` mempty)
            ocBody_ idx i a

generator_ :: forall m b. (MonadTrace m, MonadFix m) => Bool -> RefCreator m b -> RefReader m (RefCreator m b) -> RefCreator m (Ref m b)
generator_ True first _ocRefR = addTrigger' (\_ocValue -> OnChange{_ocChildren = singleton mempty :: FakeSeq (TriggerList m), ..}) $
    \i -> createVal =<< ocBody_ 0 i first
generator_ False first _ocRefR = addTrigger' (\_ocValue -> OnChange{_ocChildren = singleton mempty :: Seq (TriggerList m), ..}) $
    \i -> createVal =<< ocBody_ 0 i first

---------- derived

onChange' :: (MonadTrace m, MonadFix m) => RefReader m (RefCreator m b) -> RefCreator m (Ref m b)
onChange' r = readerToCreator r >>= \i -> generator_ True i r

joinCreator :: (MonadTrace m, MonadFix m) => RefReader m (RefCreator m b) -> RefCreator m (RefReader m b)
joinCreator = fmap readRef . onChange'

generator' :: (MonadTrace m, MonadFix m) => RefReader m (RefCreator m b) -> RefCreator m (RefReader m b)
generator' r = readerToCreator r >>= \i -> readRef <$> generator_ False i r

onChangeMemo' :: (SimpleRefs m, MonadTrace m, MonadFix m, Ord a) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeMemo' r f = do
    memo <- newSimpleRef mempty
    generator' $ r <&> \a -> modSimpleRef memo $ \ma -> case Map.lookup a ma of
        Just b -> return (ma, b)
        Nothing -> do
            b <- f a
            return (Map.insert a b ma, b)


{- depricated
onChange :: (MonadTrace m, MonadFix m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChange r f = joinCreator $ f <$> r

onChange_ :: (MonadTrace m, MonadFix m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChange_ r f = onChange' $ f <$> r

onChangeEq :: (Eq a, MonadTrace m, MonadFix m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEq r f = stabilize r >>= joinCreator . fmap f

onChangeEq_ :: (Eq a, MonadTrace m, MonadFix m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChangeEq_ r f = stabilize r >>= onChange' . fmap f

onChangeEqOld :: (Eq a, MonadTrace m, MonadFix m) => RefReader m a -> (a -> a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEqOld r f = do
    v <- readerToCreator r
    stabilize r >>= \r' -> delay_ v r' >>= \r'' -> joinCreator $ f <$> r'' <*> r'

onChangeMemo_ :: (SimpleRefs m, MonadTrace m, MonadFix m, Ord a) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeMemo_ r a = stabilize r >>= flip onChangeMemo' a

onChangeMemo :: (SimpleRefs m, MonadTrace m, MonadFix m, Ord a) => RefReader m a -> (a -> RefCreator m (RefCreator m b)) -> RefCreator m (RefReader m b)
onChangeMemo r f = stabilize r >>= flip onChangeMemo' f >>= joinCreator
-}

--------------------------------------------------------------------------------

{-
runTrigger' :: Monad' m => Path -> Trigger m -> RefReader m (Backtrack m (Maybe ()))
runTrigger' = runTrigger_ (<&>) sor

sor :: Monad' m => RefReader m a -> RefReader m a -> RefReader m a
sor r1 r2 = do
    present <- RefReader $ lift $ asks fst
    (_, (t, _)) <- RefReader $ lift $ lift $ runWriterT $ flip runReaderT False $ runRefReader_ r1
    if t == present then r1 else r2
-}



