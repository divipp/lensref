{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
module LensRef.BruteForce
    ( -- * Monads
      RefReader
    , RefCreator
    , RefWriter
    , readerToWriter
    , readerToCreator
    , runRefCreator'
    , runRefCreator

    , FakeIO
    , runFakeIO
    , putStr'

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
--    , onChangeEqOld'
    , onChangeMemo

    -- * Other
    , currentValue
    , RegionStatusChange (..)
    , onRegionStatusChange
    , onRegionStatusChange_

    -- * Reference context
    , RefContext (..)
    , Reversible (..)
    , SimpleRefs (..)
    ) where

import Data.Monoid
import Data.Maybe
import Data.List
import Data.Set (Set)
import Data.String
import Data.IORef
import Data.STRef
import qualified Data.Set as Set
import qualified Data.Sequence as S
import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.ST
--import Control.Monad.Free
import Control.Monad.Operational
import Control.Lens
import Debug.Trace

import Data.Function
import Control.Monad.Trans
import Control.Concurrent

import Unsafe.Coerce

infixr 8 `lensMap`

--------------------------------------------------------------------------------

class (Monad m, Applicative m) => Monad' m where
instance Monad' IO where
instance Monad' (ST s) where
instance Monad' Identity where
instance Monad' m => Monad' (Rev m) where
instance Monad' m => Monad' (ReaderT r m) where
instance (Monad' m, Monoid w) => Monad' (WriterT w m) where
instance Monad' m => Monad' (StateT s m) where
instance Monad' m => Monad' (RefReader m) where
instance Monad' m => Monad' (RefWriter m) where
instance Monad' m => Monad' (RefCreator m) where

-------------------------------------------------------------------------------- aux

type List = S.Seq

type Exc = ExceptT String

noExc :: Monad m => String -> Exc m b -> m b
noExc msg m = runExceptT m >>= \case
    Left er  -> error $ msg ++ ": " ++ er
    Right x -> return x

when' :: Monad m => Bool -> m (Maybe a) -> m (Maybe a)
when' b m = if b then m else return Nothing

toList :: List a -> [a]
toList x = case S.viewl x of
    a S.:< x -> a: toList x
    _ -> []

newtype MM m = MM { getMM :: m () }
instance Monad m => Monoid (MM m) where
    mempty = MM $ return ()
    MM a `mappend` MM b = MM $ a >> b

--------------------------------------------------------------------------------

class (Monad' m) => Reversible m where
    restore :: m (Either (m a) a) -> m a        -- Left: restore state & continue, Right: keep state & return

instance Reversible Identity where
    restore m = either id return $ runIdentity m

instance Reversible m => Reversible (ReaderT r m) where
    restore m = ReaderT $ \r -> restore $ runReaderT m r <&> (flip runReaderT r +++ id)

instance (Reversible m, Monoid e) => Reversible (WriterT e m) where
    restore m = WriterT $ restore $ runWriterT m <&> \(a, e) -> runWriterT +++ flip (,) e  $ a

instance Reversible m => Reversible (StateT st m) where
    restore m = StateT $ \st -> restore $ runStateT m st <&> \(a, st') -> flip runStateT st +++ flip (,) st' $ a

instance Reversible m => Reversible (RefCreator m) where
    restore m = RefCreator $ restore $ runRefCreator'' m <&> (runRefCreator'' +++ id)

instance Monad' m => Reversible (Rev m) where
    restore m = singleton $ Restore m

-- ha az első fail, attól a második még átmehet
-- első fail, második semleges -> fail
orr :: Reversible m => Exc m (Maybe a) -> Exc m (Maybe a) -> Exc m (Maybe a)
orr m1 m2 = ExceptT $ restore $ runExceptT m1 <&> \case
    Right (Just a) -> Right $ Right $ Just a
    Right Nothing -> Left $ runExceptT m2
    Left e -> Left $ runExceptT m2 <&> \case
        Right Nothing -> Left e
        x -> x

--------------------------------------------------------------------------------

class Monad' m => SimpleRefs m where
    type SimpleRef m :: * -> *   -- simple reference
    newSimpleRef   :: a -> m (SimpleRef m a)
    readSimpleRef  :: SimpleRef m a -> m a
    writeSimpleRef :: SimpleRef m a -> a -> m ()

instance SimpleRefs IO where
    type SimpleRef IO = IORef
    newSimpleRef x = newIORef x
    readSimpleRef r = readIORef r
    writeSimpleRef r a = writeIORef r a

instance SimpleRefs (ST s) where
    type SimpleRef (ST s) = STRef s
    newSimpleRef    = newSTRef
    readSimpleRef   = readSTRef
    writeSimpleRef  = writeSTRef

instance SimpleRefs m => SimpleRefs (ReaderT r m) where
    type SimpleRef (ReaderT r m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

instance (SimpleRefs m, Monoid w) => SimpleRefs (WriterT w m) where
    type SimpleRef (WriterT w m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

instance (SimpleRefs m) => SimpleRefs (StateT w m) where
    type SimpleRef (StateT w m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

-- TODO: Is this needed? If not, move to Extra module
instance SimpleRefs m => SimpleRefs (RefCreator m) where
    type SimpleRef (RefCreator m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

instance SimpleRefs m => SimpleRefs (Rev m) where
    type SimpleRef (Rev m) = SimpleRef m
    newSimpleRef a = neut $ newSimpleRef a
    readSimpleRef r = neut $ readSimpleRef r
    writeSimpleRef r a = readSimpleRef r >>= \v -> singleton $ Rev (writeSimpleRef r a) (writeSimpleRef r v)

modifyMVar' :: SimpleRefs m => SimpleRef m a -> (a -> m (a, b)) -> m b
modifyMVar' x f = do
    v <- readSimpleRef x
    (v', a) <- f v
    writeSimpleRef x v'
    return a

memoRead :: SimpleRefs m => m a -> m (m a)
memoRead g = do
    s <- newSimpleRef Nothing
    pure $ readSimpleRef s >>= \case
        Just a -> pure a
        Nothing -> g >>= \a -> a <$ writeSimpleRef s (Just a)

--------------------------------------------------------------------------------

class (SimpleRefs m, Reversible m) => RefContext m where
instance RefContext (Rev IO) where
instance RefContext (Rev (ST s)) where
instance RefContext m => RefContext (ReaderT r m) where
instance (RefContext m, Monoid w) => RefContext (WriterT w m) where
instance RefContext m => RefContext (StateT s m) where

--------------------------------------------------------------------------------

type Rev m = ProgramT (RevI m) m
type FakeIO m = Rev m

data RevI m a where
    Rev :: m a -> m () -> RevI m a
    Post :: m () -> RevI m ()
    Restore :: Rev m (Either (Rev m a) a) -> RevI m a

neut m = singleton $ Rev m (return ())
postponed m = singleton $ Post m

runFakeIO :: Monad m => FakeIO m a -> m a
runFakeIO = interpret

interpret :: Monad m => Rev m a -> m a
interpret = eval <=< viewT
  where
    eval :: Monad m => ProgramViewT (RevI m) m a -> m a
    eval (Return x)        = return x
    eval (Rev m r :>>= k)  = m >>= interpret . k
    eval (Post m :>>= k)   = m >>= interpret . k
    eval (Restore m :>>= k) = do
        (e, (post, rev)) <- runWriterT $ interpret' m
        case e of
            Left m  -> getMM (getDual rev) >> interpret (m >>= k)
            Right x -> getMM post >> interpret (k x)

interpret' :: Monad m => Rev m a -> WriterT (MM m, Dual (MM m)) m a
interpret' = eval <=< lift . viewT
  where
    eval :: Monad m => ProgramViewT (RevI m) m a -> WriterT (MM m, Dual (MM m)) m a
    eval (Return x)        = return x
    eval (Rev m r :>>= k)  = tell (mempty, Dual $ MM r) >> lift m >>= interpret' . k
    eval (Post m :>>= k)   = tell (MM m, mempty) >> interpret' (k ())
    eval (Restore m :>>= k)  = do
        (e, (post, rev)) <- lift $ runWriterT $ interpret' m
        case e of
            Left m  -> lift (getMM $ getDual rev) >> interpret' (m >>= k)
            Right x -> tell (post, mempty) >> interpret' (k x)

-- 53640 Ft
--------------------

print' :: Show a => a -> FakeIO IO ()
print' s = postponed $ print s

putStr' :: String -> FakeIO IO ()
putStr' s = postponed $ putStr s

forkIO' :: IO () -> FakeIO IO ()
forkIO' m = postponed $ void $ forkIO m

-------------------------------------------------------------------------------- time

newtype Time = Time Int
    deriving (Eq, Ord, Show)

instance Monoid Time where
    mempty = Time 0
    mappend = max

nextTime :: Time -> Time
nextTime (Time x) = Time (x + 1)

getTime :: MonadReader (Time, a) m => m Time
getTime = asks fst

inPast :: MonadReader (Time, a) m => m b -> m b
inPast = local (prevTime *** id)
  where
    prevTime (Time 0) = error "before 0"
    prevTime (Time x) = Time (x - 1)

--------------------------------------------------------------------------------

data Value a = Value
    { creation :: Time
    , access   :: Time  -- invariant:  access >= creation
    , val      :: a
    }

createVal :: Time -> a -> Value a
createVal t a = Value t t a

getVal :: (MonadWriter Time m, MonadError String m, MonadState (Value a) m) => Bool -> Time -> m a
getVal setTime time = do
    Value {..} <- get
    when (time < creation) $ throwError $ "getVal: " ++ show (time, creation)
    when setTime $ put $ Value {access = access `mappend` time, ..}
    tell creation
    return val

setVal :: (MonadError String m, MonadState (Value a) m) => Time -> a -> m ()
setVal time a = do
    Value {..} <- get
    when (access >= time) $ throwError "setVal"
    put $ createVal time a

createVal' :: Monad' m => a -> RefCreator m (Value a)
createVal' x = getTime <&> \present -> createVal present x

--------------------------------------------------------------------------------

newtype RefReader m a = RefReader { runRefReader_ :: ReaderT Bool (WriterT (Time, Set Id) (Backtrack m)) a }
    deriving (Functor, Applicative, Monad)

runRefReader :: Monad' m => RefReader m a -> Backtrack m (a, Time)
runRefReader (RefReader m) = (id *** fst) <$> runWriterT (flip runReaderT True m)

readRef :: Monad' m => Ref m a -> RefReader m a
readRef (Ref (r, _)) = r

-- eliminate?
currentValue :: Monad' m => RefReader m a -> RefReader m a
currentValue = RefReader . lift . lift . simpleRead

simpleRead :: Monad' m => RefReader m a -> Backtrack m a
simpleRead = fmap fst . runRefReader

readInPast :: Monad' m => RefReader m a -> Backtrack m a
readInPast = inPast . simpleRead

whenChanged :: Monad' m => Bool -> RefReader m a -> (a -> Backtrack m (Maybe b)) -> Backtrack m (Maybe b)
whenChanged check r m = do
    present <- getTime
    (a, t) <- runRefReader r
    when' (not check || t == present) $ m a

--------------------------------------------------------------------------------

instance (IsString str, Monad s, Functor s) => IsString (RefReader s str) where
    fromString = pure . fromString

instance (Monad' s, Num a) => Num (RefReader s a) where
    (+) = liftA2 (+)
    (*) = liftA2 (*)
    negate = fmap negate
    abs    = fmap abs
    signum = fmap signum
    fromInteger = pure . fromInteger

instance (Monad' s, Fractional a) => Fractional (RefReader s a) where
    recip  = fmap recip
    fromRational = pure . fromRational


--------------------------------------------------------------------------------

newtype Ref m a = Ref (RefReader m a, a -> Backtrack m ())

unitRef :: Monad' m => Ref m ()
unitRef = Ref (return (), \() -> return ())

lensMap :: Monad' m => Lens' a b -> Ref m a -> Ref m b
lensMap k (Ref (g, s)) = Ref ((^. k) <$> g, (readInPast g >>=) . (s .) . (k .~))

joinRef :: Monad' m => RefReader m (Ref m a) -> Ref m a
joinRef rr = Ref (join $ readRef <$> rr, (readInPast rr >>=) . (. writeRefSafe) . flip ($))

writeRefSafe :: Ref m a -> a -> Backtrack m ()
writeRefSafe (Ref (_, w)) = w

--------------------------------------------------------------------------------

newtype RefCreator m a = RefCreator { runRefCreator'' :: StateT (TMap m) (ReaderT (Time, Id) m) a }
    deriving (Functor, Applicative, Monad, MonadState (TMap m), MonadReader (Time, Id))

instance MonadTrans RefCreator where
    lift = RefCreator . lift . lift

type Backtrack m = Exc (RefCreator m)

readerToCreator :: Monad' m => RefReader m a -> RefCreator m a
readerToCreator = noExc "rToC" . simpleRead

runRefCreator' :: Monad m => RefCreator m (RefWriter m a) -> m a
runRefCreator' f = do
    (x, st) <- flip runReaderT (nextTime mempty, root) $ flip runStateT mempty $ runRefCreator'' f
    flip runReaderT root $ flip evalStateT (nextTime mempty, st) $ runRefWriter x

--------------------------------------------------------------------------------

runRefCreator :: forall a m . (Reversible m, SimpleRefs m) => ((forall b . RefWriter m b -> m b) -> RefCreator m a) -> m a
runRefCreator f = do
    st <- newSimpleRef (nextTime mempty, mempty)
    let g :: forall b . RefWriter m b -> m b
        g x = modifyMVar' st $ \s -> do
                (y, s') <- flip runReaderT root $ flip runStateT s $ runRefWriter x
                return (s', (y))

    let m = f g :: RefCreator m a
    modifyMVar' st $ \(t, trs) -> do
        ((x, trs')) <- flip runReaderT (t, root) $ flip runStateT trs $ runRefCreator'' m
        return ((t, trs'), (x))

runRefCreatorRev :: forall a m . SimpleRefs m => ((forall b . RefWriter (Rev m) b -> m b) -> RefCreator (Rev m) a) -> m a
runRefCreatorRev f = interpret $ runRefCreator $ \g -> f $ interpret . g

--------------------------------------------------------------------------------

newtype RefWriter m a = RefWriter { runRefWriter :: StateT (Time, TMap m) (ReaderT Id m) a }
    deriving (Functor, Applicative, Monad)

instance MonadTrans RefWriter where
    lift = RefWriter . lift . lift

creatorToWriter :: Monad' m => RefCreator m a -> RefWriter m a
creatorToWriter = RefWriter . (\f -> StateT $ \(time, st) -> ReaderT $ \i -> fmap (id *** (,) time) $ flip runReaderT (time, i) $ runStateT f st) . runRefCreator''

readerToWriter :: Monad' m => RefReader m a -> RefWriter m a
readerToWriter = creatorToWriter . readerToCreator

writeRef :: forall m a . Reversible m => Ref m a -> a -> RefWriter m ()
writeRef r x = do
    RefWriter $ _1 %= nextTime
    creatorToWriter $ do
        noExc "writeRef" $ writeRefSafe r x
        noExc "fatal" $ runTriggers
  where
    runTriggers :: Backtrack m ()
    runTriggers = do
        present <- getTime
        trs <- filterTriggers =<< activeTriggers
        void $ foldr orr (return Nothing) $ trs <&> \(i, tr) -> do
            triggers_at i %= fmap (_1 .~ present)
            runTrigger i tr >>= \case
                Nothing -> return Nothing
                Just _tr -> do
                    runTriggers
                    return $ Just ()


--------------------------------------------------------------------------------

newtype Id = Id [Int] deriving (Show, Eq, Ord)

consId :: Id -> Int -> Id
consId (Id r) i = Id $ r ++ [i]

inContext :: MonadReader (a, Id) m => Id -> m b -> m b
inContext i m = local (id *** const i) m

root = Id []
isRoot (Id cs) = null cs

parentId (Id cs) = Id $ init cs
idLast (Id cs) = last cs

--------------------------------------------------------------------------------

type TMap m = List (Time, Trigger m)    -- Time: mikor futtattuk utoljára

trigger_at :: Id -> Lens' (TMap m) (Time, Trigger m)
trigger_at i = triggers_at' (parentId i) . at' (idLast i)

triggers_at :: Id -> Lens' (TMap m) (Maybe (Time, Trigger m))
triggers_at i = triggers_at' (parentId i) . at' (idLast i)
  where
    at' i tr m 
        | S.length m <= i = tr Nothing <&> \Nothing -> m
        | otherwise = tr (Just $ S.index m i) <&> \(Just x) -> S.update i x m

triggers_at' :: Id -> Lens' (TMap m) (TMap m)
triggers_at' (Id is) = rou' is
  where
    rou' [] = id
    rou' (i:is) = at' i . _2 . ch . rou' (is)
      where
        ch tr OnChange{..} = tr _ocChildren <&> \_ocChildren -> OnChange{..}
        ch tr OnChangeMemo{..} = tr (_ocmLast ^. _2 . _1) <&> \x -> OnChangeMemo{_ocmLast = _2 . _1 .~ x $ _ocmLast,  ..}
        ch _ _ = error $ "rou" ++ show (i:is) 

at' i tr m = tr (S.index m i) <&> \x -> S.update i x m

filterTriggers :: Reversible m => [(Id, Trigger m)] -> Backtrack m [(Id, Trigger m)]
filterTriggers trs = return trs {-do
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

activeTriggers :: Monad' m => Backtrack m [(Id, Trigger m)]
activeTriggers = do
    present <- getTime
    let
        g :: Id -> [Time] -> TMap m -> [(Id, [Time], Trigger m)]
        g r ts trs = concatMap h $ zip [0..] (toList trs)
          where
            h (i, (t, x)) = (i', t', x): f x
              where
                i' = consId r i
                t' = t: ts
                f OnChange{..} = g i' t' _ocChildren
                f OnChangeMemo{..} = g i' t' $ _ocmLast ^. _2 . _1
                f x = mempty

        ok ts@(t:_) = t < present -- && all (zipWith () ts $ tail ts)

    trs <- get
    return $ map (\(x,_,y)->(x,y)) $ filter (ok . (^. _2)) $ g root [] trs

addTrigger :: Monad' m => (Id -> (Trigger m, RefCreator m a)) -> RefCreator m a
addTrigger ft = do
    r <- asks snd
    trs <- use $ triggers_at' r
    let (t, a) = ft $ consId r $ S.length trs
    present <- getTime
    triggers_at' r %= (S.|> (present, t))
    a

--------------------------------------------------------------------------------

data Trigger m where
    ExtendRef ::
        { _value        :: Value a
        , _erRef        :: Ref m b
        , _erLens       :: ALens' a b
        } -> Trigger m
    Stabilize ::
        { _value        :: Value a
        , _ocRefR       :: RefReader m a
        , _ocEq         :: a -> a -> Bool
        } -> Trigger m
    OnChange ::
        { _value        :: Value a
        , _ocRefR'      :: RefReader m (RefCreator m a)
        , _ocChildren   :: TMap m
        , _ocKill       :: RefReader m (m ())
        } -> Trigger m
    OnOld ::
        { _value'       :: Value (a, a)
        , _ocRefR       :: RefReader m a
        } -> Trigger m
    OnChangeMemo ::
        { _value        :: Value a
        , _ocRefR       :: RefReader m b
        , _ocmAction    :: b -> RefCreator m a
        , _ocmLast      :: (b -> Bool, (TMap m, a, RegionStatusChange' -> RefReader m (m ())))
        , _ocMemo       :: [(b -> Bool, (TMap m, a, RegionStatusChange' -> RefReader m (m ())))]
        , _ocEq         :: b -> b -> Bool
        } -> Trigger m

accessRef :: Monad' m => Id -> Ref m a
accessRef i = Ref (get', set') where
    v = value
    get' = RefReader $ do
        present <- lift getTime
        ReaderT $ \setTime -> (mapWriterT $ fmap (fmap $ flip (,) $ Set.singleton i) . mapExceptT RefCreator) $ zoom (triggers_at i) $ mapWriterT ex $ zoom (_2 . v) $ getVal setTime present
    set' a = do
        present <- getTime
        mapExceptT RefCreator $ zoom (triggers_at i) $ ex $ zoom (_2 . v) $ setVal present a

    ex :: Monad' m => Exc (StateT a m) x -> Exc (StateT (Maybe a) m) x
    ex = mapExceptT $ \(StateT f) -> StateT $ maybe (return (Left "accessRef", Nothing)) $ fmap (id *** Just) . f

    value :: Lens' (Trigger m) (Value a)
    value tr ExtendRef{..}    = tr (unsafeCoerce _value) <&> \(unsafeCoerce -> _value) -> ExtendRef{..}
    value tr Stabilize{..}    = tr (unsafeCoerce _value) <&> \(unsafeCoerce -> _value) -> Stabilize{..}
    value tr OnOld{..}        = tr (unsafeCoerce _value') <&> \(unsafeCoerce -> _value') -> OnOld{..}
    value tr OnChange{..}     = tr (unsafeCoerce _value) <&> \(unsafeCoerce -> _value) -> OnChange{..}
    value tr OnChangeMemo{..} = tr (unsafeCoerce _value) <&> \(unsafeCoerce -> _value) -> OnChangeMemo{..}

finalize :: Monad' m => Maybe RegionStatusChange' -> Trigger m -> Backtrack m ()
finalize msg = \case
    OnChange{..} -> do
        delTriggers _ocChildren
        when (msg == Nothing) $ lift $ join $ readerToCreator $ lift <$> _ocKill
    OnChangeMemo{..} -> do
        delTriggers $ _ocmLast ^. _2 . _1
        maybe (return ()) (lift . join . readerToCreator . fmap lift . (_ocmLast ^. _2 . _3)) msg
    _ -> return ()
  where
    delTriggers ids = do
        present <- getTime
        let delTrigger (t, tr)
                | t >= present = throwError "delTrigger"
                | otherwise = finalize msg tr
        mapM_ delTrigger $ toList ids

--------------------------------------------------------------------------------

extendRef :: Monad' m => Ref m b -> Lens' a b -> a -> RefCreator m (Ref m a)
extendRef _erRef _erLens a = do
    r0 <- readerToCreator $ readRef _erRef
    _value <- createVal' $ set _erLens r0 a
    addTrigger $ \i -> (ExtendRef{..}, return $ accessRef i)

stabilize :: Monad' m => (a -> a -> Bool) -> RefReader m a -> RefCreator m (RefReader m a)
stabilize _ocEq _ocRefR = do
    x <- readerToCreator _ocRefR
    _value <- createVal' x
    addTrigger $ \i -> (Stabilize{..}, return $ readRef $ accessRef i)

onOld :: Monad' m => RefReader m a -> RefCreator m (RefReader m (a, a))
onOld _ocRefR = do
    x <- readerToCreator _ocRefR
    _value' <- createVal' (x, x)
    addTrigger $ \i -> (OnOld{..}, return $ readRef $ accessRef i)

onChange' :: Monad' m => RefReader m (RefCreator m b) -> RefCreator m (Ref m b)
onChange' _ocRefR' = do
    _value <- inPast $ createVal' undefined
    let t = OnChange{_ocChildren=mempty,_ocKill= return $ return (),..}
    addTrigger $ \i -> (,) t $ do
        noExc "onCh" $ fireOnChange (whenChanged False) i t
        return $ accessRef i

onChangeMemo' :: Monad' m => (a -> a -> Bool) -> RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeMemo' _ocEq _ocRefR _ocmAction = do
    _value <- inPast $ createVal' undefined
    let t = OnChangeMemo{_ocMemo = [], _ocmLast= (const False, (mempty, error "2", const $ return $ return ())), ..}
    addTrigger $ \i -> (,) t $ do
        noExc "onCh" $ fireOnChangeMemo (whenChanged False) i t
        return $ readRef $ accessRef i

--------------------------------------------------------------------------------

ocmLast :: Lens' (Trigger m) (b -> Bool, (TMap m, a, RegionStatusChange' -> RefReader m (m ())))
ocmLast tr OnChangeMemo{..} = tr (unsafeCoerce _ocmLast) <&> \(unsafeCoerce -> _ocmLast) -> OnChangeMemo{..}

ocMemo :: Lens' (Trigger m) [(b -> Bool, (TMap m, a, RegionStatusChange' -> RefReader m (m ())))]
ocMemo tr OnChangeMemo{..} = tr (unsafeCoerce _ocMemo) <&> \(unsafeCoerce -> _ocMemo) -> OnChangeMemo{..}

fireOnChange :: Monad' m => (RefReader m (RefCreator m a) -> (RefCreator m a -> Backtrack m (Maybe ())) -> e)  -> Id -> Trigger m -> e
fireOnChange whenChanged i t@OnChange{..} = unsafeCoerce whenChanged _ocRefR' $ \a -> do
    finalize Nothing t
    trigger_at i . _2 %= (\OnChange{..} -> OnChange{_ocChildren = mempty, _ocKill = return $ return (), ..})
    b <- inContext i $ lift a
    writeRefSafe (accessRef i) b
    return $ Just ()

fireOnChangeMemo :: Monad' m => (RefReader m b -> (b -> Backtrack m (Maybe ())) -> e)  -> Id -> Trigger m -> e
fireOnChangeMemo whenChanged i t@OnChangeMemo{..} = unsafeCoerce whenChanged _ocRefR $ \a -> do
    let (a_, (ids, b_, res_)) = _ocmLast
    when' (not $ a_ a) $ do
        finalize (Just Block') t
        trigger_at i . _2 . ocmLast . _2 . _1 .= mempty
        trigger_at i . _2 . ocmLast . _2 . _3 .= const (return $ return ())
        (ub, b) <- case [y | (x, y) <- _ocMemo, x a] of
          [] -> do
            b <- inContext i $ lift $ _ocmAction a
            return (False, b)
          [(trs, b, res)] -> do
            trigger_at i . _2 . ocmLast . _2 . _1 .= trs
            trigger_at i . _2 . ocmLast . _2 . _3 %= liftA2 (flip (>>)) res
            return (True, b)
        writeRefSafe (accessRef i) b
        trigger_at i . _2 . ocMemo %= \l -> (a_, (ids, b_, res_)): filter (not . ($ a) . fst) l
        trigger_at i . _2 . ocmLast . _1 .= _ocEq a
        trigger_at i . _2 . ocmLast . _2 . _2 .= b
        tr <- use $ trigger_at i
        when ub $ finalize (Just Unblock') $ snd tr
        return $ Just ()

runTrigger' :: Monad' m => Id -> Trigger m -> RefReader m (Backtrack m (Maybe ()))
runTrigger' = runTrigger_ (<&>) sor

sor :: Monad' m => RefReader m a -> RefReader m a -> RefReader m a
sor r1 r2 = do
    present <- RefReader $ lift $ asks fst
    (x, (t, _)) <- RefReader $ lift $ lift $ runWriterT $ flip runReaderT False $ runRefReader_ r1
    if t == present then r1 else r2

runTrigger :: Reversible m => Id -> Trigger m -> Backtrack m (Maybe ())
runTrigger = runTrigger_ (whenChanged True) orr

runTrigger_ :: Monad' m => (forall b . RefReader m b -> (b -> Backtrack m (Maybe ())) -> e) -> (e -> e -> e) -> Id -> Trigger m -> e
runTrigger_ whenChanged orr i t = case t of
    OnChange{} -> fireOnChange whenChanged i t
    OnChangeMemo{} -> fireOnChangeMemo whenChanged i t
    ExtendRef{..} -> do
        let r_ = accessRef i
        orr (whenChanged (readRef r_) $ \a -> do
                writeRefSafe _erRef $ a ^. cloneLens _erLens
                return $ Just ()
            )
            (whenChanged (readRef _erRef) $ \b -> do
                a <- readInPast $ readRef r_
                writeRefSafe r_ $ cloneLens _erLens .~ b $ a
                return $ Just ()
            )

    Stabilize{..} -> whenChanged _ocRefR $ \a -> do
        let r_ = accessRef i
        old <- readInPast $ readRef r_
        when' (not $ _ocEq a old) $ do
            writeRefSafe r_ a
            return $ Just ()

    OnOld{..} -> whenChanged _ocRefR $ \a -> do
        let r_ = accessRef i
        (a1, a2) <- readInPast $ readRef r_
        writeRefSafe r_ (a2, a)
        return $ Just ()

data RegionStatusChange' = Block' | Unblock' deriving (Eq, Ord)
instance Show RegionStatusChange' where
    show Block' = "Block"
    show Unblock' = "Unblock"
data RegionStatusChange = Kill | Block | Unblock deriving (Eq, Ord, Show)

onRegionStatusChange :: Monad' m => (RegionStatusChange -> m ()) -> RefCreator m ()
onRegionStatusChange f = onRegionStatusChange_ $ \msg -> return $ f msg

onRegionStatusChange_ :: Monad' m => (RegionStatusChange -> RefReader m (m ())) -> RefCreator m ()
onRegionStatusChange_ f = do
    c <- asks snd
    noExc "ors" $ setF fg c
    noExc "ors'" $ setF fg' c
    return ()
  where
    g Block' = Block
    g Unblock' = Unblock

    setF _ c | isRoot c = return ()
    setF fg c = do
        ok <- fg c . snd =<< use (trigger_at c)
        when (not ok) $ setF fg $ parentId c

    fg c = \case
        OnChange{..} -> do
            trigger_at c . _2 .= OnChange{_ocKill=_ocKill >> f Kill, ..}
            return True
        _ -> return False

    fg' c = \case
        OnChangeMemo{..} -> do
            trigger_at c . _2 . ocmLast . _2 . _3 %= liftA2 (flip (>>)) (f . g)
            return True
        _ -> return False

--------------------------------------------------------------------------------

newRef :: Monad' m => a -> RefCreator m (Ref m a)
newRef = extendRef unitRef united

joinCreator :: Monad' m => RefReader m (RefCreator m b) -> RefCreator m (RefReader m b)
joinCreator = fmap readRef . onChange'

onChange :: Monad' m => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChange r f = joinCreator $ f <$> r

onChange_ :: Monad' m => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChange_ r f = onChange' $ f <$> r

onChangeEq :: (Eq a, Monad' m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEq r f = stabilize (==) r >>= \r' -> onChange r' f

onChangeEq_ :: (Eq a, Monad' m) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (Ref m b)
onChangeEq_ r f = stabilize (==) r >>= \r' -> onChange_ r' f

onChangeMemo :: (Monad' m, Eq a) => RefReader m a -> (a -> RefCreator m (RefCreator m b)) -> RefCreator m (RefReader m b)
onChangeMemo r f = onChangeMemo_ r f >>= joinCreator

onChangeMemo_ :: (Monad' m, Eq a) => RefReader m a -> (a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeMemo_ = onChangeMemo' (==)

modRef :: Reversible m => Ref m a -> (a -> a) -> RefWriter m ()
r `modRef` f = readerToWriter (readRef r) >>= writeRef r . f

onChangeEqOld :: (Eq a, Monad' m) => RefReader m a -> (a -> a -> RefCreator m b) -> RefCreator m (RefReader m b)
onChangeEqOld r f = stabilize (==) r >>= \r' -> onOld r' >>= \r'' -> onChange r'' $ uncurry f

--------------------------------------------------------------------------------

type Prog = Writer [Maybe (Either String String)]

--message :: String -> RefCreator Prog ()
message = lift . message_

message_ s = tell [Just $ Right $ "message: " ++ s]

send x y = lift (tell [Nothing]) >> writeRef x y
message' s = lift $ tell [Just $ Left $ "message: " ++ s]

runProg :: String -> Prog () -> IO ()
runProg name p = showRes . f [] . snd $ runWriter p
  where
    showRes [] = return ()
    showRes xs = fail $ "\ntest " ++ name ++ " failed.\n" ++ unlines xs ++ "\n"

    f acc (Just (Right x): xs) = f (acc ++ [x]) xs
    f (s:acc) (Just (Left s'): xs) | s == s' = f acc xs
    f [] (Nothing: xs) = f [] xs
    f acc (Just (Left s'): _) = acc ++ ["Left " ++ s'] -- s == s' = f acc xs
    f acc _ = acc

runTests :: IO ()
runTests = do

    let runTest :: String -> (RefCreator Prog (RefWriter Prog ())) -> IO ()
        runTest name t = do
            putStrLn $ "running test " ++ name
            runProg name $ runRefCreator' t

        a ==? b = when (a /= b) $ message $ show a ++ " /= " ++ show b

        r ==> v = readerToWriter (readRef r) >>= (==? v)

    runTest "trivial" $ return $ return ()

    runTest "newRefTest" $ do
        r <- newRef (3 :: Int)
        return $ do
            r ==> 3

    runTest "writeRefsTest" $ do
        r1 <- newRef (3 :: Int)
        r2 <- newRef (13 :: Int)
        return $ do
            r1 ==> 3
            r2 ==> 13
            writeRef r1 4
            r1 ==> 4
            r2 ==> 13
            writeRef r2 0
            r1 ==> 4
            r2 ==> 0

    runTest "extRefTest" $ do
        r <- newRef $ Just (3 :: Int)
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        return $ do
            r ==> Just 3
            q ==> (True, 3)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 3)
            q1 ==> False
            writeRef q1 True    --
            q1 ==> True
            r ==> Just 3
            writeRef q2 1
            r ==> Just 1

    runTest "joinTest" $ do
        r2 <- newRef (5 :: Int)
        r1 <- newRef 8
        rr <- newRef r1
        return $ do
            r1 ==> 8
            let r = joinRef $ readRef rr
            r ==> 8
            writeRef r1 4
            r ==> 4
            writeRef r 3
            r1 ==> 3
            r2 ==> 5
            writeRef rr r2
            r2 ==> 5
            r ==> 5
            writeRef r1 4
            r ==> 5
            writeRef r2 14
            r ==> 14
            writeRef r 10
            r1 ==> 4
            r2 ==> 10
            writeRef rr r1
            r ==> 4
            r1 ==> 4
            r2 ==> 10
            writeRef r 11
            r ==> 11
            r1 ==> 11
            r2 ==> 10

    runTest "join + ext" $ do
        r2 <- newRef $ Just (5 :: Int)
        r1 <- newRef (Nothing :: Maybe Int)
        rr <- newRef r1
        let r = joinRef $ readRef rr
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
        return $ do
            q ==> (False, 0)
            writeRef r1 $ Just 4
            q ==> (True, 4)
            writeRef q1 False
            r1 ==> Nothing
            writeRef rr r2
            q ==> (True, 5)
            writeRef r1 $ Just 6
            q ==> (True, 5)
            r2 ==> Just 5
            writeRef r2 $ Just 7
            q ==> (True, 7)
            r1 ==> Just 6
            writeRef q1 False
            r2 ==> Nothing
            r1 ==> Just 6
            writeRef q1 True
            r2 ==> Just 7
            r1 ==> Just 6
            writeRef r2 Nothing
            r1 ==> Just 6
            q ==> (False, 7)
            writeRef r1 Nothing
            q ==> (False, 7)

    runTest "join + ext 2" $ do
        r2 <- newRef $ Just (5 :: Int)
        r1 <- newRef Nothing
        rr <- newRef True
        let r = joinRef $ do
                b <- readRef rr
                pure $ if b then r1 else r2
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
        return $ do
            q ==> (False, 0)
            writeRef r1 $ Just 4
            q ==> (True, 4)
            writeRef q1 False
            r1 ==> Nothing
            writeRef rr False
            q ==> (True, 5)
            writeRef r1 $ Just 6
            q ==> (True, 5)
            r2 ==> Just 5
            writeRef q1 False
            r2 ==> Nothing
            r1 ==> Just 6
            writeRef q1 True
            r2 ==> Just 5
            r1 ==> Just 6
            writeRef r2 Nothing
            r1 ==> Just 6
            q ==> (False, 5)

    runTest "joinTest2" $ do
        r1 <- newRef (3 :: Int)
        rr <- newRef r1
        r2 <- newRef 5
        return $ do
            writeRef rr r2
            joinRef (readRef rr) ==> 5

    runTest "chainTest0" $ do
        r <- newRef (1 :: Int)
        q <- extendRef r id 0
        s <- extendRef q id 0
        return $ do
            r ==> 1
            q ==> 1
            s ==> 1
            writeRef r 2
            r ==> 2
            q ==> 2
            s ==> 2
            writeRef q 3
            r ==> 3
            q ==> 3
            s ==> 3
            writeRef s 4
            r ==> 4
            q ==> 4
            s ==> 4

    runTest "forkTest" $ do
        r <- newRef (1 :: Int)
        q <- extendRef r id 0
        s <- extendRef r id 0
        return $ do
            r ==> 1
            q ==> 1
            s ==> 1
            writeRef r 2
            r ==> 2
            q ==> 2
            s ==> 2
            writeRef q 3
            r ==> 3
            q ==> 3
            s ==> 3
            writeRef s 4
            r ==> 4
            q ==> 4
            s ==> 4

    runTest "forkTest2" $ do
        r <- newRef $ Just (1 :: Int)
        q <- extendRef r maybeLens (False, 0)
        s <- extendRef r maybeLens (False, 0)
        return $ do
            r ==> Just 1
            q ==> (True, 1)
            s ==> (True, 1)
            writeRef r $ Just 2
            r ==> Just 2
            q ==> (True, 2)
            s ==> (True, 2)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 2)
            s ==> (False, 2)
            writeRef (_1 `lensMap` q) True
            r ==> Just 2
            q ==> (True, 2)
            s ==> (True, 2)
            writeRef (_2 `lensMap` q) 3
            r ==> Just 3
            q ==> (True, 3)
            s ==> (True, 3)
            writeRef (_1 `lensMap` q) False
            r ==> Nothing
            q ==> (False, 3)
            s ==> (False, 3)
            writeRef (_2 `lensMap` q) 4
            r ==> Nothing
            q ==> (False, 4)
            s ==> (False, 3)
            writeRef (_1 `lensMap` q) True
            r ==> Just 4
            q ==> (True, 4)
            s ==> (True, 4)
            writeRef q (False, 5)
            r ==> Nothing
            q ==> (False, 5)
            s ==> (False, 4)
            writeRef (_1 `lensMap` s) True
            r ==> Just 4
            q ==> (True, 4)
            s ==> (True, 4)

    runTest "chainTest" $ do
        r <- newRef $ Just Nothing
        q <- extendRef r maybeLens (False, Nothing)
        s <- extendRef (_2 `lensMap` q) maybeLens (False, 3 :: Int)
        return $ do
            writeRef (_1 `lensMap` s) False
            r ==> Just Nothing
            q ==> (True, Nothing)
            s ==> (False, 3)
            writeRef (_1 `lensMap` q) False
            r ==> Nothing
            q ==> (False, Nothing)
            s ==> (False, 3)

    runTest "chainTest1" $ do
        r <- newRef $ Just $ Just (3 :: Int)
        q <- extendRef r maybeLens (False, Nothing)
        s <- extendRef (_2 `lensMap` q) maybeLens (False, 0 :: Int)
        return $ do
            r ==> Just (Just 3)
            q ==> (True, Just 3)
            s ==> (True, 3)
            writeRef (_1 `lensMap` s) False
            r ==> Just Nothing
            q ==> (True, Nothing)
            s ==> (False, 3)
            writeRef (_1 `lensMap` q) False
            r ==> Nothing
            q ==> (False, Nothing)
            s ==> (False, 3)
            writeRef (_1 `lensMap` s) True
            r ==> Nothing
            q ==> (False, Just 3)
            s ==> (True, 3)
            writeRef (_1 `lensMap` q) True
            r ==> Just (Just 3)
            q ==> (True, Just 3)
            s ==> (True, 3)

    runTest "mapchain" $ do
        r <- newRef 'x'
        let q = iterate (lensMap id) r !! 10
        return $ do
            q ==> 'x'
            writeRef q 'y'
            q ==> 'y'

    runTest "joinchain" $ do
        rb <- newRef True
        r1 <- newRef 'x'
        r2 <- newRef 'y'
        let f (r1, r2) = (r1', r2') where
                r1' = joinRef $ bool r1 r2 <$> readRef rb
                r2' = joinRef $ bool r2 r1 <$> readRef rb
            (r1', r2') = iterate f (r1, r2) !! 10
        return $ do
            r1' ==> 'x'
            r2' ==> 'y'
            writeRef r1' 'X'
            r1' ==> 'X'
            r2' ==> 'y'
            writeRef r2' 'Y'
            r1' ==> 'X'
            r2' ==> 'Y'
            writeRef rb False
            r1' ==> 'X'
            r2' ==> 'Y'
            writeRef r1' 'x'
            r1' ==> 'x'
            r2' ==> 'Y'
            writeRef r2' 'y'
            r1' ==> 'x'
            r2' ==> 'y'

    runTest "undoTest" $ do
        r <- newRef (3 :: Int)
        q <- extendRef r (lens head $ flip (:)) []
        return $ do
            writeRef r 4
            q ==> [4, 3]

    runTest "undoTest2" $ do
        r <- newRef (3 :: Int)
        q <- extendRef r (lens head $ flip (:)) []
        return $ do
            q ==> [3]


    let
        perform m = m >>= maybe (pure ()) id
        m === t = m >>= \x -> isJust x ==? t

    runTest "undoTest3" $ do
        r <- newRef (3 :: Int)
        (undo, redo) <- fmap (readerToWriter *** readerToWriter) $ undoTr (==) r
        return $ do
            r ==> 3
            redo === False
            undo === False
            writeRef r 4
            r ==> 4
            redo === False
            undo === True
            writeRef r 5
            r ==> 5
            redo === False
            undo === True
            perform undo
            r ==> 4
            redo === True
            undo === True
            perform undo
            r ==> 3
            redo === True
            undo === False
            perform redo
            r ==> 4
            redo === True
            undo === True
            writeRef r 6
            r ==> 6
            redo === False
            undo === True

    runTest "time" $ do
        t1 <- newRef "z"
        r <- newRef "a"
        q_ <- extendRef r (lens fst (\_ x -> (x, ""))) ("","")
        let q = lensMap _2 q_
        t2 <- newRef "z"
        return $ do
            writeRef q "."
            q ==> "."
            writeRef t2 "q"
            q ==> "."
            writeRef t1 "q"
            q ==> "."
{- TODO
    runTest "recursion" $ do
        r <- newRef "x"
        rr <- newRef r
        let r' = joinRef $ readRef rr
        return $ do
            r' ==> "x"
            writeRef rr r'
            r' ==> "x"
-}
    runTest "ordering" $ do
        t1 <- newRef $ Just (3 :: Int)
        t <- newRef t1
        let r = joinRef $ readRef t
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        t2 <- newRef $ Just (3 :: Int)
        return $ do
            r ==> Just 3
            q ==> (True, 3)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 3)
            q1 ==> False
            writeRef q1 True
            r ==> Just 3
            writeRef q2 1
            r ==> Just 1
            writeRef t t2
            r ==> Just 3
            q ==> (True, 3)
            writeRef r Nothing
            r ==> Nothing
            q ==> (False, 3)
            q1 ==> False
            writeRef q1 True
            r ==> Just 3
            writeRef q2 1
            r ==> Just 1

    runTest "message" $ do
        message "Hello"
        return $ do
            message' "Hello"

    runTest "onChangeEq" $ do
        r <- newRef "x"
        _ <- onChangeEq (readRef r) message
        return $ do
            message' "x"
            send r "x"
            send r "y"
            message' "y"

    runTest "onChangeEq + listener" $ do
        r1 <- newRef "x"
        r2 <- newRef "y"
        _ <- onChangeEq (liftA2 (++) (readRef r1) (readRef r2)) message
        return $ do
            message' "xy"
            send r1 "x"
            send r2 "y"
            send r1 "y"
            message' "yy"
            send r2 "y"
            send r2 "x"
            message' "yx"

    runTest "onChangeEq + join" $ do
        r1 <- newRef "x"
        r2 <- newRef "y"
        rr <- newRef r1
        _ <- onChangeEq (readRef $ joinRef $ readRef rr) message
        return $ do
            message' "x"
            send r1 "x"
            send r2 "y"
            send r1 "y"
            message' "y"
            send r2 "y"
            send r2 "x"
            send rr r2
            message' "x"
            send r1 "a"
            send r2 "b"
            message' "b"
            send r2 "c"
            message' "c"

    let showStatus msg = onRegionStatusChange $ \s -> message_ $ show s ++ " " ++ msg

    runTest "onRegionStatusChange" $ do
        r <- newRef True
        onChange (readRef r) $ \i -> do
            showStatus "#1"
        return $ do
            send r False
            message' "Kill #1"
            send r True
            message' "Kill #1"

    runTest "onRegionStatusChange2" $ do
        r <- newRef True
        onChangeMemo_ (readRef r) $ \i -> do
            showStatus "#1"
        return $ do
            send r True
            send r False
            message' "Block #1"
            send r False
            send r True
            message' "Block #1"
            message' "Unblock #1"
            send r True
            send r False
            message' "Block #1"
            message' "Unblock #1"

    let showStatus msg = onRegionStatusChange $ \s -> message_ $ show s ++ " " ++ msg

    runTest "kill & block" $ do
        r <- newRef (0 :: Int)
        r2 <- onChangeMemo_ (readRef r) $ \i -> case i of
            0 -> return $ showStatus "#0"
            1 -> do
                showStatus "#1"
                return $ return ()
            _ -> error $ "Unexpected value for r in kill & block: " ++ show i
        _ <- joinCreator r2

        return $ do
            send r 0
            send r 1
            message' "Kill #0"
            send r 1
            send r 0
            message' "Block #1"
            send r 1
            message' "Unblock #1"
            message' "Kill #0"

    runTest "bla2" $ do
        r <- newRef $ Just (3 :: Int)
        q <- extendRef r maybeLens (False, 0)
        let q1 = _1 `lensMap` q
            q2 = _2 `lensMap` q
        _ <- onChangeEq (readRef r) $ message . show
        _ <- onChangeEq (readRef q) $ message . show
        return $ do
            message' "Just 3"
            message' "(True,3)"
            send r (Nothing :: Maybe Int)
            message' "Nothing"
            message' "(False,3)"
            send q1 True
            message' "Just 3"
            message' "(True,3)"
            send q2 (1 :: Int)
            message' "Just 1"
            message' "(True,1)"

    runTest "onChangeEq value" $ do
        r <- newRef (0 :: Int)
        q <- onChangeEq (readRef r) pure
        _ <- onChangeEq q $ message . show
        return $ do
            message' "0"
            send r (1 :: Int)
            message' "1"
            send r (2 :: Int)
            message' "2"
            send r (3 :: Int)
            message' "3"
            send r (3 :: Int)
            send r (4 :: Int)
            message' "4"
{-
    runTest "schedule" (do
        r <- newRef "a"
        q <- newRef "b"
        _ <- onChangeEq (readRef r) message
        _ <- onChangeEq (readRef q) message
        listen 0 $ \(x,y) -> writeRef r x >> writeRef q y
        listen 1 $ \(x,y) -> writeRef q y >> writeRef r x
        ) $ do
        message' "a"
        message' "b"
        message' "listener #0"
        message' "listener #1"
        pure $ (,) () $ do
            send 0 ("x", "y")
            message' "x"
            message' "y"
            send 1 ("1", "2")
            message' "2"
            message' "1"
-}
{- TODO
    runTest "diamond" (do
        r <- newRef "a"
        q <- newRef "b"
        rq <- onChangeEq (liftA2 (++) (readRef r) (readRef q)) $ pure . pure
        _ <- onChangeEq (join rq) message
        postponeModification $ message "." >> writeRef r "x" >> writeRef q "y"
        postponeModification $ message ".." >> writeRef q "1" >> writeRef r "2"
        ) $ do
        message' "ab"
        pure $ (,) () $ do
            message' "."
            message' "xy"
            message' ".."
            message' "21"
-}

{- not ready
    runTest "notebook" $ do 
        buttons <- newRef ("",[])
        let ctrl = lens fst (\(_,xs) x -> ("",x:xs)) `lensMap` buttons

            h b = do
                q <- extendRef b listLens (False, ("", []))
                onChangeMemo (fst <$> readRef q) $ \bb -> return $ case bb of
                    False -> pure $ pure []
                    _ -> do
                        r <- h $ _2 . _2 `lensMap` q
                        pure $ ((_2 . _1 `lensMap` q) :) <$> join r

        r <- fmap join $ h $ _2 `lensMap` buttons

        let act i f = do
                xs <- readRef r
                when (length xs <= i) $ fail' "nootebook error"
                f $ xs !! i

        writeRef ctrl "a"
        buttons ==> ("", ["a"])
        act 0 $ \rr -> writeRef ctrl "a"
-}

    runTest "onChange + onChange + onRegionStatusChange" $ do
        a <- newRef True
        b <- newRef ()
        _ <- onChange (readRef a) $ \v -> case v of
            True -> do
                void $ onChange (readRef b) $ const $ onRegionStatusChange $ message_ . (++ "1") . show
                void $ onChangeEq (readRef b) $ const $ onRegionStatusChange $ message_ . (++ "2") . show
--                void $ onChangeEq_ (readRef b) $ const $ onRegionStatusChange $ message_ . (++ "3") . show
                void $ onChangeMemo (readRef b) $ const $ do
                    onRegionStatusChange $ message_ . (++ "4") . show
                    return $ onRegionStatusChange $ message_ . (++ "5") . show
            False -> return ()
        return $ do
            writeRef a False
            message' "Kill1"
            message' "Kill2"
            message' "Kill5"        -- TODO: later
            message' "Kill4"
--            message' "Kill3"

    runTest "issue1" $ do
        r <- newRef (0 :: Int)
        le <- onChangeEq (fmap (min 1) $ readRef r) $ \b -> do
            case b of
                0 -> return $ pure 0
                1 -> onChange (readRef r) return
                _ -> error "impossible"

        _ <- onChange (liftM2 (,) (readRef r) (join le)) $ message . show

        return $ do
            message' "(0,0)"
            send r 1
            message' "(1,1)"
            send r 2
            message' "(2,2)"

    runTest "issue2" $ do
        r <- newRef ()
        _ <- onChange (readRef r) $ \_ -> void $ extendRef r id ()
        return $ writeRef r ()

    runTest "issue3" $ do
        let
            undo (x: xs@(_:_), ys) = (xs, x: ys)
            undo _ = error "impossible"

            undoLens = lens get set where
                get = head . fst
                set (xs, _) x = (x : xs, [])
        list_ <- newRef True
        ku <- extendRef list_ undoLens ([], [])

        _ <- onChange (readRef list_) $ message . show

        return $ do
            message' "True"
            writeRef list_ False
            message' "False"
            modRef ku undo
            message' "True"

    runTest "issue4" $ do
        r <- newRef False
        b <- onChange (readRef r) $ \case
            False -> pure $ pure True
            True -> do
                r' <- onChange (readRef r) return
                onChange r' return

        void $ onChange (join b) $ message . show

        return $ do
            message' "True"
            writeRef r True
            message' "True"
            writeRef r False
            message' "True"

    runTest "issue5" $ do
        r <- newRef True
        w <- onChangeMemo (readRef r) $ \case
            True  -> fmap return $ onChange (readRef r) $ return . ("e" ++) . show
            False -> return $ return $ return "F"
        void $ onChange (join w) message
        return $ do
            message' "eTrue"
            writeRef r False
            message' "F"
            writeRef r True
            message' "eTrue"

    runTest "issue6" $ do
        r <- newRef True
        q <- onChangeMemo (readRef r) $ \case
            True -> return $ return $ return True
            False -> do
                v <- extendRef r id undefined
                return $ return $ readRef v
        void $ onChange (join q) $ message . show
        return $ do
            message' "True"
            writeRef r False
            message' "False"
            writeRef r True
            message' "True"
            writeRef r False
            message' "False"

    runTest "issue6b" $ do
        r <- newRef True
        void $ onChangeMemo (readRef r) $ \case
            True -> return $ return ()
            False -> do
                q <- extendRef r id undefined
                return $ readerToCreator (readRef q) >>= message . show
        return $ do
            writeRef r False
            message' "False"
            writeRef r True
            writeRef r False
            message' "False"

-------------------------- auxiliary definitions

bool :: a -> a -> Bool -> a
bool a _ True  = a
bool _ b False = b

maybeLens :: Lens' (Bool, a) (Maybe a)
maybeLens = lens (\(b,a) -> if b then Just a else Nothing)
              (\(_,a) -> maybe (False, a) (\a' -> (True, a')))

-- | Undo-redo state transformation.
undoTr
    :: (Reversible m)
    => (a -> a -> Bool)     -- ^ equality on state
    -> Ref m a             -- ^ reference of state
    -> RefCreator m (RefReader m (Maybe (RefWriter m ()))
           , RefReader m (Maybe (RefWriter m ()))
           )  -- ^ undo and redo actions
undoTr eq r = do
    ku <- extendRef r (undoLens eq) ([], [])
    let try f = fmap (fmap (writeRef ku) . f) $ readRef ku
    pure (try undo, try redo)
  where
    undo (x: xs@(_:_), ys) = Just (xs, x: ys)
    undo _ = Nothing

    redo (xs, y: ys) = Just (y: xs, ys)
    redo _ = Nothing

undoLens :: (a -> a -> Bool) -> Lens' ([a],[a]) a
undoLens eq = lens get set where
    get = head . fst
    set (x' : xs, ys) x | eq x x' = (x: xs, ys)
    set (xs, _) x = (x : xs, [])

--------------------------------------------------------------------------------

main :: IO ()
main = do
    exit <- newEmptyMVar
    runRefCreatorRev $ \runRefWriter -> do

        a <- newRef False
        b <- newRef False

        _ <- onChangeEq (liftM2 (,) (readRef a) (readRef b)) $ lift . print'

        lift $ void $ forkIO' $ fix $ \cycle -> do
            l <- getLine
            case l of
                "" -> putMVar exit ()
                "a" -> runRefWriter (modRef a not) >> cycle
                "b" -> runRefWriter (modRef b not) >> cycle
                _ -> putStrLn "wrong input" >> cycle

    void $ takeMVar exit



