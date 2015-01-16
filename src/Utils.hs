{-# LANGUAGE NoMonomorphismRestriction #-}
--{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
module Utils
    ( Monad'
    , (<&>)
    , MonadTrace (..), TraceT, runTraceT
    , Reversible (..), ReversibleT, postponed, reversible, neut, runRev, orElse
    , SimpleRefs (..), modSimpleRef, memoRead
    , RefContext
    , Exc, when', assert_, assert
    , IsSeq (..), S.Seq, FakeSeq
    , Time, prevTime, nextTime
    ) where

import Data.Monoid
import Data.IORef
import Data.STRef
import qualified Data.Sequence as S
import Control.Applicative
import Control.Arrow
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.ST
import Lens.Family2 (Lens')

-------------------------------------------------------------------------------- Monad - Applicative (eliminate later)

type Monad' m = (Monad m, Applicative m)

-------------------------------------------------------------------------------- misc aux

infixl 1 <&>
(<&>) = flip (<$>)

-------------------------------------------------------------------------------- exceptions

type Exc = ExceptT String

assert :: Monad m => String -> Exc m b -> m b
assert msg m = runExceptT m >>= \case
    Left er  -> error $ msg ++ ": " ++ er
    Right x -> return x

assert_ :: String -> Bool -> a -> a
assert_ _ True x = x
assert_ msg False _ = error $ "assert: " ++ msg

when' :: (Monad m, Monoid a) => Bool -> m a -> m a
when' b m = if b then m else return mempty

-------------------------------------------------------------------------------- tracing

-- TODO: fancier tracing (indentation, tracing levels)
class Monad' m => MonadTrace m where
    traceM :: String -> m ()

instance MonadTrace m => MonadTrace (ReaderT r m) where
    traceM = lift . traceM

instance MonadTrace m => MonadTrace (StateT s m) where
    traceM = lift . traceM

instance (MonadTrace m, Monoid w) => MonadTrace (WriterT w m) where
    traceM = lift . traceM

instance (MonadTrace m) => MonadTrace (ExceptT e m) where
    traceM = lift . traceM

instance MonadTrace (ST s) where
    traceM _ = return ()

-- TODO: replace with dummy instance; use TraceT instead
instance MonadTrace IO where
    traceM = putStrLn
--    traceM _ = return ()

-------------------

newtype TraceT m a = TraceT { unTraceT :: WriterT [String] m a }
    deriving (Functor, Applicative, Monad, MonadFix)

instance MonadTrans TraceT where
    lift = TraceT . lift

instance Monad' m => MonadTrace (TraceT m) where
    traceM = TraceT . tell . (:[])

runTraceT :: Monad m => TraceT m a -> m (a, [String])
runTraceT (TraceT m) = runWriterT m


-------------------------------------------------------------------------------- Reversible monads

class Monad' m => Reversible m where
    -- Left: restore state & continue, Right: keep state & return
    restore :: m (Either (m a) a) -> m a

instance Reversible Identity where
    restore m = Identity $ runIdentity ||| id $ runIdentity m

instance Reversible m => Reversible (ReaderT r m) where
    restore m = ReaderT $ \r -> restore $ runReaderT m r <&> (flip runReaderT r +++ id)

instance (Reversible m, Monoid e) => Reversible (WriterT e m) where
    restore m = WriterT $ restore $ runWriterT m <&> \(a, e) -> runWriterT +++ flip (,) e  $ a

instance Reversible m => Reversible (StateT st m) where
    restore m = StateT $ \st -> restore $ runStateT m st <&> \(a, st') -> flip runStateT st +++ flip (,) st' $ a

instance Reversible m => Reversible (TraceT m) where
    restore m = TraceT $ restore $ unTraceT m <&> (unTraceT +++ id)

-- dummy instance
instance Reversible IO where
    restore m = m <&> either (const $ error "cannot reverse IO operation") id

-- dummy instance
instance Reversible (ST s) where
    restore m = m <&> either (const $ error "cannot reverse ST operation") id

-- Just, if at least one is Just (also when the other is error)
-- Nothing, if all is Nothing
-- error otherwise
orElse :: (Reversible m, MonadTrace m) => String -> Exc m (Maybe a) -> Exc m (Maybe a) -> Exc m (Maybe a)
orElse msg m1 m2 = ExceptT $ restore $ runExceptT m1 <&> \case
    Right (Just a) -> {-trace "     ok" $ -} Right $ Right $ Just a
    Right Nothing -> Left $ traceM ("     <- " ++ msg) >> runExceptT m2
    Left e -> Left $ traceM ("     <----- bt " ++ msg ++ " because " ++ e) >> runExceptT m2 <&> \case
        Right Nothing -> Left e
        x -> x

-------------------------------------------------------------------------------- Reversible monad transformer

newtype ReversibleT m a = ReversibleT (ReaderT Bool (WriterT (MM m, Dual (MM m)) m) a)
    deriving (Functor, Applicative, Monad, MonadFix)

-- TODO: replace this with reversed trace
instance (MonadTrace m) => MonadTrace (ReversibleT m) where
    traceM = ReversibleT . traceM

runRev :: Monad m => ReversibleT m a -> m a
runRev (ReversibleT m) = liftM fst $ runWriterT $ flip runReaderT False m

neut :: Monad m => m a -> ReversibleT m a
neut = ReversibleT . lift . lift

postponed :: Monad m => m () -> ReversibleT m ()
postponed m = ReversibleT $ do
    b <- ask
    if b then tell (MM m, mempty)
         else lift $ lift m

reversible :: Monad m => m (a, m ()) -> ReversibleT m a
reversible m = ReversibleT $ do
    (a, r) <- lift $ lift m
    b <- ask
    when b $ tell (mempty, Dual $ MM r)
    return a

instance Monad' m => Reversible (ReversibleT m) where
    restore (ReversibleT m) = ReversibleT $ do
        (e, (post, rev)) <- lift $ lift $ runWriterT $ flip runReaderT True m
        b <- ask
        case e of
            Left (ReversibleT m') -> do
                if b then tell (mempty, rev) else lift $ lift $ getMM $ getDual rev
                m'
            Right a -> do
                if b then tell (post, mempty) else lift $ lift $ getMM post
                return a

------------

newtype MM m = MM { getMM :: m () }

instance Monad m => Monoid (MM m) where
    mempty = MM $ return ()
    MM a `mappend` MM b = MM $ a >> b

-------------------------------------------------------------------------------- simple references

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

instance (SimpleRefs m) => SimpleRefs (TraceT m) where
    type SimpleRef (TraceT m) = SimpleRef m
    newSimpleRef     = lift . newSimpleRef
    readSimpleRef    = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

instance SimpleRefs m => SimpleRefs (ReversibleT m) where
    type SimpleRef (ReversibleT m) = SimpleRef m
    newSimpleRef a = neut $ newSimpleRef a
    readSimpleRef r = neut $ readSimpleRef r
    writeSimpleRef r a = reversible $ readSimpleRef r >>= \v -> writeSimpleRef r a >> return ((), writeSimpleRef r v)

modSimpleRef :: SimpleRefs m => SimpleRef m a -> (a -> m (a, b)) -> m b
modSimpleRef x f = do
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

-------------------------------------------------------------------------------- RefContext -- TODO: eliminate?

type RefContext m = (SimpleRefs m, Reversible m, MonadFix m, MonadTrace m)

-------------------------------------------------------------------------------- discrete time

newtype Time = Time Int
    deriving (Eq, Ord, Show)

instance Monoid Time where
    mempty = Time 0
    mappend = max

nextTime :: Time -> Time
nextTime (Time x) = Time (x + 1)

prevTime (Time 0) = error "before 0"
prevTime (Time x) = Time (x - 1)

-------------------------------------------------------------------------------- sequences

class IsSeq c where
    toList' :: c a -> [a]
    length' :: c a -> Int
    last'   :: c a -> a
    snoc'   :: c a -> a -> c a
    singleton :: a -> c a
    -- may fail
    at'     :: Int -> Lens' (c a) a

instance IsSeq S.Seq where
    toList' x = case S.viewl x of
        a S.:< x -> a: toList' x
        _ -> []
    length' = S.length
    last' (S.viewr -> _ S.:> x) = x
    last' _ = error "impossible"
    snoc'   = (S.|>)
    singleton = S.singleton
    at' i tr m = tr (S.index m i) <&> \x -> S.update i x m

data FakeSeq a = FakeSeq {len :: Int, elemm :: a}

instance IsSeq FakeSeq where
    toList' = (:[]) . elemm
    length' = len
    last' = elemm
    snoc' (FakeSeq n _) x = FakeSeq (n+1) x
    singleton = FakeSeq 1
    at' i tr ~FakeSeq{..} = assert_ (show (len-1, i)) (i == len-1) (tr elemm) <&> \elemm -> FakeSeq{..}


