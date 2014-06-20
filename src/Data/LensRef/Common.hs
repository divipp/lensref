{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
module Data.LensRef.Common where

import Data.Monoid hiding (Any)
import Data.IORef
import qualified Data.IntMap as Map
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import Unsafe.Coerce

import Data.LensRef.Class

-------------

newtype MonadMonoid m a = MonadMonoid
    { runMonadMonoid :: m a }
        deriving (Monad, Applicative, Functor)

instance MonadTrans MonadMonoid where
    lift = MonadMonoid

-- Applicative would be enough
instance (Monad m, Monoid a) => Monoid (MonadMonoid m a) where
    mempty = MonadMonoid $ return mempty
    MonadMonoid a `mappend` MonadMonoid b = MonadMonoid $ liftM2 mappend a b

------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge [] xs = xs
merge xs [] = xs
merge (x:xs) (y:ys) = case compare x y of
    LT -> x: merge xs (y:ys)
    GT -> y: merge (x:xs) ys
    EQ -> x: merge xs ys

mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy _ [] xs = xs
mergeBy _ xs [] = xs
mergeBy p (x:xs) (y:ys) = case p x y of
    LT -> x: mergeBy p xs (y:ys)
    GT -> y: mergeBy p (x:xs) ys
    EQ -> x: mergeBy p xs ys

----------------

class (Monad m, Applicative m) => SimpleRefClass m where

    -- simple reference
    type SimpleRefOf m :: * -> *

    newSimpleRef   :: a -> m (SimpleRefOf m a)
    readSimpleRef  :: SimpleRefOf m a -> m a
    writeSimpleRef :: SimpleRefOf m a -> a -> m ()

modSimpleRef :: SimpleRefClass m => SimpleRefOf m a -> StateT a m b -> m b
modSimpleRef r s = do
    a <- readSimpleRef r
    (x, a') <- runStateT s a
    writeSimpleRef r a'
    return x

-------------------

instance SimpleRefClass IO where
    type SimpleRefOf IO = IORef

--    {-# INLINE newSimpleRef #-}
    newSimpleRef x = newIORef x
--    {-# INLINE readSimpleRef #-}
    readSimpleRef r = readIORef r
--    {-# INLINE writeSimpleRef #-}
    writeSimpleRef r a = writeIORef r a

-------------------

instance SimpleRefClass m => SimpleRefClass (ReaderT r m) where
    type SimpleRefOf (ReaderT r m) = SimpleRefOf m
    newSimpleRef = lift . newSimpleRef
    readSimpleRef = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

-------------------

-- TODO: wrap in newtype
type SimpleRefT = StateT (Map.IntMap Any)

nextKey :: Map.IntMap a -> Int
nextKey = maybe 0 ((+1) . fst . fst) . Map.maxViewWithKey

data Any where Any :: a -> Any

newtype RefOfSimpleRefT a = RefOfSimpleRefT Int

instance (Monad m, Functor m) => SimpleRefClass (SimpleRefT m) where
    type SimpleRefOf (SimpleRefT m) = RefOfSimpleRefT 
    newSimpleRef a = do
        i <- gets nextKey
        let r = RefOfSimpleRefT i
        writeSimpleRef r a
        return r

    readSimpleRef (RefOfSimpleRefT i) = gets $ unsafeGetAny . (Map.! i)
      where
        unsafeGetAny :: Any -> a
        unsafeGetAny (Any a) = unsafeCoerce a

    writeSimpleRef (RefOfSimpleRefT i) a = modify $ Map.insert i (Any a)

runSimpleRefT :: Monad m => SimpleRefT m a -> m a
runSimpleRefT = flip evalStateT mempty

---------------------------

{-
    memoWrite = memoWrite_

    future = future_

future_ :: (MonadRefCreator m, MonadRefWriter m) => (RefReaderOf m a -> m a) -> m a
future_ f = do
    s <- newRef $ error "can't see the future"
    a <- f $ readRef s
    writeRef s a
    pure a
-}
memoRead_ :: MonadRefCreator m => (RefOf m (Maybe a) -> Maybe a -> m ()) -> m a -> m (m a) 
memoRead_ writeRef g = do
    s <- newRef Nothing
    pure $ readRef s >>= \x -> case x of
        Just a -> pure a
        _ -> g >>= \a -> do
            writeRef s $ Just a
            pure a

{-
memoWrite_ g = do
    s <- newRef Nothing
    pure $ \b -> readRef s >>= \x -> case x of
        Just (b', a) | b' == b -> pure a
        _ -> g b >>= \a -> do
            writeRef s $ Just (b, a)
            pure a
-}


