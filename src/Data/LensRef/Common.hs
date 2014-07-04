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
import Control.Monad.State.Strict
import Control.Monad.Reader

import Unsafe.Coerce

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
    type SimpleRef m :: * -> *

    newSimpleRef   :: a -> m (SimpleRef m a)
    readSimpleRef  :: SimpleRef m a -> m a
    writeSimpleRef :: SimpleRef m a -> a -> m ()

modSimpleRef :: SimpleRefClass m => SimpleRef m a -> StateT a m b -> m b
modSimpleRef r s = do
    a <- readSimpleRef r
    (x, a') <- runStateT s a
    writeSimpleRef r a'
    return x

-------------------

instance SimpleRefClass IO where
    type SimpleRef IO = IORef

--    {-# INLINE newSimpleRef #-}
    newSimpleRef x = newIORef x
--    {-# INLINE readSimpleRef #-}
    readSimpleRef r = readIORef r
--    {-# INLINE writeSimpleRef #-}
    writeSimpleRef r a = writeIORef r a

-------------------

instance SimpleRefClass m => SimpleRefClass (ReaderT r m) where
    type SimpleRef (ReaderT r m) = SimpleRef m
    newSimpleRef = lift . newSimpleRef
    readSimpleRef = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

-------------------

-- TODO: wrap in newtype
type SimpleRefT = StateT (Map.IntMap Any)

nextKey :: Map.IntMap a -> Int
nextKey = maybe 0 ((+1) . fst . fst) . Map.maxViewWithKey

data Any where Any :: a -> Any

newtype RefSimpleRefT a = RefSimpleRefT Int

instance (Monad m, Functor m) => SimpleRefClass (SimpleRefT m) where
    type SimpleRef (SimpleRefT m) = RefSimpleRefT 
    newSimpleRef a = do
        i <- gets nextKey
        let r = RefSimpleRefT i
        writeSimpleRef r a
        return r

    readSimpleRef (RefSimpleRefT i) = gets $ unsafeGetAny . (Map.! i)
      where
        unsafeGetAny :: Any -> a
        unsafeGetAny (Any a) = unsafeCoerce a

    writeSimpleRef (RefSimpleRefT i) a = modify $ Map.insert i (Any a)

runSimpleRefT :: Monad m => SimpleRefT m a -> m a
runSimpleRefT = flip evalStateT mempty

