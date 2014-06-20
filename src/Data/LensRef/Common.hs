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

--type SRef (m :: * -> *) = IORef

class (Monad m, Applicative m) => NewRef m where

    -- simple reference
    type SRef m :: * -> *

    newRef'   :: a -> m (SRef m a)

    modRef'   :: SRef m a -> StateT a m b -> m b
    modRef' r s = do
        a <- readRef' r
        (x, a') <- runStateT s a
        writeRef' r a'
        return x

    readRef'  :: SRef m a -> m a
    readRef' r = modRef' r get

    writeRef' :: SRef m a -> a -> m ()
    writeRef' r a = modRef' r $ put a

-------------------

instance NewRef IO where
    type SRef IO = IORef

--    {-# INLINE newRef' #-}
    newRef' x = newIORef x
--    {-# INLINE readRef' #-}
    readRef' r = readIORef r
--    {-# INLINE writeRef' #-}
    writeRef' r a = writeIORef r a

-------------------

instance NewRef m => NewRef (ReaderT r m) where
    type SRef (ReaderT r m) = SRef m
    newRef' = lift . newRef'
    readRef' = lift . readRef'
    writeRef' r = lift . writeRef' r

-------------------

type NewRefT = StateT (Map.IntMap Any)

nextKey :: Map.IntMap a -> Int
nextKey = maybe 0 ((+1) . fst . fst) . Map.maxViewWithKey

data Any where Any :: a -> Any

newtype SRefProg a = SRefProg Int

instance (Monad m, Functor m) => NewRef (StateT (Map.IntMap Any) m) where
    type SRef (StateT (Map.IntMap Any) m) = SRefProg 
    newRef' a = do
        i <- gets nextKey
        let r = SRefProg i
        writeRef' r a
        return r

    readRef' (SRefProg i) = gets $ unsafeGetAny . (Map.! i)
      where
        unsafeGetAny :: Any -> a
        unsafeGetAny (Any a) = unsafeCoerce a

    writeRef' (SRefProg i) a = modify $ Map.insert i (Any a)

runNewRefT :: Monad m => NewRefT m a -> m a
runNewRefT = flip evalStateT mempty

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
memoRead_ :: MonadRefCreator m => (Ref m (Maybe a) -> Maybe a -> m ()) -> m a -> m (m a) 
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


