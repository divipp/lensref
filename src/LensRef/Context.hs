{-# LANGUAGE TypeFamilies #-}
module LensRef.Context where

import Data.IORef
import Data.STRef
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.ST

---------------------------------

infixl 1 <&>

{-# INLINE (<&>) #-}
(<&>) :: Functor f => f a -> (a -> b) -> f b
as <&> f = f <$> as

----------------

class (Monad m, Applicative m) => RefContext m where

    -- simple reference
    type SimpleRef m :: * -> *

    newSimpleRef   :: a -> m (SimpleRef m a)
    readSimpleRef  :: SimpleRef m a -> m a
    writeSimpleRef :: SimpleRef m a -> a -> m ()

modSimpleRef :: RefContext m => SimpleRef m a -> StateT a m b -> m b
modSimpleRef r s = do
    a <- readSimpleRef r
    (x, a') <- runStateT s a
    writeSimpleRef r a'
    return x

-------------------

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
    newSimpleRef = newSTRef
    readSimpleRef = readSTRef
    writeSimpleRef = writeSTRef

instance RefContext m => RefContext (ReaderT r m) where
    type SimpleRef (ReaderT r m) = SimpleRef m
    newSimpleRef = lift . newSimpleRef
    readSimpleRef = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

instance (RefContext m, Monoid w) => RefContext (WriterT w m) where
    type SimpleRef (WriterT w m) = SimpleRef m
    newSimpleRef = lift . newSimpleRef
    readSimpleRef = lift . readSimpleRef
    writeSimpleRef r = lift . writeSimpleRef r

