{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
-- | Minimalized lens dependency. Compatible with the lens package.
module Control.Lens.Simple
    ( module Lens
    , (<&>)
    , Field1 (..)
    , Field2 (..)
    , Field3 (..)
    ) where

import Control.Applicative

import Lens.Family2 as Lens
import Lens.Family2.State.Strict as Lens
import Lens.Family2.Unchecked as Lens

---------------------------------

infixl 1 <&>

{-# INLINE (<&>) #-}
(<&>) :: Functor f => f a -> (a -> b) -> f b
as <&> f = f <$> as

---------------------------------

class Field1 s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _1 :: Lens s t a b

instance Field1 (a,b) (a',b) a a' where
  _1 k ~(a,b) = k a <&> \a' -> (a',b)

instance Field1 (a,b,c) (a',b,c) a a' where
  _1 k ~(a,b,c) = k a <&> \a' -> (a',b,c)

instance Field1 (a,b,c,d) (a',b,c,d) a a' where
  _1 k ~(a,b,c,d) = k a <&> \a' -> (a',b,c,d)

class Field2 s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _2 :: Lens s t a b

instance Field2 (a,b) (a,b') b b' where
  _2 k ~(a,b) = k b <&> \b' -> (a,b')

instance Field2 (a,b,c) (a,b',c) b b' where
  _2 k ~(a,b,c) = k b <&> \b' -> (a,b',c)

instance Field2 (a,b,c,d) (a,b',c,d) b b' where
  _2 k ~(a,b,c,d) = k b <&> \b' -> (a,b',c,d)

class Field3 s t a b | s -> a, t -> b, s b -> t, t a -> s where
    _3 :: Lens s t a b

instance Field3 (a,b,c) (a,b,c') c c' where
  _3 k ~(a,b,c) = k c <&> \c' -> (a,b,c')

