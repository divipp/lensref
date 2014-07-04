{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
-- | Minimalized lens dependency. Compatible with the lens package.
module Control.Lens.Simple where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

----------- type synonyms

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a

type LensLike f s t a b = (a -> f b) -> s -> f t
type LensLike' f s a = LensLike f s s a a

type Traversal s t a b = forall f. Applicative f => (a -> f b) -> s -> f t
type Traversal' s a = Traversal s s a a

type Getting r s a = (a -> Const r a) -> s -> Const r s

type Setting p s t a b = p a (Identity b) -> s -> Identity t

type ASetter s t a b = (a -> Identity b) -> s -> Identity t

------------ setter

{-# INLINE set #-}
set :: ASetter s t a b -> b -> s -> t
set l b = runIdentity . l (\_ -> Identity b)

{-# INLINE over #-}
over :: (p ~ (->)) => Setting p s t a b -> p a b -> s -> t
over l f = runIdentity . l (Identity . f)

infixr 4 %~

{-# INLINE (%~) #-}
(%~) :: (p ~ (->)) => Setting p s t a b -> p a b -> s -> t
(%~) = over

------------- getter

{-# INLINE to #-}
to :: (s -> a) -> Getting r s a
to f g s = Const $ getConst $ g $ f s

infixl 8 ^.

{-# INLINE (^.) #-}
(^.) :: s -> Getting a s a -> a
a ^. l = getConst $ l Const a

------------- lens

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt afb s = sbt s <$> afb (sa s)

united :: Lens' a ()
united f v = fmap (\() -> v) $ f ()


------------------------- State

{-# INLINE use #-}
use :: MonadState s m => Getting a s a -> m a
use l = gets (view l)

infix 4 %=

{-# INLINE (%=) #-}
(%=) :: (p ~ (->), MonadState s m) => Setting p s s a b -> p a b -> m ()
l %= f = modify (l %~ f)

{-# INLINE (.=) #-}
(.=) :: MonadState s m => ASetter s s a b -> b -> m ()
l .= a = modify $ set l a

zoom :: Monad m => Lens' s t -> StateT t m a -> StateT s m a
--zoom :: Monad m => Lens' s t -> ReaderT t m a -> ReaderT s m a
zoom l (StateT m) = StateT $ \s -> liftM (over _2 $ \t -> set l t s) $ m $ s ^. l
--zoom l (ReaderT m) = ReaderT (zoom l . m)

--------------------------- Reader

infixr 2 `zoom`, `magnify`

{-# INLINE magnify #-}
magnify :: Monad m => Lens' a b -> ReaderT b m c -> ReaderT a m c
magnify l (ReaderT f) = ReaderT $ \a -> f $ a ^. l

--instance Zoom m n s t => Zoom (ReaderT e m) (ReaderT e n) s t where

{-# INLINE view #-}
view :: MonadReader s m => Getting a s a -> m a
view l = asks (^. l)

----------------------

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

