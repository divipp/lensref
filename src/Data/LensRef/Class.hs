{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# OPTIONS_HADDOCK prune #-}
--{-# OPTIONS_HADDOCK not-home #-}
-- | Core lensref interface
module Data.LensRef.Class
    (
    -- * References
      RefClass (..)
    , RefSimple
    , RefWriterOf_
    , RefWriterSimple

    , MonadRefReader (..)
    , MonadRefWriter (..)
    , RefOf
    , RefReaderOf
    , RefWriterOf

    -- * Reference creation
    , MonadRefCreator (..)
    , RegionStatusChange (..)
    , RegionStatusChangeHandler

    -- * Other
    , MonadMemo (..)
    , MonadEffect (..)

    , RefHandler_
    , RefAction (..)
    ) where


import Control.Applicative
import Control.Monad.Reader
--import Control.Monad.Writer
import Control.Monad.Trans.Control
import Control.Lens.Simple --(Lens', united)

--------------------------------


{- |
Type class for references which can be joined and on which lenses can be applied.
-}
class ( MonadRefReader (RefReaderSimple r)
      , MonadRefWriter (RefWriterSimple r)
      , RefReaderOf (RefReaderSimple r) ~ RefReaderSimple r
      )
    => RefClass r where

    {- | unit reference
    -}
    unitRef :: RefSimple r ()

    {- | Apply a lens on a reference.
    -}
    lensMap :: Lens' a b -> RefSimple r a -> RefSimple r b
{-
    -- proposed by Michael Sloan (experimental)
    traversalMap :: (Monoid b) => Traversal' a b -> RefSimple r a -> RefSimple r b
-}
    {- | Associated reference reader monad.

    @(RefReaderSimple m)@ is ismoroprhic to @('Reader' x)@ for some @x@.
    Laws which ensures this isomorphism (@(r :: RefReaderSimple m a)@ is arbitrary):

    prop> r >> pure ()  =  pure ()
    prop> liftA2 (,) r r  =  fmap (\a -> (a, a)) r

    See also <http://stackoverflow.com/questions/16123588/what-is-this-special-functor-structure-called>
    -}
    type RefReaderSimple r :: * -> *

    {- | Reference read.
    -}
    readRefSimple  :: RefSimple r a -> RefReaderSimple r a

    {- | Reference writeRef.
    -}
    writeRefSimple :: RefSimple r a -> a -> RefWriterSimple r ()

    joinRef :: RefReaderSimple r (RefSimple r a) -> RefSimple r a

data family RefWriterOf_ (m :: * -> *) :: * -> *

{- |
There are two associated types of a reference, 'RefReaderSimple' and 'RefWriterSimple' which determines each-other.
This is implemented by putting only 'RefReaderSimple' into the 'RefClass' class and
adding a @RefWriterOf_@ data family outside of 'RefClass'.

@RefWriterOf_@ is hidden from the documentation because you never need it explicitly.
-}
type RefWriterSimple m = RefWriterOf_ (RefReaderSimple m)

-- | Reference wrapped into a RefReaderSimple monad. See the documentation of 'RefClass'.
type RefSimple (r :: * -> *) = r

infixr 8 `lensMap`

-- | TODO
class ( Applicative m, Monad m
      , BaseRef (RefWriterOf m) ~ BaseRef m
      )
    => MonadRefReader m where

    -- | Base reference associated to the reference reader monad
    type BaseRef m :: * -> *

    liftRefReader :: RefReaderOf m a -> m a

    {- | @readRef@ === @liftRefReader . readRefSimple@
    -}
    readRef :: (RefClass r, RefReaderOf m ~ RefReaderSimple r) => RefSimple r a -> m a
    readRef = liftRefReader . readRefSimple


-- | TODO
type RefReaderOf m = RefReaderSimple (BaseRef m)

-- | TODO
type RefWriterOf m = RefWriterSimple (BaseRef m)

-- | TODO
type RefOf m a = RefSimple (BaseRef m) a



-- | TODO
class ( MonadRefReader m
      )
    => MonadRefWriter m where

    liftRefWriter :: RefWriterOf m a -> m a

    {- | @writeRef r@ === @liftRefWriter . writeRefSimple r@
    -}
    writeRef :: (RefClass r, RefReaderSimple r ~ RefReaderOf m) => RefSimple r a -> a -> m ()
    writeRef r = liftRefWriter . writeRefSimple r

    -- | @modRef r f@ === @readRef r >>= writeRef r . f@
    modRef :: (RefClass r, RefReaderSimple r ~ RefReaderOf m) => RefSimple r a -> (a -> a) -> m ()
    r `modRef` f = readRef r >>= writeRef r . f


type RefHandler_ m a =
        forall f
        .  (RefAction f, RefCreatorOf f ~ m)
        => (a -> RefActionFunctor f a)
        -> f ()

class ( Functor (RefActionFunctor f)
      , MonadRefCreator (RefCreatorOf f)
      )
    => RefAction (f :: * -> *) where

    type RefActionFunctor f :: * -> *
    type RefCreatorOf f :: * -> *

    buildRefAction
        :: (a -> RefActionFunctor f a)
        -> RefReaderOf (RefCreatorOf f) a
        -> ((a -> a) -> RefWriterOf (RefCreatorOf f) ())
        -> RefRegOf (RefCreatorOf f) a
        -> f ()

    joinRefAction :: RefReaderOf (RefCreatorOf f) (f ()) -> f ()


{- | Monad for reference creation. Reference creation is not a method
of the 'RefClass' type class to make possible to
create the same type of references in multiple monads.

For basic usage examples, look into the source of @Data.LensRef.Test@.
-}
class ( RefClass (BaseRef m)
      , MonadRefReader m
      , MonadMemo m
      , MonadEffect m
      , MonadEffect (RefWriterOf m)
      , EffectM (RefWriterOf m) ~ EffectM m
      )
    => MonadRefCreator m where

    type RefRegOf m a :: *

    {- | Reference creation by extending the state of an existing reference.

    Suppose that @r@ is a reference and @k@ is a lens.

    Law 1: @extendRef@ applies @k@ on @r@ backwards, i.e. 
    the result of @(extendRef r k a0)@ should behaves exactly as @(lensMap k r)@.

    prop> (fmap (k .) $ extendRef r k a0)  =  pure r

    Law 2: @extendRef@ does not change the value of @r@:

    prop> (extendRef r k a0 >> readRef r)  =  readRef r

    Law 3: Proper initialization of newly defined reference with @a0@:

    prop> (extendRef r k a0 >>= readRef)  =  (readRef r >>= set k a0)
    -}
    extendRef :: RefOf m b -> Lens' a b -> a -> m (RefOf m a)

    {- | @newRef@ extends the state @s@ in an independent way.

    @newRef@ === @extendRef unitRef united@
    -}
    newRef :: a -> m (RefOf m a)
    --newRef = extendRef unitRef united

    onChange :: RefReaderOf m a -> (a -> m b) -> m (RefReaderOf m b)

    onChangeEq_ :: Eq a => RefReaderOf m a -> (a -> m b) -> m (RefOf m b)
    -- onChangeEq r f = onChangeMemo r $ pure . f

    onChangeEq :: Eq a => RefReaderOf m a -> (a -> m b) -> m (RefReaderOf m b)
    onChangeEq r f = fmap readRef $ onChangeEq_ r f

    onChangeMemo :: Eq a => RefReaderOf m a -> (a -> m (m b)) -> m (RefReaderOf m b)

    onRegionStatusChange :: RegionStatusChangeHandler (EffectM m) -> m ()


-- | TODO
class (Monad m, Applicative m) => MonadMemo m where
    {- | Lazy monadic evaluation.
    In case of @y <- memoRead x@, invoking @y@ will invoke @x@ at most once.

    Laws:

     *  @(memoRead x >> pure ())@ === @pure ()@

     *  @(memoRead x >>= id)@ === @x@

     *  @(memoRead x >>= \y -> liftA2 (,) y y)@ === @fmap (\a -> (a, a)) y@

     *  @(memoRead x >>= \y -> liftA3 (,) y y y)@ === @fmap (\a -> (a, a, a)) y@

     *  ...
    -}
    memoRead :: m a -> m (m a)
{-
    memoWrite :: Eq b => (b -> m a) -> m (b -> m a)

    future :: (RefReaderOf m a -> m a) -> m a
-}

-- | TODO
class ( Monad m, Applicative m
      , Monad (EffectM m), Applicative (EffectM m)
      )
    => MonadEffect m where

    type EffectM m :: * -> *

    liftEffectM :: EffectM m a -> m a


-- | TODO
data RegionStatusChange = Kill | Block | Unblock deriving (Eq, Ord, Show)

-- | TODO
type RegionStatusChangeHandler m = RegionStatusChange -> m ()


---------------------

instance (MonadRefReader m) => MonadRefReader (ReaderT w m) where
    type BaseRef (ReaderT w m) = BaseRef m
    liftRefReader = lift . liftRefReader

instance MonadRefCreator m => MonadRefCreator (ReaderT w m) where
    extendRef r l       = lift . extendRef r l
    newRef           = lift . newRef
    onChange r f     = ReaderT $ \st -> onChange r $ fmap (flip runReaderT st) f
    onChangeEq r f   = ReaderT $ \st -> onChangeEq r $ fmap (flip runReaderT st) f
    onChangeEq_ r f  = ReaderT $ \st -> onChangeEq_ r $ fmap (flip runReaderT st) f
    onChangeMemo r f = ReaderT $ \st -> onChangeMemo r $ fmap (fmap (flip runReaderT st) . flip runReaderT st) f
    onRegionStatusChange = lift . onRegionStatusChange

instance (MonadMemo m) => MonadMemo (ReaderT w m) where
    memoRead m = liftWith $ \unlift -> fmap restoreT $ memoRead $ unlift m

instance (MonadEffect m) => MonadEffect (ReaderT w m) where
    type EffectM (ReaderT w m) = EffectM m
    liftEffectM = lift . liftEffectM






