{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# OPTIONS_HADDOCK prune #-}
module Data.LensRef
    (
    -- * Core
      module Data.LensRef.Class
    -- ** References
{-
      unitRef
    , lensMap
            -- TODO: elim these?
            , RefReaderSimple, RefClass --RefClass (..)
            , RefSimple
    , MonadRefReader (..)
    , MonadRefWriter (..)
    , RefOf
    , RefReaderOf
    , RefWriterOf

    -- ** Reference creation
    , MonadRefCreator (..)

    -- ** Other
    , MonadMemo (..)
-}
    , EqRefClass        --EqRefClass (..)
            , hasEffect
--    , EqRefSimple
    , EqRefOf
    , toEqRef
    , fromEqRef
    , newEqRef
{-
    , CorrRef
    , corrRef
    , fromCorrRef
    , correction
-}
    ) where

import Control.Applicative
import Control.Lens.Simple --(set)

import Data.LensRef.Class

--------------------------------

{- | Reference with inherent equivalence.

-}
class RefClass r => EqRefClass r where
    valueIsChanging :: RefSimple r a -> a -> RefReaderSimple r Bool

{- | @hasEffect r f@ returns @False@ iff @(modRef m f)@ === @(pure ())@.

@hasEffect@ is correct only if @toEqRef@ is applied on a pure reference (a reference which is a pure lens on the hidden state).

@hasEffect@ makes defining auto-sensitive buttons easier, for example.
-}
hasEffect
    :: EqRefClass r
    => RefSimple r a
    -> (a -> a)
    -> RefReaderSimple r Bool
hasEffect r f = readRef r >>= valueIsChanging r


-- | TODO
data EqRefCore r a = EqRefCore (r a) (a -> RefReaderSimple r Bool{-changed-})

{- | RefClasss with inherent equivalence.

@EqRefSimple r a@ === @RefReaderSimple r (exist b . Eq b => (Lens' b a, r b))@

As a reference, @(m :: EqRefSimple r a)@ behaves as

@join $ fmap (uncurry lensMap) m@
-}
type EqRefSimple r a = EqRefCore r a

-- | TODO
type EqRefOf m a = EqRefSimple (BaseRef m) a

{- | @EqRefSimple@ construction.
-}
toEqRef :: (RefClass r, Eq a) => RefSimple r a -> EqRefSimple r a
toEqRef r = EqRefCore r $ \x -> readRef r <&> (/= x)

-- | TODO
newEqRef :: (MonadRefCreator m, Eq a) => a -> m (EqRefOf m a) 
newEqRef = fmap toEqRef . newRef

{- | An @EqRefSimple@ is a normal reference if we forget about the equality.

@fromEqRef m@ === @join $ fmap (uncurry lensMap) m@
-}
fromEqRef :: RefClass r => EqRefSimple r a -> RefSimple r a
fromEqRef (EqRefCore r _) = r

instance RefClass r => EqRefClass (EqRefCore r) where
    valueIsChanging (EqRefCore _r k) = k

instance RefClass r => RefClass (EqRefCore r) where

    type (RefReaderSimple (EqRefCore r)) = RefReaderSimple r

    readRefSimple = readRef . fromEqRef

    writeRefSimple = writeRefSimple . fromEqRef

    lensMap l (EqRefCore r k)
        = EqRefCore (lensMap l r) $ \b -> readRef r >>= \a -> k $ set l b a

    unitRef = toEqRef unitRef

    joinRef mr = EqRefCore (joinRef $ mr <&> fromEqRef) $ \a -> mr >>= \(EqRefCore _ k) -> k a

data CorrBaseRef r a = CorrBaseRef (r a) (a -> RefReaderSimple r (Maybe a{-corrected-}))

type CorrRef r a = CorrBaseRef r a

instance RefClass r => RefClass (CorrBaseRef r) where

    type (RefReaderSimple (CorrBaseRef r)) = RefReaderSimple r

    readRefSimple = readRefSimple . fromCorrRef

    writeRefSimple = writeRefSimple . fromCorrRef

    lensMap l (CorrBaseRef r k)
        = CorrBaseRef (lensMap l r) $ \b -> do
            a <- readRef r
            fmap (fmap (^. l)) $ k $ set l b a

    unitRef = corrRef (const $ pure Nothing) unitRef

fromCorrRef :: RefClass r => CorrRef r a -> RefSimple r a
fromCorrRef (CorrBaseRef r _) = r

corrRef :: RefClass r => (a -> RefReaderSimple r (Maybe a)) -> RefSimple r a -> CorrRef r a
corrRef f r = CorrBaseRef r f

correction :: RefClass r => CorrRef r a -> a -> RefReaderSimple r (Maybe a)
correction (CorrBaseRef _ f) a = f a



