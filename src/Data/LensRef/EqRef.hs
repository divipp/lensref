{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Data.LensRef.EqRef
    ( module Data.LensRef
    , RefClass (..)
    , readRef
    , writeRef
    , modRef
    , EqRef
    , toEqRef
    , changing
    ) where

import Control.Applicative
import Lens.Family2

import Data.LensRef hiding (readRef, writeRef, lensMap, modRef, joinRef)
import qualified Data.LensRef as Ref

--------------------------------------------------------------------------------

class RefClass r where
    toRef    :: RefContext s => r s a -> Ref s a
    lensMap  :: RefContext s => Lens' a b -> r s a -> r s b
    joinRef  :: RefContext s => RefReader s (r s a) -> r s a

infixr 8 `lensMap`

readRef :: (RefClass r, RefContext m) => r m a -> RefReader m a
readRef  = Ref.readRef  . toRef

writeRef :: (RefClass r, RefContext m) => r m a -> a -> RefWriter m ()
writeRef = Ref.writeRef . toRef

modRef :: (RefClass r, RefContext m) => r m a -> (a -> a) -> RefWriter m ()
modRef   = Ref.modRef   . toRef

instance RefClass Ref where
    toRef   = id
    lensMap = Ref.lensMap
    joinRef = Ref.joinRef

--------------------------------------------------------------------------------

data EqRef s a = EqRef
    { refOfEqRef :: Ref s a
    , changing   :: a -> RefReader s Bool
    }

instance RefClass EqRef where
    toRef = refOfEqRef
    lensMap k (EqRef r c) = EqRef (lensMap k r) $ \b -> readRef r >>= c . set k b
    joinRef m = EqRef (joinRef $ toRef <$> m) $ \a -> m >>= flip changing a

toEqRef :: (Eq a, RefContext s) => Ref s a -> EqRef s a
toEqRef r = EqRef r $ \x -> (/= x) <$> readRef r

