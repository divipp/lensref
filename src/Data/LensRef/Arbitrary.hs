{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGe TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module Data.LensRef.Arbitrary where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Operational
import Test.QuickCheck

import Data.LensRef.Class
import Data.LensRef.TestEnv
import qualified Data.LensRef.Pure as Pure
import qualified Data.LensRef.Fast as Fast

--------------------------------

data RegisterI a where
    OnChange :: Eq a => ARefReader a -> (a -> ARegister b) -> RegisterI (ARefReader b)

type ARegister = Program RegisterI

data RefReaderI a where
    X :: RefReaderI ()

type ARefReader = Program RefReaderI

---------------------------------

instance Show (ARegister a) where

---------------------------------

instance Arbitrary (ARefReader Bool) where

instance Arbitrary (ARegister ()) where
    arbitrary = oneof
        [ fmap return arbitrary
        ]

instance Arbitrary (ARegister Bool) where
    arbitrary = oneof
        [ fmap return arbitrary
        ]

instance Arbitrary (ARegister (ARefReader Bool)) where
    arbitrary = oneof
        [ fmap return arbitrary
        , liftA2 (\r f -> singleton $ OnChange (r :: ARefReader Bool) f) arbitrary arbitrary
        ]

toPure :: ARegister a -> Pure.RefCreatorT Identity a
toPure = undefined

toFast :: ARegister a -> Fast.RefCreatorT Identity a
toFast = undefined

similar :: Pure.RefCreatorT Identity a -> Fast.RefCreatorT Identity a -> Bool
similar = undefined

prop :: ARegister () -> Bool
prop m = similar (toPure m) (toFast m)

test = quickCheck prop


