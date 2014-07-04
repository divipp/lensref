{-# LANGUAGE CPP #-}
module Data.LensRef
    (
    -- * Core
      module Ref
    , SimpleRefClass
    ) where

import Data.LensRef.Common
#ifdef __PURE__
import Data.LensRef.Pure as Ref
#else
import Data.LensRef.Fast as Ref
#endif

