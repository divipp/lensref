{-# LANGUAGE CPP #-}
module Data.LensRef
    ( -- * Monads
      RefReaderT            -- RefReader
    , RefCreatorT           -- RefCreator
    , RefWriterT            -- RefWriter
    , readerToWriter
    , readerToCreator
    , runRefCreatorT        -- runRefCreator

    -- * References
    , Ref
    , readRef
    , writeRef
    , modRef
    , joinRef
    , lensMap
    , unitRef
    , newRef

    -- * composed with register
    , memoRead
    , extendRef
    , onChange
    , onChangeEq
    , onChangeEq_
    , onChangeMemo

    -- * Other
    , currentValue
    , RegionStatusChange (..)
    , onRegionStatusChange

    -- * Simple references
    , SimpleRefClass (..)
    ) where

import Data.LensRef.Common
#ifdef __PURE__
import Data.LensRef.Pure
#else
import Data.LensRef.Fast
#endif

