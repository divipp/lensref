{-# LANGUAGE CPP #-}
module Data.LensRef
    ( -- * Monads
      RefReader            -- RefReader
    , RefCreator           -- RefCreator
    , RefWriter            -- RefWriter
    , readerToWriter
    , readerToCreator
    , runRefCreator        -- runRefCreator

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
    , onRegionStatusChange_

    -- * Reference context
    , RefContext (..)
    , modSimpleRef
    ) where

import Data.LensRef.Context
#ifdef __PURE__
import Data.LensRef.Pure
#else
import Data.LensRef.Fast
#endif

