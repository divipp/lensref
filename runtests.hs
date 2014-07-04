{-# LANGUAGE CPP #-}
module Main where

#ifndef __TESTS__
main :: IO ()
main = fail "enable the tests flag like \'cabal configure --enable-tests -ftests; cabal build; cabal test\'"
#else
import Data.LensRef.Test

main :: IO ()
main = runTests
#endif

