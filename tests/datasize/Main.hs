{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}

module Main where

import Control.DeepSeq
import GHC.DataSize
import GHC.Generics
import Data.Rawr
import Test.Tasty
import Test.Tasty.HUnit

data Id a = Id a deriving (Generic, NFData)

main :: IO ()
main = defaultMain $ testGroup "ghc-datasize"
    [ testCase "R0" $ do
        s <- recursiveSize $!! ()
        s' <- recursiveSize $!! R ()
        s @?= s'
    , testCase "R1" $ do
        s <- recursiveSize $!! Id True
        s' <- recursiveSize $!! R ( #a := True )
        s @?= s'
    , testCase "R2" $ do
        let a = 1 :: Int
        s <- recursiveSize $!! (a, True)
        s' <- recursiveSize $!! R ( #a := a, #b := True )
        s @?= s'
    , testCase "R3" $ do
        let a = 1 :: Int
            c = "Hello world"
        s <- recursiveSize $!! (a, True, c)
        s' <- recursiveSize $!! R ( #a := a, #b := True, #c := c )
        s @?= s'
    ]
