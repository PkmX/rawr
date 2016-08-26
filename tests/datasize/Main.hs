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
        s <- rsize $!! ()
        s' <- rsize $!! R ()
        s @?= s'
    , testCase "R1" $ do
        s <- rsize $!! Id True
        s' <- rsize $!! R ( #a := True )
        s @?= s'
    , testCase "R2" $ do
        let a = 1 :: Int
        s <- rsize $!! (a, True)
        s' <- rsize $!! R ( #a := a, #b := True )
        s @?= s'
    , testCase "R3" $ do
        let a = 1 :: Int
            c = "Hello world"
        s <- rsize $!! (a, True, c)
        s' <- rsize $!! R ( #a := a, #b := True, #c := c )
        s @?= s'
    ]
  where rsize = recursiveSize :: (a -> IO Integer)
