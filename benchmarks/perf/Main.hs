{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Main (main) where

import Criterion.Main
import Data.Rawr

main :: IO ()
main =
  defaultMain
    [ bgroup "R/reverse5"
        [ bench "rawr" $ nf R ( #e := (), #d := (), #c := (), #b := (), #a := () )
        , bench "handwritten" $ nf (\(a, b, c, d, e) -> (e, d, c, b, a)) ( #e := (), #d := (), #c := (), #b := (), #a := () )
        , bench "identity" $ nf id ( #e := (), #d := (), #c := (), #b := (), #a := () )
        ]
    , bgroup "R/identity5"
        [ bench "rawr" $ nf R ( #a := (), #b := (), #c := (), #d := (), #e := () )
        , bench "handwritten" $ nf id ( #a := (), #b := (), #c := (), #d := (), #e := () )
        ]
    , bgroup "select"
        [ bench "rawr" $ nf #e (R ( #a := (), #b := (), #c := (), #d := (), #e := () ))
        , bench "handwritten" $ nf (\(_, _, _, _, e) -> e) ( #a := (), #b := (), #c := (), #d := (), #e := () )
        ]
    , bgroup "merge"
        [ bench "rawr" $ nf (uncurry (:*:)) (R ( #a := (), #e := () ), R ( #b := (), #c := (), #d := () ))
        , bench "handwritten" $ nf (uncurry $ \(a, e) (b, c, d) -> (a, b, c, d, e)) (( #a := (), #e := () ), ( #b := (), #c := (), #d := () ))
        ]
    , bgroup "partition"
        [ bench "rawr" $ nf (\(R ( _ :: "c" := () , _ :: "e" := () ) :*: r) -> r) (R ( #a := (), #b := (), #c := (), #d := (), #e := () ))
        , bench "handwritten" $ nf (\(a, b, _, d, _) -> (a, b, d)) ( #a := (), #b := (), #c := (), #d := (), #e := () )
        ]
    ]
