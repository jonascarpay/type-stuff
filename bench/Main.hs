{-# LANGUAGE OverloadedStrings #-}

import Control.DeepSeq (deepseq)
import Criterion
import Criterion.Main
import qualified HM.Check as Reference
import qualified HM.FastCheck as Fast
import HM.Term
import HM.Type

-- TODO benchmark `infer`, not `inferT`
benchInfer ::
  (Term String -> Either String (Type Int)) ->
  [Benchmark]
benchInfer infer =
  [ run "Int" 0,
    bgroup
      "explode"
      [ run "0" (explode 0),
        run "5" (explode 5),
        run "10" (explode 10)
      ],
    bgroup
      "SKI"
      [ run "S" (λ "x" $ λ "y" $ λ "z" $ "x" @ "z" @ ("y" @ "z")),
        run "K" (λ "x" $ λ "y" "x"),
        run "I" (λ "x" "x")
      ]
  ]
  where
    run :: String -> Term String -> Benchmark
    run label term = deepseq term $ bench label $ whnf infer term

main :: IO ()
main =
  defaultMain
    [ bgroup "reference" $ benchInfer Reference.inferT,
      bgroup "fast" $ benchInfer Fast.inferT
    ]
