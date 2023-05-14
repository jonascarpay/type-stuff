{-# LANGUAGE OverloadedStrings #-}

import Control.DeepSeq (NFData, deepseq)
import Criterion
import Criterion.Main
import qualified HM.Check as HM
import qualified HM.Free.Check as Ref
import qualified HM.Free.FastCheck as Fast
import qualified HM.Free.Term as Free
import HM.Term
import HM.Term.Embed
import HM.Type

-- TODO benchmark `infer`, not `inferT`
benchInfer ::
  NFData a =>
  (TermInfo -> a) ->
  (a -> Either String (Type Int)) ->
  [Benchmark]
benchInfer convert infer =
  [ run "Int" 0,
    bgroup
      "explode"
      [ run "0" (explodeLet 0),
        run "5" (explodeLet 5),
        run "10" (explodeLet 10)
      ],
    bgroup
      "SKI"
      [ run "S" (λ "x" $ λ "y" $ λ "z" $ "x" @ "z" @ ("y" @ "z")),
        run "K" (λ "x" $ λ "y" "x"),
        run "I" (λ "x" "x")
      ]
  ]
  where
    run :: String -> Term -> Benchmark
    run label term =
      let term' = convert $ resolve term
       in deepseq term' $ bench label $ whnf infer term'

main :: IO ()
main =
  defaultMain
    [ bgroup "reference" $ benchInfer Free.fromTermInfo Ref.inferT,
      bgroup "fast" $ benchInfer Free.fromTermInfo Fast.inferT,
      bgroup "term" $ benchInfer id HM.inferT
    ]
