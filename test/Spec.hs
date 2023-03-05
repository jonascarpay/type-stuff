import Test.Hspec

main :: IO ()
main =
  hspec $
    describe "type-stuff-test" $
      it "works" $
        2 + 2 `shouldBe` (4 :: Int)
