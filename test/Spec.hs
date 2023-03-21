import qualified Spec.HM
import Test.Hspec

main :: IO ()
main =
  hspec $
    describe "HM" Spec.HM.spec
