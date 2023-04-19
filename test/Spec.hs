import qualified Spec.HM
import qualified Spec.HM2
import Test.Hspec

main :: IO ()
main =
  hspec $ do
    describe "HM" Spec.HM.spec
    fdescribe "HM2" Spec.HM2.spec
