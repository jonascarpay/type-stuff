import qualified Spec.HM
import Test.Hspec

main :: IO ()
main =
  hspec $ do
    describe "HM" Spec.HM.spec
