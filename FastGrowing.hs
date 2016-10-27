module FastGrowing where
import Data.List (genericIndex)
import Ordinals

-- The fast-growing hierarchy.
f :: OrdinalRepr o => o -> Integer -> Integer
f alpha n = transfiniteInduction alpha
  (n + 1)
  (\alpha' -> iterate (f alpha') n `genericIndex` n)
  (\alphas -> f (alphas `genericIndex` n) n)

-- I'm glad Haskell has arbitrary precision Integers. Let's put them to the test.
grahamsNumber :: Integer
grahamsNumber = f (Omega + 1) 64

-- Now let's have the fast-growing hierarchy show its work.
data Fexpr o = F o (Fexpr o) | Mere Integer

instance Show o => Show (Fexpr o) where
  show (Mere n) = show n
  show (F alpha expr) = "f[" ++ show alpha ++ "](" ++ show expr ++ ")"

step :: OrdinalRepr o => Fexpr o -> Fexpr o
step (Mere n) = Mere n
step (F alpha (Mere n)) = transfiniteInduction alpha
  (Mere (n + 1))
  (\alpha' -> iterate (F alpha') (Mere n) `genericIndex` n)
  (\alphas -> F (alphas `genericIndex` n) (Mere n))
step (F alpha expr) = F alpha (step expr)

expand :: OrdinalRepr o => Fexpr o -> [Fexpr o]
expand (Mere n) = [Mere n]
expand expr = expr : expand (step expr)

verboseF :: OrdinalRepr o => o -> Integer -> [Fexpr o]
verboseF alpha n = expand (F alpha $ Mere n)

-- The first 10 steps of evaluating Graham's number via f.
main :: IO ()
main = mapM_ print $ take 10 $ verboseF (Omega + 1) 64
