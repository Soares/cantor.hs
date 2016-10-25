-- Load Integer versions of !! and length. Int versions... don't quite suffice.
import Data.List (genericIndex, genericLength)

-- Here we make a weak representation of ordinals. If you want more juice out
-- of your ordinals, code up a stronger representation.
data CantorOrdinal
  = Nat Integer
  | Omega
  | CantorOrdinal :+: CantorOrdinal
  | CantorOrdinal :*: CantorOrdinal
  | CantorOrdinal :^: CantorOrdinal

instance Show CantorOrdinal where
  showsPrec p e0 = case e0 of
    Nat n -> shows n
    Omega -> ("ω" ++)
    x :+: y -> showParen (p >= 6) $ showsPrec 6 x . (" + " ++) . showsPrec 6 y
    x :*: y -> showParen (p >= 7) $ showsPrec 7 x . (" * " ++) . showsPrec 7 y
    x :^: y -> showParen (p >= 8) $ showsPrec 8 x . (" ^ " ++) . showsPrec 8 y

-- Here's how to decrease an ordinal:
-- For zero, yield zero.
-- For successor ordinals, yield the predecessor.
-- For limit ordinals, yield a fundamental sequence.
-- Conventions:
--   3 * ω expands into [0, 3, 6, ...]
--   ω * 3 expands into [ω * 2 + 0, ω * 2 + 1, ω * 2 + 2, ...]
-- Descent chains are not unique; equivalent ordinals in different
-- representations will generate different chains of descent.
decrease :: CantorOrdinal -> Either [CantorOrdinal] CantorOrdinal
decrease (Nat 0) = Right $ Nat 0
decrease (Nat n) = Right (Nat $ n - 1)
decrease Omega = Left (fmap Nat [0..])
decrease (x :+: Nat 0) = decrease x
decrease (x :+: y) =  case decrease y of
  -- Example: ω + 2 => ω + 1
  Right yPred -> Right (x :+: yPred)
  -- Example: 3 + ω => [3 + 0, 3 + 1, 3 + 2, ...]
  Left ySeq -> Left [x :+: yVal | yVal <- ySeq]
decrease (x :*: Nat 0) = decrease (Nat 0)
decrease (x :*: y) = case (decrease x, decrease y) of
  -- Example: (ω + 1) * 3 => (ω + 1) * 2 + ω
  (Right xPred, Right yPred) -> Right ((x :*: yPred) :+: xPred)
  -- Example: ω * 3 => [ω * 2 + 0, ω * 2 + 1, ω * 2 + 2, ...]
  (Left xSeq, Right yPred) -> Left [(x :*: yPred) :+: xVal | xVal <- xSeq]
  -- Example: 3 * ω => [3 * 0, 3 * 1, 3 * 2, ...]
  (_, Left ySeq) -> Left [x :*: yVal | yVal <- ySeq]
decrease (x :^: Nat 0) = decrease (Nat 1)
decrease (x :^: y) = case decrease y of
  -- Example: ω ^ 3 => predecessor of ω ^ 2 * ω
  Right yPred -> decrease ((x :^: yPred) :*: x)
  -- Example: (ω + 1)^ω => [(ω + 1)^0, (ω + 1)^1, (ω + 1)^2, ...]
  Left ySeq -> Left [x :^: yVal | yVal <- ySeq]

-- Given a counter, descends down the whole chain for an ordinal, incrementing
-- the counter each step. Whenever we need to descend a limit ordinal, we use
-- the current counter to decide how deep in the fundamental sequence to go.
chain :: Integer -> CantorOrdinal -> [(Integer, CantorOrdinal)]
chain n (Nat 0) = [(n, Nat 0)]
chain n ordinal = (n, ordinal) : os where
  os = case decrease ordinal of
    Right prev -> chain (n + 1) prev
    Left seq -> chain (n + 1) (seq `genericIndex` n)

-- The depth of an ordinal's chain when you start at the given counter.
value :: Integer -> CantorOrdinal -> Integer
value n = genericLength . chain n

-- The depth of an ordinal's chain when you start at 1.
encode :: CantorOrdinal -> Integer
encode = value 1

-- The fast-growing hierarchy.
f :: CantorOrdinal -> Integer -> Integer
f (Nat 0) n = n + 1
f alpha n = case decrease alpha of
  Right prev -> iterate (f prev) n `genericIndex` n
  Left seq -> f (seq `genericIndex` n) n

-- I'm glad Haskell has arbitrary precision Integers. Let's put them to the test.
grahamsNumber :: Integer
grahamsNumber = f (Omega :+: Nat 1) 64

-- Now let's have the fast-growing hierarchy show its work.
data Fexpr = F CantorOrdinal Fexpr | Mere Integer

instance Show Fexpr where
  show (Mere n) = show n
  show (F alpha expr) = "f[" ++ show alpha ++ "](" ++ show expr ++ ")"

step :: Fexpr -> Fexpr
step (Mere n) = Mere n
step (F (Nat 0) (Mere n)) = Mere (n + 1)
step (F alpha (Mere n)) = case decrease alpha of
  Right prev -> iterate (F prev) (Mere n) `genericIndex` n
  Left seq -> F (seq `genericIndex` n) (Mere n)
step (F alpha expr) = F alpha (step expr)

expand :: Fexpr -> [Fexpr]
expand (Mere n) = [Mere n]
expand expr = expr : expand (step expr)

verboseF :: CantorOrdinal -> Integer -> [Fexpr]
verboseF alpha n = expand (F alpha $ Mere n)

main :: IO ()
main = mapM_ print $ take 10 $ verboseF (Omega :+: Nat 1) 64
