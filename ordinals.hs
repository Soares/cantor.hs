-- Load Integer versions of !! and length. Int versions... don't quite suffice.
import Data.List (genericIndex, genericLength)

-- Here we make a weak representation of ordinals. If you want more juice out
-- of your ordinals, code up a stronger representation.
data Ordinal
  = Nat Integer
  | Omega
  | Epsilon Ordinal -- Shorthand for Phi (Nat 1)
  | Phi Ordinal Ordinal
  | Ordinal :+: Ordinal
  | Ordinal :*: Ordinal
  | Ordinal :^: Ordinal

instance Show Ordinal where
  showsPrec p e0 = case e0 of
    Nat n -> shows n
    Omega -> ("ω" ++)
    Epsilon ordinal -> ("ε[" ++) . shows ordinal . ("]" ++)
    Phi gamma alpha -> ("φ[" ++) . shows gamma . ("](" ++) . shows alpha . (")" ++)
    x :+: y -> showParen (p >= 6) $ showsPrec 6 x . (" + " ++) . showsPrec 6 y
    x :*: y -> showParen (p >= 7) $ showsPrec 7 x . (" * " ++) . showsPrec 7 y
    x :^: y -> showParen (p >= 8) $ showsPrec 8 x . (" ^ " ++) . showsPrec 8 y

-- Here's how to decrease an ordinal:
-- For zero, you can't decrease it.
-- For successor ordinals, yield the predecessor.
-- For limit ordinals, yield a fundamental sequence.
-- Conventions:
--   3 * ω expands into [0, 3, 6, ...]
--   ω * 3 expands into [ω * 2 + 0, ω * 2 + 1, ω * 2 + 2, ...]
-- Descent chains are not unique; equivalent ordinals in different
-- representations will generate different chains of descent.
decrease :: Ordinal -> Maybe (Either [Ordinal] Ordinal)
decrease (Nat 0) = Nothing
decrease (Nat n) = Just $ Right (Nat $ n - 1)
decrease Omega = Just $ Left $ fmap Nat [0..]
decrease (Epsilon ordinal) =
  let powerTower ordinal n = iterate (ordinal :^:) (Nat 0) `genericIndex` n
  in case decrease ordinal of
    Nothing -> Just $ Left $ fmap (powerTower Omega) [0..]
    Just (Right prev) -> Just $ Left $ fmap (powerTower (Epsilon prev)) [0..]
    Just (Left seq) -> Just $ Left $ fmap Epsilon seq
decrease (Phi gamma alpha) = case decrease gamma of
  Nothing -> decrease (Omega :^: alpha)
  Just (Right gamma') -> case decrease alpha of
    -- φ[γ+1](0) = [φ[γ](0), φ[γ](φ[γ](0)), φ[γ](φ[γ](φ[γ](0))), ...]
    Nothing -> Just $ Left $ iterate (Phi gamma') (Nat 0)
    -- φ[γ+1](3) = [φ[γ](φ[γ+1](2)+1), ...]
    Just (Right alpha') -> Just $ Left $ iterate (Phi gamma') ((Phi gamma alpha') :+: Nat 1)
    -- φ[γ+1](ω) = [φ[γ+1](0), φ[γ+1](1), ...]
    Just (Left alphaSeq) -> Just $ Left [Phi gamma alpha' | alpha' <- alphaSeq]
  -- φ[ω](α) = [φ[0](α), φ[1](α), φ[2](α), ...]
  Just (Left gammaSeq) -> Just $ Left [Phi gamma' alpha | gamma' <- gammaSeq]
decrease (x :+: y) =  case decrease y of
  -- (3 + (7 * 0)) => predecessor of 3
  Nothing -> decrease x
  -- ω + 2 => ω + 1
  Just (Right yPred) -> Just $ Right (x :+: yPred)
  -- 3 + ω => [3 + 0, 3 + 1, 3 + 2, ...]
  Just (Left ySeq) -> Just $ Left [x :+: yVal | yVal <- ySeq]
decrease (x :*: y) = case decrease y of
  -- (ω * 0) => no predecessor
  Nothing -> Nothing
  -- 3 * ω => [3 * 0, 3 * 1, 3 * 2, ...]
  Just (Left ySeq) -> Just $ Left (fmap (x :*:) ySeq)
  Just (Right yPred) -> case decrease x of
    -- 0 * (ω + 1) => no predecessor
    Nothing -> Nothing
    -- (ω + 1) * 3 => (ω + 1) * 2 + ω
    Just (Right xPred) -> Just $ Right ((x :*: yPred) :+: xPred)
    -- ω * 3 => [ω * 2 + 0, ω * 2 + 1, ω * 2 + 2, ...]
    Just (Left xSeq) -> Just $ Left (fmap ((x :*: yPred) :+:) xSeq)
decrease (x :^: Nat 0) = decrease (Nat 1)
decrease (x :^: y) = case decrease y of
  -- ω ^ 0 => 1
  Nothing -> decrease (Nat 1)
  -- ω ^ 3 => predecessor of ω ^ 2 * ω
  Just (Right yPred) -> decrease ((x :^: yPred) :*: x)
  -- (ω + 1)^ω => [(ω + 1)^0, (ω + 1)^1, (ω + 1)^2, ...]
  Just (Left ySeq) -> Just $ Left [x :^: yVal | yVal <- ySeq]

-- If you want an immediate predecessor of an ordinal, these are your choices.
descendants :: Ordinal -> [Ordinal]
descendants = maybe [] (either id pure) . decrease

-- Given a counter, descends down the whole chain for an ordinal, incrementing
-- the counter each step. Whenever we need to descend a limit ordinal, we use
-- the current counter to decide how deep in the fundamental sequence to go.
chain :: Integer -> Ordinal -> [(Integer, Ordinal)]
chain n ordinal = (n, ordinal) : descent where
  descent = case decrease ordinal of
    Nothing -> []
    Just (Right prev) -> chain (n + 1) prev
    Just (Left seq) -> chain (n + 1) (seq `genericIndex` n)

-- The depth of an ordinal's chain when you start at the given counter.
value :: Integer -> Ordinal -> Integer
value n = genericLength . chain n

-- The depth of an ordinal's chain when you start at 1.
encode :: Ordinal -> Integer
encode = value 1

-- The fast-growing hierarchy.
f :: Ordinal -> Integer -> Integer
f alpha n = case decrease alpha of
  Nothing -> n + 1
  Just (Right prev) -> iterate (f prev) n `genericIndex` n
  Just (Left seq) -> f (seq `genericIndex` n) n

-- I'm glad Haskell has arbitrary precision Integers. Let's put them to the test.
grahamsNumber :: Integer
grahamsNumber = f (Omega :+: Nat 1) 64

-- Now let's have the fast-growing hierarchy show its work.
data Fexpr = F Ordinal Fexpr | Mere Integer

instance Show Fexpr where
  show (Mere n) = show n
  show (F alpha expr) = "f[" ++ show alpha ++ "](" ++ show expr ++ ")"

step :: Fexpr -> Fexpr
step (Mere n) = Mere n
step (F alpha (Mere n)) = case decrease alpha of
  Nothing -> Mere (n + 1)
  Just (Right prev) -> iterate (F prev) (Mere n) `genericIndex` n
  Just (Left seq) -> F (seq `genericIndex` n) (Mere n)
step (F alpha expr) = F alpha (step expr)

expand :: Fexpr -> [Fexpr]
expand (Mere n) = [Mere n]
expand expr = expr : expand (step expr)

verboseF :: Ordinal -> Integer -> [Fexpr]
verboseF alpha n = expand (F alpha $ Mere n)

main :: IO ()
main = mapM_ print $ take 10 $ verboseF (Omega :+: Nat 1) 64
