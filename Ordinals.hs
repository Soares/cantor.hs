{-# LANGUAGE DeriveFunctor #-}
module Ordinals where
import Prelude hiding ((^))
-- Load Integer versions of !! and length. Int versions... don't quite suffice.
import Data.List
  ( genericIndex
  , genericLength
  , genericReplicate
  , intercalate
  , span
  , find )

-- The standard form for an ordinal type.
-- We'll represent ordinals using complex expressions like ω and φ[10](ω^2),
-- and in each case, it will be possible to do a step of evaluation and get an
-- ordinal expression in one of these three forms:
data StandardForm o = Zero | Succ o | Limit [o] deriving Functor

instance Show o => Show (StandardForm o) where
  show Zero = "0"
  show (Succ x) = show x ++ " + 1"
  show (Limit os) = "[" ++ intercalate "," (map show $ take 5 os) ++ ",...]"

-- An ordinal representation is anything that can be put into standard form.
-- If you want the ordinals to be well-formed, then they must be well-founded,
-- in the sense that if you take an ordinal, put it in standard form, choose
-- a predecessor, and repeat; you'll always eventually end at zero. Note that
-- we do *not* require that the same ordinal under different representations
-- must have the same normal form; for example, 2ω and ω are representations of
-- the same ordinal, but they might have normal forms [0, 2, 4, ...] and [0, 1,
-- 2, ...] and it's fine that those differ.
class OrdinalRepr o where
  standardForm :: o -> StandardForm o

-- Let's say you want to build an x out of an ordinal representation.
-- If you tell me which x is assigned to 0, and how to get x from the
-- predecessor of a successor ordinal, and how to get an x from a fundamental
-- sequence of a limit ordinal, then I can build you an x for any OrdinalRepr.
transfiniteInduction :: OrdinalRepr o => o -> x -> (o -> x) -> ([o] -> x) -> x
transfiniteInduction o fromZero fromSuc fromLimit = case standardForm o of
  Zero -> fromZero
  Succ p -> fromSuc p
  Limit os -> fromLimit os

-- Simple classification
isZero :: OrdinalRepr o => o -> Bool
isZero o = transfiniteInduction o True (const False) (const False)

isSuccessor :: OrdinalRepr o => o -> Bool
isSuccessor o = transfiniteInduction o False (const True) (const False)

isLimit :: OrdinalRepr o => o -> Bool
isLimit o = transfiniteInduction o False (const False) (const True)

-- Say you want to pick a real high predecessor of an ordinal.
-- These are your choices.
descendants :: OrdinalRepr o => o -> [o]
descendants o = transfiniteInduction o [] pure id

-- Our goal is more or less to generate long chains of descent. Here's one
-- simple way to do so. Give me a counter and an OrdinalRepr. I'll descend to
-- zero from that ordinal, incrementing the counter at each step. At successor
-- ordinals I'll choose the immediate succesor. At limit ordianls, I'll use the
-- current value of the counter to decide how deep in the funtamental sequence
-- to go. Note that the path of descent will depend heavily on the exact
-- fundamental sequence of limit ordinals used; if the fundamental sequence
-- depends on the specific representation of the ordinal then the same ordinal
-- could yield two different paths of descent under different representations.
-- (Example: 3ω and ω represent the same ordinal, but if in standard form they
-- are represented as [0, 3, 6, 9, ...] and [0, 1, 2, 3, ...] then the chain of
-- descent will be very different.)
descend :: OrdinalRepr o => Integer -> o -> [(Integer, o)]
descend n o = (n, o) : transfiniteInduction o
  []
  (descend (n + 1))
  (\os -> descend (n + 1) (os `genericIndex` n))

-- The depth of an ordinal's descent when you start at the given counter.
depth :: OrdinalRepr o => Integer -> o -> Integer
depth n = genericLength . descend n

-- Ok, here's our ordinal representation.
-- If you want more juice, this is what you need to strengthen.
-- Note that each ordinal is represented by many expressions.
data OrdinalExpr
-- Level 1: Just the finite numbers.
  = Nat Integer
  | OrdinalExpr :+: OrdinalExpr
  | OrdinalExpr :*: OrdinalExpr
  | OrdinalExpr :^: OrdinalExpr
-- Level 2: To infinity and beyond!
  | Omega
-- Level 3: Beyond PA
  | Epsilon OrdinalExpr
-- Level 4: The fixpoint insight
  | Fixpoint OrdinalExpr (OrdinalExpr -> OrdinalExpr) String
  | BinPhi OrdinalExpr OrdinalExpr
-- Level 5: To the Veblen ordinals!
  | FinPhi [OrdinalExpr]
  | Phi OrdinalTable


instance OrdinalRepr OrdinalExpr where
-- Conventions:
--   3 * ω expands into [0, 3, 6, ...]
--   ω * 3 expands into [ω * 2 + 0, ω * 2 + 1, ω * 2 + 2, ...]
-- Thus, fundamental sequences will definitely depend on the representation.
  standardForm expr = simplify <$> expand expr where
    expand (Nat 0) = Zero
    expand (Nat n) = Succ (Nat $ pred n)

    expand (x :+: y) = transfiniteInduction y
      -- (3 + 0) => S 2
      (standardForm x)
      -- (ω + 3) => S (ω + 2)
      (Succ . (x :+:))
      -- (ω + ω) => [(ω + 0), (ω + 1), (ω + 2), ...]
      (Limit . map (x :+:))

    expand (x :*: y) = transfiniteInduction y
      -- (ω * 0) => 0
      Zero
      (\y' -> transfiniteInduction x
        -- 0 * (ω + 1) => 0
        Zero
        -- (ω + 7) * 3 => S [(ω + 7) * 2 + (ω + 6)]
        (Succ . ((x :*: y') :+:))
        -- ω * 3 => [ω * 2 + 0, ω * 2 + 1, ω * 2 + 2, ...]
        (Limit . map ((x :*: y') :+:)))
      -- ω ^ 2 * ω => [ω ^ 2 * 0, ω ^ 2 * 1, ω ^ 2 * 2, ...]
      (Limit . map (x :*:))

    expand (x :^: y) = transfiniteInduction y
      -- ω ^ 0 => 1
      (standardForm $ Nat 1)
      -- ω ^ 3 => ω ^ 2 * ω
      (\y' -> standardForm ((x :^: y') :*: x))
      -- (ω + 1)^ω => [(ω + 1)^0, (ω + 1)^1, (ω + 1)^2, ...]
      (Limit . map (x :^:))

    expand Omega = Limit [0..]

    expand (Epsilon index) = Limit $ transfiniteInduction index
      -- ε[0] is ω ^ ω ^ ω  ...
      (iterate (Omega :^:) 0)
      -- ε[1] is ε[0] ^ ε[0] ^ ε[0] ...
      -- it's also ω ^ (ε[0] + 1) ^ (ε[0] + 1) ..., making it the second
      -- fixpoint of x = ω ^ x; we'll explore that idea with BinPhi.
      (\index' -> iterate (Epsilon index' :^:) 0)
      -- ε[ω] is [ε[0], ε[1], ε[2], ...]
      (map Epsilon)

    expand (Fixpoint index fn name) = transfiniteInduction index
      (Limit $ iterate fn 0)
      (\index' -> let fp = Fixpoint index' fn name in Limit $ iterate fn (fp + 1))
      (\indices -> Limit [Fixpoint index' fn name | index' <- indices])

    expand (BinPhi strength index) = transfiniteInduction strength
      (standardForm $ Fixpoint index (Omega :^:) "ω^")
      (\strength' -> standardForm $ Fixpoint index (BinPhi strength')
        ("φ[" ++ show strength' ++ "]"))
      (\strengths -> Limit [BinPhi strength' index | strength' <- strengths])

    expand (FinPhi coefficients) = expanded where
      (index, gcfs) = decreaseCoefficients coefficients
      name decrementor' = "φ(" ++ showGcfs decrementor' gcfs ++ ")"
      recurse decrementor' = Fixpoint index (\x -> FinPhi (applyGcfs decrementor' x gcfs))
        (name decrementor')
      expanded = transfiniteInduction (gcfsDecrementor gcfs)
        -- We've bottomed out. There are no positive coefficients.
        (standardForm $ Fixpoint index (Omega :^:) "ω^")
        (standardForm . recurse)
        (Limit . map recurse)

    expand (Phi ordinalTable) = expanded where
      (index, genOT) = decreaseOrdinalTable ordinalTable
      recurse newDecrementorValue indexBelowDecrementor =
        Fixpoint index (\x -> Phi (applyGOT newDecrementorValue indexBelowDecrementor x genOT))
          (name newDecrementorValue indexBelowDecrementor)
      expanded = transfiniteInduction (indexToVary genOT)
        -- We've bottomed out. The generalized list is just (0 -> index).
        (standardForm $ Fixpoint index (Omega :^:) "ω^")
        (\indexBelowDecrementor -> transfiniteInduction (valueBeingVaried genOT)
          (error $ "malformed list: found a key with zero value" ++ show (indexToVary genOT))
          (\newDecrementorValue -> standardForm $ recurse newDecrementorValue indexBelowDecrementor)
          (\newDecrementorValues -> Limit [recurse x indexBelowDecrementor | x <- newDecrementorValues]))
        (\indicesBelowDecrementor -> transfiniteInduction (valueBeingVaried genOT)
          (error $ "malformed list: found a key with zero value" ++ show (indexToVary genOT))
          (\newDecrementorValue -> Limit [recurse newDecrementorValue y | y <- indicesBelowDecrementor])
          -- We have something like (ω -> ω). Arbitrarily, the fundamental
          -- sequence we chose will be [(1 -> ξ) (ω -> 1)], [(2 -> ξ) (ω -> 2)], etc.
          (\newDecrementorValues -> Limit [recurse x y | (x, y) <- zip newDecrementorValues indicesBelowDecrementor]))
      name newDV iBel = "φ(" ++ showGOT newDV iBel genOT ++ ")"

-- =============================================================================
-- Representation helpers for the Veblen functions.
-- It sure looks like the latter two Veblen functions are trying to use
-- [OrdinalExpr] and OrdinalTable to represent ordinals, and use the 'decrease'
-- functions below to decrease them. This is exactly what we're doing; we can
-- view both [OrdinalExpr] and OrdinalTable as rather weak representations of
-- uncountable ordinals. We could generalize this idea to a function Psi which
-- has (as a parameter) a representaiton of an uncountable ordinal and proceeds
-- in the same vein as FinPhi and Phi; this leads us straight to "ordinal
-- collapsing functions". But we're not going to go there in this code base.

-- -----------------------------------------------------------------------------
-- To the small Veblen ordinal!
-- Used to define the finite-coefficient Veblen function. The basic idea is that
-- we have a list of coefficients, and we "decrement" it as follows:
-- (1) Chop off the final value, interpret it as telling us which fixpt to use.
-- (2) Go leftward until you find something positive. Decrement it.
-- (3) Now you can insert any ordinal before the zeros you passed over.
-- Clearly, this is well-founded.
-- Examples: γ00δ0β00α → (γ, \δ' x → 00xδ'0β00α)
--           γα → (γ, \α' x → xα')
--           γ → (γ, \_ x → x)
showCfs :: [OrdinalExpr] -> String
showCfs = intercalate "," . map show

data GenCoefficients = GenCoefficients
  { gcfsHeldFixed :: [OrdinalExpr]
  , gcfsDecrementor :: OrdinalExpr
  , gcfsZeroCount :: Integer }

showGcfs :: OrdinalExpr -> GenCoefficients -> String
showGcfs newDecrementorValue gcfs = intercalate "," (zeros ++ [arg] ++ rest) where
  zeros = map show $ genericReplicate (gcfsZeroCount gcfs) (0 :: OrdinalExpr)
  arg = "_"
  rest = map show $ newDecrementorValue : gcfsHeldFixed gcfs

applyGcfs :: OrdinalExpr -> OrdinalExpr -> GenCoefficients -> [OrdinalExpr]
applyGcfs newDecrementorValue arbitraryOrdinal gcfs = if isZero (gcfsDecrementor gcfs)
  -- There was nothing to decrement. newDecrementorValue is undefined.
  then [arbitraryOrdinal]
  else genericReplicate (gcfsZeroCount gcfs) (0 :: OrdinalExpr) ++
       [arbitraryOrdinal, newDecrementorValue] ++ 
       gcfsHeldFixed gcfs

-- If there 2nd value isZero, the 3rd value ignores its first argument.
decreaseCoefficients :: [OrdinalExpr] -> (OrdinalExpr, GenCoefficients)
decreaseCoefficients coefficients = (index, gen) where
  (index:rest1) = if null coefficients then [0] else coefficients
  (zeros, rest2) = span isZero rest1
  gen = case rest2 of
    [] -> GenCoefficients [] 0 0
    (decrementor:fixed) -> GenCoefficients fixed decrementor (genericLength zeros)

-- -----------------------------------------------------------------------------
-- To the large Veblen ordinal!
-- We do basically the same thing as the small Veblen ordinal, except things
-- can ordinally-deep in the coefficient list. Every ordinal not mentioned in
-- the table is assumed to have value 0. The table must be finite. The table
-- should have at most one isZero key.
type OrdinalTable = [(OrdinalExpr, OrdinalExpr)]

data GenOrdinalTable = GenOrdinalTable
  { portionHeldFixed :: OrdinalTable
  , indexToVary :: OrdinalExpr
  , valueBeingVaried :: OrdinalExpr }

applyGOT :: OrdinalExpr -> OrdinalExpr -> OrdinalExpr -> GenOrdinalTable -> OrdinalTable
applyGOT newValueAtIndex indexBelow arbitraryOrdinal got =
  if isZero (indexToVary got)
    -- There is no indexBelow; it will be undefined. We've bottomed out.
    then [(0, arbitraryOrdinal)]
    else [(indexBelow, arbitraryOrdinal), (indexToVary got, newValueAtIndex)] ++ portionHeldFixed got

showOT :: OrdinalTable -> String
showOT = intercalate "," . map (\(k, v) -> show k ++ "↦" ++ show v)

showGOT :: OrdinalExpr -> OrdinalExpr -> GenOrdinalTable -> String
showGOT newValueAtIndex indexBelowValue got = intercalate "," $ [a, b] ++ cs where
  a = show indexBelowValue ++ "↦_"
  b = show (indexToVary got) ++ "↦" ++ show newValueAtIndex
  cs = map (\(k, v) -> show k ++ "↦" ++ show v) (portionHeldFixed got)

decreaseOrdinalTable :: OrdinalTable -> (OrdinalExpr, GenOrdinalTable)
decreaseOrdinalTable table = (fixptIndex, generator) where
  (fixptIndex, sanitized) = sepZeroValAndDropZeroKeysAndVals table
  (decrementor, valueOfDecrementor, heldFixed) = splitFirstPositiveKeyVal sanitized
  generator = GenOrdinalTable heldFixed decrementor valueOfDecrementor
  sepZeroValAndDropZeroKeysAndVals [] = (0, [])
  sepZeroValAndDropZeroKeysAndVals xs = (v, rest) where
    v = maybe 0 snd $ find (isZero . fst) xs
    rest = removeZeroKeysAndVals xs
  splitFirstPositiveKeyVal [] = (0, 0, [])
  splitFirstPositiveKeyVal ((k, v):rest) = (k, v, rest)
  removeZeroKeysAndVals = filter (\(k, v) -> not (isZero k || isZero v))
-- =============================================================================


-- =============================================================================
-- Some neat ordinals.

smallVeblenOrdinal :: OrdinalExpr
smallVeblenOrdinal = Phi [(Omega, 1)]

largeVeblenOrdinal :: OrdinalExpr
largeVeblenOrdinal = Fixpoint 0 (\o -> Phi [(o, 1)]) "the large Veblen sequence"

-- -----------------------------------------------------------------------------
-- The rest is boilerplate.

-- We derive Num so that you can write, e.g., "Omega + 7", which is really
-- convenient. However, we don't actually satisfy all the Haskell num laws: we
-- can't equality check, and we can't negate. Thus, some functions give errors.
instance Num OrdinalExpr where
  x + y = simplify (x :+: y)
  x * y = simplify (x :*: y)
  abs = id
  signum _ = Nat 1
  fromInteger = Nat
  negate = error "ordinals are positive"
-- Haskell doesn't make it easy to override (^), so we just hide the Prelude
-- one and implement our own.
(^) :: OrdinalExpr -> OrdinalExpr -> OrdinalExpr
x ^ y = simplify (x :^: y)
-- We only derive Eq and Enum so that we can implement Num for user convenience
-- (of writing, e.g, "Omega + 7" to get an ordinal). Don't try to use it.  (Why
-- not check literal equality of expressions, even if we can't check
-- equivalence o the represented ordial? Because Fixpoint type expressions
-- contain functions, and Haskell can't handle checking function equivalence.)
instance Eq OrdinalExpr where
  _ == _ = error "It's real hard to tell when ordinals are equal."
-- We also only derive Enum so that we can use Num. You can use succ, but pred
-- will only work on successor ordinals.
instance Enum OrdinalExpr where
  succ (Nat n) = Nat (succ n)
  succ (x :+: y) = x :+: succ y
  succ expr = expr :+: Nat 1
  pred expr = transfiniteInduction expr
    (error "zero has no predecessor")
    id
    (error "cannot find immediate predecessor of limit ordinal")
  toEnum = Nat . toInteger
  fromEnum expr = case simplify expr of
    Nat n -> fromInteger n
    _ -> error "cannot convert ordinal to int"

data EvalOrdinalExpr a = EvalOrdinalExpr
  { atNat :: Integer -> a
  , atPlus :: a -> a -> a
  , atTimes :: a -> a -> a
  , atExp :: a -> a -> a
  , atOmega :: a
  , atEpsilon :: a -> a
  , atFixpoint :: a -> (OrdinalExpr -> OrdinalExpr) -> String -> a
  , atBinPhi :: a -> a -> a
  , atFinPhi :: [a] -> a
  , atPhi :: [(a, a)] -> a }

evalOrdinalExpr :: EvalOrdinalExpr a -> OrdinalExpr -> a
evalOrdinalExpr eval expr = let recurse = evalOrdinalExpr eval in case expr of
  Nat i -> atNat eval i
  x :+: y -> atPlus eval (recurse x) (recurse y)
  x :*: y -> atTimes eval (recurse x) (recurse y)
  x :^: y -> atExp eval (recurse x) (recurse y)
  Omega -> atOmega eval
  Epsilon index -> atEpsilon eval (recurse index)
  Fixpoint index fn mname -> atFixpoint eval (recurse index) fn mname
  BinPhi subscript index -> atBinPhi eval (recurse subscript) (recurse index)
  FinPhi args -> atFinPhi eval $ map recurse args
  Phi fn -> atPhi eval [(recurse k, recurse v) | (k, v) <- fn]

simplify :: OrdinalExpr -> OrdinalExpr
simplify = evalOrdinalExpr simplifier where
  simplifier :: EvalOrdinalExpr OrdinalExpr
  simplifier = EvalOrdinalExpr
    { atNat = Nat
    , atPlus  = \x y -> case (x, y) of
                          (Nat 0, _) -> y
                          (_, Nat 0) -> x
                          _ -> x :+: y
    , atTimes = \x y -> case (x, y) of
                          (Nat 0, _) -> Nat 0
                          (_, Nat 0) -> Nat 0
                          (Nat 1, _) -> y
                          (_, Nat 1) -> x
                          _ -> x :*: y
    , atExp = \x y -> case (x, y) of
                          (_, Nat 0) -> Nat 1
                          (Nat 0, _) -> Nat 0
                          (Nat 1, _) -> Nat 1
                          (_, Nat 1) -> x
                          _ -> x :^: y
    , atOmega = Omega
    , atEpsilon = Epsilon
    , atFixpoint = Fixpoint
    , atBinPhi = BinPhi
    , atFinPhi = FinPhi
    , atPhi = Phi }
  
-- We avoid using EvalOrdinalExpr here because it's not easy to thread the
-- showsPrec precedence through.
instance Show OrdinalExpr where
  showsPrec p e0 = let
    string str = (str ++)
    op str = ((" " ++ str ++ " ") ++)
    bracket o = ("[" ++) . o . ("]" ++)
    args os = ("(" ++) . (intercalate "," os ++) . (")" ++)
    in case e0 of
      Nat n -> shows n
      x :+: y -> showParen (p >= 6) $ showsPrec 6 x . op "+" . showsPrec 6 y
      x :*: y -> showParen (p >= 7) $ showsPrec 7 x . op "*" . showsPrec 7 y
      x :^: y -> showParen (p >= 8) $ showsPrec 8 x . op "^" . showsPrec 8 y
      Omega -> string "ω"
      Epsilon o -> string "ε" . bracket (shows o)
      BinPhi index arg -> string "φ" . bracket (shows index) . args [show arg]
      Fixpoint index _ name -> let
        start = string "<fixpoint " . shows index . string " of "
        end = string ">"
        in start . string name . end
      FinPhi os -> string "φ" . args (map show os)
      Phi fn -> string $ "φ(" ++ showOT fn ++ ")"
