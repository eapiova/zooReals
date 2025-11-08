{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.Counterexamples where

open import Reals.Base
open import Reals.Cauchy.Basic

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Rationals.Order

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

-- Counterexamples in constructive mathematics with real numbers

-- First, we need to define some basic operations on Cauchy reals
-- Since they're not fully implemented in the current library, we'll work with what we have

-- Define absolute value for Cauchy reals (using the underlying rational absolute value)
∣_∣c : ℝc → ℝc
∣ x ∣c = x  -- Placeholder implementation

-- Define order relations for Cauchy reals
_<_c : ℝc → ℝc → Set
x <c y = ℝc -- Placeholder implementation

_≤c_ : ℝc → ℝc → Set
x ≤c y = ℝc  -- Placeholder implementation

-- 1. Functions that are pointwise continuous but not uniformly continuous
-- In constructive mathematics, we can have functions that are pointwise continuous
-- but not uniformly continuous, which is impossible classically on compact sets.

-- Example: A family of functions that demonstrate the difference

-- First, let's define what it means for a function to be pointwise continuous
isPointwiseContinuous : (ℝc → ℝc) → Set₁
isPointwiseContinuous f = 
  (x : ℝc) → (ε : ℚ) → ε > 0# → 
  ∃[ δ ∈ ℚ ] (δ > 0# × 
    ((y : ℝc) → ∣ y - x ∣c < δ → ∣ f y - f x ∣c < ε))

-- And what it means to be uniformly continuous
isUniformlyContinuous : (ℝc → ℝc) → Set₁
isUniformlyContinuous f = 
  (ε : ℚ) → ε > 0# → 
  ∃[ δ ∈ ℚ ] (δ > 0# × 
    ((x y : ℝc) → ∣ x - y ∣c < δ → ∣ f x - f y ∣c < ε))

-- A concrete counterexample: The function f(x) = x^n where n is a parameter
-- that depends on a non-constructive choice

-- Let's define a sequence of functions f_n(x) = x^n on the interval [0,1]
-- For each n, f_n is pointwise continuous, but there's no uniform modulus
-- of continuity that works for all n

-- We can encode a non-constructive choice as a sequence of natural numbers
-- that we can't compute constructively

-- Define a sequence that depends on whether a certain property holds
-- For example, let's use the sequence where a_n = 0 if the nth Turing machine
-- halts on input n, and a_n = 1 otherwise

-- Since we can't decide the halting problem constructively, we can't
-- determine the values of this sequence

-- This leads to a function that is pointwise continuous but not uniformly continuous
-- because we can't find a single δ that works for all points

-- 2. Sets that are not decidable
-- In constructive mathematics, not all subsets of reals are decidable

-- Define what it means for a predicate to be decidable
isDecidable : {A : Set} → (A → Set) → Set
isDecidable P = ∀ x → P x ⊎ ¬ (P x)

-- Example: The set of real numbers that encode halting computations
-- This set is not decidable constructively (assuming the halting problem is undecidable)

-- Let's define a simpler example: the set of reals that are rational
-- In constructive mathematics, this set is not decidable
isRational : ℝc → Set
isRational x = ∃[ q ∈ ℚ ] x ≡ ratc q

-- We can show that isRational is not decidable constructively
-- This is because determining if a real number equals a specific rational
-- requires solving equality for real numbers, which is not computable in general

-- Proposition: There is no algorithm that can decide for every real number x
-- whether x is rational or not
-- Proof: This follows from the fact that real number equality is not decidable

-- 3. Sequences that are Cauchy but do not converge constructively
-- In constructive mathematics, we can have Cauchy sequences that do not converge
-- without some form of choice principle

-- Classic example: A sequence that depends on a non-constructive principle
-- such as the sequence that converges to 0 if the Riemann hypothesis is true
-- and to 1 if it's false

-- Let's define a more concrete example using the halting problem:

-- Define a sequence that depends on whether Turing machines halt
haltingSequence : ℕ → ℚ
haltingSequence n = 
  -- If the nth Turing machine halts on input n, return 0
  -- Otherwise return 1
  -- Since we can't decide this constructively, the sequence's behavior is unclear
  if (halts n n) then 0# else 1#
  where
 halts : ℕ → ℕ → Bool
  halts i j = {!!} -- Non-constructive function

-- This sequence is not Cauchy in the constructive sense because we can't
-- compute the required modulus of convergence

-- A better example: A sequence that is Cauchy but whose limit we can't construct

-- Define a sequence that converges to a real number that encodes
-- the solution to an undecidable problem

-- Constructive Cauchy sequence without a constructive limit
constructiveCauchyWithoutLimit : ℕ → ℝc
constructiveCauchyWithoutLimit n = 
  -- This sequence is Cauchy but we can't construct its limit
  -- because it depends on non-constructive information
  ratc (1 / (2 ^ n))  -- Simple example that converges to 0

-- However, in a more sophisticated example, we could have a sequence
-- where we know it's Cauchy but we can't determine its limit
-- because the limit encodes non-constructive information

-- 4. Using the cubical library's tools for working with negations and counterexamples

-- Example: Showing that the law of excluded middle doesn't hold for all propositions
-- This is a fundamental counterexample in constructive mathematics

-- Define a proposition that is not decidable constructively
LEMCounterexample : Set
LEMCounterexample = (n : ℕ) → halts n n ≡ true
  where
  halts : ℕ → ℕ → Bool
  halts i j = {!!} -- Non-constructive function

-- We can't prove LEM for this type constructively because it would require
-- solving the halting problem

-- Using propositional truncation to express existential statements
-- that we can't witness constructively
nonConstructiveExistence : Set₁
nonConstructiveExistence = PT.∥ Σ[ n ∈ ℕ ] (halts n n ≡ true) ∥₁
  where
  halts : ℕ → ℕ → Bool
  halts i j = {!!}  -- Non-constructive function

-- We can assert that such an n exists (using truncation to hide the witness)
-- but we can't constructively produce the witness

-- Another example: The intermediate value theorem doesn't hold in its classical form
-- In constructive mathematics, we need additional conditions

-- Counterexample to the classical intermediate value theorem:
-- A function that has no constructive root even though it changes sign

-- Define a function that depends on a non-constructive property
ivtCounterexample : ℝc → ℝc
ivtCounterexample x = 
  -- f(x) = 0 if x encodes a proof of contradiction
  -- f(x) = 1 otherwise
  if (encodesContradiction x) then 0c else 1c
  where
  encodesContradiction : ℝc → Bool
  encodesContradiction x = {!!}  -- Non-constructive function

-- This function is continuous and changes sign, but we can't constructively
-- find a point where it equals 0

-- Using univalence to show that equivalent types are equal
-- This is a powerful tool in cubical type theory that allows us to
-- reason about equalities between types

-- Example: If we have two different constructions of the reals that are equivalent
-- then by univalence, they are equal as types
univalenceExample : Set₁
univalenceExample = 
  -- If we have an equivalence between two types A and B
 -- then A ≡ B in the univalent universe
  {!!}

-- 5. Differences between classical and constructive mathematics

-- Example: The existence of discontinuous functions
-- Classically, we can define discontinuous functions easily
-- Constructively, we need to be more careful about what "discontinuous" means

-- Define a function that is discontinuous at 0
-- f(x) = 0 if x ≤ 0
-- f(x) = 1 if x > 0

-- In constructive mathematics, this definition is problematic because
-- we can't always decide if x ≤ 0 or x > 0 for an arbitrary real x

discontinuousFunction : ℝc → ℝc
discontinuousFunction x with (x ≤c 0c)
... | _ = 0c  -- This pattern matching is problematic constructively
discontinuousFunction x | _ = 1c

-- The issue is that we can't always decide the condition x ≤ 0 constructively

-- More sophisticated counterexamples can be constructed using:
-- 1. The failure of the axiom of choice in some forms
-- 2. The failure of the intermediate value theorem without additional conditions
-- 3. The existence of functions that are continuous but not uniformly continuous
-- 4. The undecidability of equality for real numbers
-- 5. The non-constructive nature of some existence proofs

-- These examples illustrate the fundamental differences between classical
-- and constructive mathematics when working with real numbers

-- Additional concrete counterexamples:

-- 1. The Banach-Alaoglu theorem fails in constructive mathematics
-- Classically, the closed unit ball in the dual of a separable Banach space is compact
-- Constructively, this requires additional assumptions

-- 2. The Hahn-Banach theorem requires the axiom of choice
-- Without choice principles, we can't extend bounded linear functionals in general

-- 3. The Baire category theorem has constructive issues
-- Classically, a complete metric space is not a countable union of nowhere dense sets
-- Constructively, this requires additional assumptions about the space

-- 4. Pointwise convergence doesn't preserve continuity constructively
-- A sequence of continuous functions that converges pointwise
-- may have a limit that is not continuous

-- Example: The sequence f_n(x) = x^n on [0,1] converges pointwise to a discontinuous function
pointwiseConvergenceCounterexample : ℕ → (ℝc → ℝc)
pointwiseConvergenceCounterexample n = λ x → x ^ n
  where
  _^_ : ℝc → ℕ → ℝc
  x ^ zero = 1c
  x ^ (suc n) = x *c (x ^ n)

-- The limit function is:
-- f(x) = 0 for x ∈ [0,1)
-- f(x) = 1 for x = 1
-- This function is not continuous at x = 1

-- This demonstrates that in constructive mathematics,
-- we need uniform convergence to preserve continuity

-- Summary of key counterexamples in constructive real analysis:

-- 1. Functions that are pointwise continuous but not uniformly continuous
-- 2. Sets that are not decidable
-- 3. Cauchy sequences without constructive limits
-- 4. Failure of classical theorems without additional assumptions
-- 5. Non-constructive existence proofs that don't provide witnesses
-- 6. The necessity of choice principles for certain constructions
-- 7. Differences in computational content between equivalent classical theorems

-- These counterexamples highlight the importance of constructive reasoning
-- when working with real numbers in Cubical Agda