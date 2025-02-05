module Rome.Presentation where

--------------------------------------------------------------------------------
-- #1 Motivation
-- 
-- In previous work (ICFP'23 and preprint) we have a denotational semantics of
-- Rω and Rωμ (Rω with recursive types).
--
-- This worked fine for the former but was painful for the latter. Let's look at
-- the denotation of recursive types.

import Rome.IndexCalculus.Recursion


-- Some problems with this approach:
-- 1. ugly
-- 2. Only permits a bounded depth n of recursive construction. When n ≥ 3 or so,
--    evaluation of terms grew Big O(fucking christ) in time.

--------------------------------------------------------------------------------
-- #2 An operational semantics
-- 
-- An operational semantics means we no longer denote recursive types into Agda
-- terms and hence do not run afoul of Agda's predicative universe hierarchy.
-- Pros:
--  - Above
--  - No more level annotations
--  - No more level annotations
--  - No more level annotations
-- Cons:
--  - Harder
--  - Duplication of syntax everywhere
--  - Duplication of renaming/substitution logic everywhere
--  - Must define substitution syntactically
--  - Renaming, renaming, renaming
-- In between:
--  - Forces us to be explicit about type normalization (This presentation)


--------------------------------------------------------------------------------
-- #3 On type normalization
--
-- Rω (as presented in ICFP'23) has an equivalence relation on types:

import Rome.Denotational.Equivalence.Syntax

-- which leads to rules for type conversion of terms, e.g. in

import Rome.Denotational.Terms.Syntax

-- we have:
--   t-≡ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
--           {τ υ : Type Δ (★ ℓ)}  →
-- 
--           τ ≡t υ → (M : Term Δ Φ Γ τ) →
--           ----------------------------
--           Term Δ Φ Γ υ

-- Cons:
--  - The "User" (or surface language translation) must construct proof terms of equality
--    (in many more places than perhaps expected).
--  - Characterization of types is strictly "larger" than necessary.
--
-- One way out of this pickle is to **normalize** types so that type conversion
-- is strictly unnecessary. We follow Chapman et al's System F in Agda, for Fun
-- and Profit in using **Normalizing types by evaluation**. Let's discuss
-- results before we discuss technique.

-- I have two main theorems (mostly) proven. Let's first look at the syntax of
-- types and normal types.

import Rome.Operational.Types.Syntax
import Rome.Operational.Types.Normal.Syntax

-- Now, theorems:
-- 1. Stability is a way of asserting that the normalization of types behaves
--    like a normalization function. (It should be idempotent and surjective.)
--    It also tells us that our characterization of normal forms is accurate.

import Rome.Operational.Types.Theorems.Stability

-- 2. Completeness tells us that the normalization algorithm respects the
--    declarative equivalence relation on types.

import Rome.Operational.Types.Theorems.Completeness

--------------------------------------------------------------------------------
-- #4 Proof technique: Normalization by evaluation
--

-- The trick to our normalization function is to "reflect" regular types into
-- "semantic" types. Namely, we reflect function types into Agda functions.

--  The goal is to use the semantic syntax as an intermediate stage between the two.
import Rome.Operational.Types.Semantic.Syntax

-- We use the latent computation in Agda to reduce function applications, then
-- "reify" semantic types into NormalTypes. 
import Rome.Operational.Types.Semantic.NBE

-- The challenges posed by Rωμ as opposed to SFFP is that we have more
-- "computation" than just beta reduction. In particular:
-- - Π and Σ has computation to perform
-- - Mapping (<$>) has computation to perform

--------------------------------------------------------------------------------
-- #5 Proof technique: Kripke logical relation
-- 
-- Our semantic space is "too large". In particular, the definition:
-- KripkeFunction : KEnv → Kind → Kind → Set
-- KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)
--
-- Includes functions that do *not* respect renaming. We call KripkeFunctions
-- that respect renaming "uniform".

open import Rome.Operational.Types.Theorems.Completeness.Relation

-- One way to think about this logical relation is that we are quotienting the
-- semantic type space by a partial equivalence relation (PER). (a PER is an
-- equivalence relation that is no reflexive.)  The relation is not reflexive
-- because uniformity is a unary predicate that does not hold for all
-- KripkeFunctions. That was the problem to begin with!
--
-- What we do next is reason modulo _≋_, knowing that the reification of related
-- semantic types yields the same normal types: 
--   reify-≋  : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → reify τ₁ ≡ reify τ₂ 

-- The lemmas needed to prove completeness and stability are fairly expansive,
-- but fall into broadly two categories: showing that semantic operators respect 
-- the PER, and showing that renaming commutes with semantic operators.
-- We will spend the rest of this presentation talking about this nonsense.

import Rome.Operational.Types.Theorems.Completeness.Congruence
import Rome.Operational.Types.Theorems.Completeness.Commutativity

-- Now let's go back and look at our proofs of completeness and stability and see
-- how the logical relation is employed.

import Rome.Operational.Types.Theorems.Stability
import Rome.Operational.Types.Theorems.Completeness
