{-# OPTIONS --safe #-}
module Rome.Types.Substitution where

open import Preludes.Relation
open import Preludes.Data

open import Rome.Kinds
open import Rome.Types.Syntax
import Rome.Pre.Types as Pre

open Pre.Type
open Pre.Pred

--------------------------------------------------------------------------------
-- Substitution & Weakening.
--
-- We follow the approach of Wadler, Kokke, and Siek.
-- https://plfa.github.io/DeBruijn/
--
-- As we are substituting over *intrinsically kinded types*, there is no
-- separation of substitution/weakening *logic* and substitution/weakening
-- *theory*. That is to say, the code is metatheory and vice versa.

--------------------------------------------------------------------------------
-- The general idea.
--
-- If we try implement a weakening lemma directly,
-- we will get stuck here:
--     weaken :∀ Δ κ τ →  Type Δ τ κ → Type (Δ , ι) τ κ
--     weaken (`∀ k t) = ?
-- as our IH is restricted to a specific Δ, whereas we need to induct
-- on (Δ , k), given that the subdata t has type Type (Δ , k) τ' κ'.
--
-- We generalize Δ by establishing a notion of *context invariant maps* (denoted
-- `τ-map`s), which are a mapping of type variables from KEnv Δ₁ to Δ₂ such that
-- all well kinded types τ in Δ₁ are also well-kinded in Δ₂. You may also think
-- of this operation as "rebasing" a type in one environment to another.

--------------------------------------------------------------------------------
-- Defs & context invariance.
--
-- A Δ-map can be thought of as a "reindexing" of type variables:
--   if you give me a tvar in Δ with kind κ at index n,
--   I can give you a (reindexed) tvar in Δ₂ with kind Κ at index (f n),
--   with f : ℕ → ℕ the ℕ index.
Δ-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
Δ-map Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → TVar Δ₂ κ

-- Here be the main idea: context invariance over types.
--   give me a type in Δ₁ and I'll give you the same kinded type in Δ₂.
τ-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
τ-map Δ₁ Δ₂ = (∀ {κ : Kind} → Type Δ₁ κ → Type Δ₂ κ)

-- Context invariance over preds.
π-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
π-map Δ₁ Δ₂ = ∀ {κ : Kind} → Pred Δ₁ κ → Pred Δ₂ κ

-- Some overloaded terminology: A *Context* here denotes not the kinding
-- environment but the mapping from tvars to types, i.e., a context in
-- type-level evaluation. Again we have a notion of "rebasing" from Δ₁ to Δ₂.
Context : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
Context Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → Type Δ₂ κ 

--------------------------------------------------------------------------------
-- Δ-map extension.

-- IF I have a rebasing of tvars, I can extend each rebasing by kind ι.
ext-Δ : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} {ι : Kind} →
         Δ-map Δ₁ Δ₂ →
         Δ-map (Δ₁ , ι) (Δ₂ , ι)
ext-Δ ρ Z     = Z
ext-Δ ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming lemma.
--
-- Aka, if I can rebase the tvars, then I can rebase the types,
-- where (in De Bruijn notation), *rebasing is renaming*.

rename : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Δ-map Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂
renamePred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Δ-map Δ₁ Δ₂ →
           π-map Δ₁ Δ₂

rename ρ (tvar v) = tvar (ρ v)
rename ρ (τ `→ υ) = rename ρ τ `→ rename ρ υ
rename ρ (`∀ κ τ) = `∀ κ (rename (ext-Δ ρ) τ)
rename ρ (`λ s τ) = `λ s (rename (ext-Δ ρ) τ)
rename ρ (τ ·[ υ ]) = rename ρ τ ·[ rename ρ υ ]
rename ρ U = U
rename ρ (lab l) = lab l
rename ρ (t ▹ v) = (rename ρ t) ▹ (rename ρ v)
rename ρ (⌊ t ⌋) = ⌊ rename ρ t ⌋
rename ρ (t R▹ v) = rename ρ t R▹ rename ρ v
rename ρ (Π r) = Π (rename ρ r)
rename ρ (Type.Σ r) = Type.Σ (rename ρ r)
rename ρ (π ⇒ τ) = renamePred ρ π ⇒ rename ρ τ
rename ρ (r ·⌈ τ ⌉) =  (rename ρ r)  ·⌈ (rename ρ τ) ⌉
rename ρ (⌈ τ ⌉· r) = ⌈ (rename ρ τ) ⌉· (rename ρ r)
rename ρ (μ τ) = μ (rename ρ τ)
rename ρ (ν τ) = ν (rename ρ τ)
rename ρ ∅ = ∅

renamePred ρ (ρ₁ ≲ ρ₂) = rename ρ ρ₁ ≲ rename ρ ρ₂
renamePred ρ (ρ₁ · ρ₂ ~ ρ₃) = rename ρ ρ₁ ·  rename ρ ρ₂ ~ rename ρ ρ₃

--------------------------------------------------------------------------------
-- Weakening.
--
weaken : ∀ {Δ : KEnv} {κ : Kind} →
           τ-map Δ (Δ , κ)
weaken = rename S

-- -- --------------------------------------------------------------------------------
-- -- Context extension.
-- --

ext-Context : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv}
         {ι : Kind} →
         Context Δ₁ Δ₂ →
         Context (Δ₁ , ι) (Δ₂ , ι)
ext-Context θ Z = tvar Z
ext-Context θ (S n) = rename S (θ n)

--------------------------------------------------------------------------------
-- (Simultaneous) Substitution.
--
-- Substitution of *zero or more* type variables in types.

-- N.b. need to relate ℕ- and Pre.contexts---may be as simple as indexing.
subst : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv}  →
           Context Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂

substPred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
          Context Δ₁ Δ₂ →
          π-map Δ₁ Δ₂

subst θ (tvar x) = θ x -- θ x
subst θ (τ `→ υ) = subst θ τ `→ subst θ υ
subst θ (`∀ κ τ) = `∀ κ (subst (ext-Context θ) τ) 
subst θ (`λ κ τ) = `λ κ (subst  (ext-Context θ) τ)
subst θ (τ ·[ υ ]) = subst θ τ ·[ subst θ υ ]
subst θ U = U
subst θ (lab l) = lab l
subst θ (t ▹ v) = (subst θ t) ▹ (subst θ v)
subst θ (⌊ t ⌋) = ⌊ subst θ t ⌋
subst θ (t R▹ v) = subst θ t R▹ subst θ v
subst θ (Π r) = Π (subst θ r)
subst θ (Type.Σ r) = Type.Σ (subst θ r)
subst θ (π ⇒ τ) = substPred θ π ⇒ subst θ τ
subst θ ( r ·⌈ τ ⌉) = (subst θ r) ·⌈ (subst θ τ) ⌉
subst θ ( ⌈ τ ⌉· r) = ⌈ (subst θ τ) ⌉· (subst θ r)
subst θ (μ τ) = μ (subst θ τ)
subst θ (ν τ) = ν (subst θ τ)
subst _ ∅ = ∅

substPred θ (ρ₁ ≲ ρ₂)      = subst θ ρ₁ ≲ subst θ ρ₂
substPred θ (ρ₁ · ρ₂ ~ ρ₃) = subst θ ρ₁ ·  subst θ ρ₂ ~ subst θ ρ₃

--------------------------------------------------------------------------------
-- Single substitution.

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {Δ : KEnv} {κ : Kind} →
        Type Δ κ → Context (Δ , κ) Δ
Z↦ τ Z = τ
Z↦ τ (S x) = tvar x

-- Regular ol' bet'r red'uction.
_β[_] : ∀ {Δ : KEnv} {κ : Kind}{ι : Kind}
         → Type (Δ , ι) κ → Type Δ ι → Type Δ κ
τ β[ υ ] = subst (Z↦ υ) τ
