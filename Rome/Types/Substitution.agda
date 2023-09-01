{-# OPTIONS --safe #-}
module Rome.Types.Substitution where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rome.Kinds
open import Rome.Types.Syntax

open import Data.Product hiding (Σ)

import Rome.Types.Pre as Pre
open Pre.Type
open Pre.Pred

open import Function
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
-- Pre-Renaming.

open import Data.Nat using (ℕ ; zero ; suc)

index = ℕ → ℕ
pre-τ-map = Pre.Type → Pre.Type
pre-π-map = Pre.Pred → Pre.Pred

ext : index → index
ext f zero = zero
ext f (suc n) = suc (f n)

pre-rename : index → Pre.Type → Pre.Type
pre-rename-π : index → Pre.Pred → Pre.Pred
pre-rename-π f (ρ₁ Pre.≲ ρ₂) = (pre-rename f ρ₁) ≲ ((pre-rename f ρ₂))
pre-rename-π f (ρ₁ Pre.· ρ₂ ~ ρ₃) = (pre-rename f ρ₁) · pre-rename f ρ₂ ~ (pre-rename f ρ₃)

pre-rename f U = U
pre-rename f (tvar x) = tvar (f x)
pre-rename f (τ `→ τ') = pre-rename f τ `→ pre-rename f τ'
pre-rename f (`∀ κ τ) = `∀ κ (pre-rename (ext f) τ) -- `∀ κ ((ext f) <$>τ τ) 
pre-rename f (`λ κ τ) = `λ κ (pre-rename (ext f) τ) -- `λ κ ((ext f) <$>τ τ)
pre-rename f (τ ·[ τ' ]) = (pre-rename f τ) ·[ pre-rename f τ' ]
pre-rename f (μ τ) = μ (pre-rename f τ)
pre-rename f (ν τ) = ν (pre-rename f τ)
pre-rename f (π ⦂ κ ⇒ τ) = (pre-rename-π f π) ⦂ κ ⇒ (pre-rename f τ) 
pre-rename f (lab x) = lab x
pre-rename f (τ ▹ τ') = (pre-rename f τ) ▹ (pre-rename f τ')
pre-rename f (τ R▹ τ') = (pre-rename f τ) R▹ (pre-rename f τ')
pre-rename f ⌊ τ ⌋ = ⌊ (pre-rename f τ) ⌋
pre-rename f ∅ = ∅
pre-rename f (Π τ) = Π (pre-rename f τ)
pre-rename f (Σ τ) = Σ (pre-rename f τ)
pre-rename f (τ ·⌈ τ' ⌉) = (pre-rename f τ) ·⌈ (pre-rename f τ') ⌉
pre-rename f (⌈ τ ⌉· τ') = ⌈ (pre-rename f τ) ⌉· (pre-rename f τ')


--------------------------------------------------------------------------------
-- Pre-substitution.

pre-context = ℕ → Pre.Type
ext-c : pre-context → pre-context
ext-c f zero = tvar zero
ext-c f (suc n) = pre-rename suc (f n)

pre-subst : pre-context → Pre.Type → Pre.Type
pre-subst-π : pre-context → Pre.Pred → Pre.Pred
pre-subst-π f (ρ₁ Pre.≲ ρ₂) = (pre-subst f ρ₁) ≲ ((pre-subst f ρ₂))
pre-subst-π f (ρ₁ Pre.· ρ₂ ~ ρ₃) = (pre-subst f ρ₁) · pre-subst f ρ₂ ~ (pre-subst f ρ₃)

pre-subst f U = U
pre-subst f (tvar x) = f x
pre-subst f (τ `→ τ') = pre-subst f τ `→ pre-subst f τ'
pre-subst f (`∀ κ τ) = `∀ κ (pre-subst (ext-c f) τ) -- `∀ κ ((ext f) <$>τ τ) 
pre-subst f (`λ κ τ) = `λ κ (pre-subst (ext-c f) τ) -- `λ κ ((ext f) <$>τ τ)
pre-subst f (τ ·[ τ' ]) = (pre-subst f τ) ·[ pre-subst f τ' ]
pre-subst f (μ τ) = μ (pre-subst f τ)
pre-subst f (ν τ) = ν (pre-subst f τ)
pre-subst f (π ⦂ κ ⇒ τ) = (pre-subst-π f π) ⦂ κ ⇒ (pre-subst f τ) 
pre-subst f (lab x) = lab x
pre-subst f (τ ▹ τ') = (pre-subst f τ) ▹ (pre-subst f τ')
pre-subst f (τ R▹ τ') = (pre-subst f τ) R▹ (pre-subst f τ')
pre-subst f ⌊ τ ⌋ = ⌊ (pre-subst f τ) ⌋
pre-subst f ∅ = ∅
pre-subst f (Π τ) = Π (pre-subst f τ)
pre-subst f (Σ τ) = Σ (pre-subst f τ)
pre-subst f (τ ·⌈ τ' ⌉) = (pre-subst f τ) ·⌈ (pre-subst f τ') ⌉
pre-subst f (⌈ τ ⌉· τ') = ⌈ (pre-subst f τ) ⌉· (pre-subst f τ')

--------------------------------------------------------------------------------
-- Defs & context invariance.
--
-- A Δ-map can be thought of as a "reindexing" of type variables:
--   if you give me a tvar in Δ with kind κ at index n,
--   I can give you a (reindexed) tvar in Δ₂ with kind Κ at index (f n),
--   with f : ℕ → ℕ the ℕ index.
Δ-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) (f : index) → Set
Δ-map Δ₁ Δ₂ f =
  (∀ {κ : Kind} {n} → TVar Δ₁ n κ → TVar Δ₂ (f n) κ)

-- Here be the main idea: context invariance over types.
--   give me a type in Δ₁ and I'll give you the same kinded type in Δ₂.
τ-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) (T : pre-τ-map) → Set
τ-map Δ₁ Δ₂ T = (∀ {κ : Kind}{τ : Pre.Type} → Type Δ₁ τ κ → Type Δ₂ (T τ) κ)

-- Context invariance over preds.
π-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) (P : pre-π-map) → Set
π-map Δ₁ Δ₂ P = ∀ {κ : Kind}{p : Pre.Pred} → Pred Δ₁ p κ → Pred Δ₂ (P p) κ

-- Some overloaded terminology: A *Context* here denotes not the kinding
-- environment but the mapping from tvars to types, i.e., a context in
-- type-level evaluation. Again we have a notion of "rebasing" from Δ₁ to Δ₂.
Context : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv)(c : pre-context) → Set
Context Δ₁ Δ₂ c = ∀ {κ : Kind}{n} → TVar Δ₁ n κ → Type Δ₂ (c n) κ 

--------------------------------------------------------------------------------
-- Δ-map extension.

-- IF I have a rebasing of tvars, I can extend each rebasing by kind ι.
ext-Δ : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} {ι : Kind} {f : index} →
         Δ-map Δ₁ Δ₂ f →
         Δ-map (Δ₁ , ι) (Δ₂ , ι) (ext f)
ext-Δ ρ Z     = Z
ext-Δ ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming lemma.
--
-- Aka, if I can rebase the tvars, then I can rebase the types,
-- where (in De Bruijn notation), *rebasing is renaming*.

rename : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : index) →
           Δ-map Δ₁ Δ₂ f →
           τ-map Δ₁ Δ₂ (pre-rename f)
renamePred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : index) →
           Δ-map Δ₁ Δ₂ f →
           π-map Δ₁ Δ₂ (pre-rename-π f)

rename f ρ (tvar n v) = tvar (f n) (ρ v)
rename f ρ (τ `→ υ) = rename f ρ τ `→ rename f ρ υ
rename f ρ (`∀ κ τ) = `∀ κ (rename (ext f) (ext-Δ ρ) τ)
rename f ρ (`λ s τ) = `λ s (rename (ext f) (ext-Δ ρ) τ)
rename f ρ (τ ·[ υ ]) = rename f ρ τ ·[ rename f ρ υ ]
rename f ρ U = U
rename f ρ (lab l) = lab l
rename f ρ (t ▹ v) = (rename f ρ t) ▹ (rename f ρ v)
rename f ρ (⌊ t ⌋) = ⌊ rename f ρ t ⌋
rename f ρ (t R▹ v) = rename f ρ t R▹ rename f ρ v
rename f ρ (Π r) = Π (rename f ρ r)
rename f ρ (Type.Σ r) = Type.Σ (rename f ρ r)
rename f ρ (π ⇒ τ) = renamePred f ρ π ⇒ rename f ρ τ
rename f ρ (r ·⌈ τ ⌉) =  (rename f ρ r)  ·⌈ (rename f ρ τ) ⌉
rename f ρ (⌈ τ ⌉· r) = ⌈ (rename f ρ τ) ⌉· (rename f ρ r)
rename f ρ (μ τ) = μ (rename f ρ τ)
rename f ρ (ν τ) = ν (rename f ρ τ)
rename f ρ ∅ = ∅

renamePred f ρ (ρ₁ ≲ ρ₂) = rename f ρ ρ₁ ≲ rename f ρ ρ₂
renamePred f ρ (ρ₁ · ρ₂ ~ ρ₃) = rename f ρ ρ₁ ·  rename f ρ ρ₂ ~ rename f ρ ρ₃

--------------------------------------------------------------------------------
-- Weakening.
--
weaken : ∀ {Δ : KEnv} {κ : Kind} →
           τ-map Δ (Δ , κ) (pre-rename suc)
weaken = rename suc S

-- -- --------------------------------------------------------------------------------
-- -- Context extension.
-- --

ext-Context : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv}
         {ι : Kind} (c : pre-context) →
         Context Δ₁ Δ₂ c →
         Context (Δ₁ , ι) (Δ₂ , ι) (ext-c c)
ext-Context c θ Z = tvar zero Z
ext-Context c θ (S n) = rename suc S (θ n)

--------------------------------------------------------------------------------
-- (Simultaneous) Substitution.
--
-- Substitution of *zero or more* type variables in types.

-- N.b. need to relate ℕ- and pre-contexts---may be as simple as indexing.
subst : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : index) (σ : pre-context) →
           Context Δ₁ Δ₂ σ →
           τ-map Δ₁ Δ₂ (pre-subst σ)

substPred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : index) (σ : pre-context) →
          Context Δ₁ Δ₂ σ →
          π-map Δ₁ Δ₂ (pre-subst-π σ)

subst f σ θ (tvar _ x) = θ x -- θ x
subst f σ θ (τ `→ υ) = subst f σ θ τ `→ subst f σ θ υ
subst f σ θ (`∀ κ τ) = `∀ κ (subst f (ext-c σ) (ext-Context σ θ) τ) 
subst f σ θ (`λ κ τ) = `λ κ (subst f (ext-c σ) (ext-Context σ θ) τ)
subst f σ θ (τ ·[ υ ]) = subst f σ θ τ ·[ subst f σ θ υ ]
subst f σ θ U = U
subst f σ θ (lab l) = lab l
subst f σ θ (t ▹ v) = (subst f σ θ t) ▹ (subst f σ θ v)
subst f σ θ (⌊ t ⌋) = ⌊ subst f σ θ t ⌋
subst f σ θ (t R▹ v) = subst f σ θ t R▹ subst f σ θ v
subst f σ θ (Π r) = Π (subst f σ θ r)
subst f σ θ (Type.Σ r) = Type.Σ (subst f σ θ r)
subst f σ θ (π ⇒ τ) = substPred f σ θ π ⇒ subst f σ θ τ
subst f σ θ ( r ·⌈ τ ⌉) = (subst f σ θ r) ·⌈ (subst f σ θ τ) ⌉
subst f σ θ ( ⌈ τ ⌉· r) = ⌈ (subst f σ θ τ) ⌉· (subst f σ θ r)
subst f σ θ (μ τ) = μ (subst f σ θ τ)
subst f σ θ (ν τ) = ν (subst f σ θ τ)
subst _ _ _ ∅ = ∅

substPred f σ θ (ρ₁ ≲ ρ₂)      = subst f σ θ ρ₁ ≲ subst f σ θ ρ₂
substPred f σ θ (ρ₁ · ρ₂ ~ ρ₃) = subst f σ θ ρ₁ ·  subst f σ θ ρ₂ ~ subst f σ θ ρ₃

--------------------------------------------------------------------------------
-- Single substitution.


pre-Z↦ : Pre.Type → pre-context
pre-Z↦ t zero    = t
pre-Z↦ t (suc n) = tvar n

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {Δ : KEnv} {κ : Kind} {τ} →
        Type Δ τ κ → Context (Δ , κ) Δ (pre-Z↦ τ)
Z↦ τ Z = τ
Z↦ τ (S {n = n} x) = tvar n x

-- Regular ol' substitution.
_β[_] : ∀ {Δ : KEnv} {κ : Kind}{ι : Kind} {τ υ}
         → Type (Δ , ι) τ κ → Type Δ υ ι → Type Δ (pre-subst (pre-Z↦ υ) τ) κ
τ β[ υ ] = subst id _ (Z↦ υ) τ
