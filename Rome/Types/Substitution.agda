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
-- Pre-Defs.

open import Data.Nat using (ℕ ; zero ; suc)
ℕ-map = ℕ → ℕ

_<$>τ_ : ∀ (f : ℕ-map) → Pre.Type → Pre.Type
_<$>π_ : ∀ (f : ℕ-map) → Pre.Pred → Pre.Pred

ℂ-map = ℕ → Pre.Type
-- ℂ-map f = (n : ℕ) → f <$>τ Σ[ g ∈ (ℕ → Pre.Type) ] (∀ n. g (f n) ≡ 

ext : ℕ-map → ℕ-map
ext f zero = zero
ext f (suc n) = suc (f n)

ext-c : ℂ-map → ℂ-map
ext-c f zero = tvar zero
ext-c f (suc n) = suc <$>τ (f n)

_<$>τ_ f U = U
_<$>τ_ f (tvar x) = tvar (f x)
_<$>τ_ f (τ `→ τ') = f <$>τ τ `→ f <$>τ τ'
_<$>τ_ f (`∀ κ τ) = `∀ κ ((ext f) <$>τ τ) 
_<$>τ_ f (`λ κ τ) = `λ κ ((ext f) <$>τ τ)
_<$>τ_ f (τ ·[ τ' ]) = (f <$>τ τ) ·[ f <$>τ τ' ]
_<$>τ_ f (μ τ) = μ (f <$>τ τ)
_<$>τ_ f (ν τ) = ν (f <$>τ τ)
_<$>τ_ f (π ⦂ κ ⇒ τ) = (f <$>π π) ⦂ κ ⇒ (f <$>τ τ) 
_<$>τ_ f (lab x) = lab x
_<$>τ_ f (τ ▹ τ') = (f <$>τ τ) ▹ (f <$>τ τ')
_<$>τ_ f (τ R▹ τ') = (f <$>τ τ) R▹ (f <$>τ τ')
_<$>τ_ f ⌊ τ ⌋ = ⌊ (f <$>τ τ) ⌋
_<$>τ_ f ∅ = ∅
_<$>τ_ f (Π τ) = Π (f <$>τ τ)
_<$>τ_ f (Σ τ) = Σ (f <$>τ τ)
_<$>τ_ f (τ ·⌈ τ' ⌉) = (f <$>τ τ) ·⌈ (f <$>τ τ') ⌉
_<$>τ_ f (⌈ τ ⌉· τ') = ⌈ (f <$>τ τ) ⌉· (f <$>τ τ')

f <$>π (ρ₁ Pre.≲ ρ₂) = (f <$>τ ρ₁) ≲ ((f <$>τ ρ₂))
f <$>π (ρ₁ Pre.· ρ₂ ~ ρ₃) = (f <$>τ ρ₁) · f <$>τ ρ₂ ~ (f <$>τ ρ₃)


--------------------------------------------------------------------------------
-- Defs.

-- -- A Δ-map maps type vars in environment Δ₁ to environment Δ₂.
-- -- (This is the De Bruijn equivalent of renaming variables.)
Δ-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) (f : ℕ-map) → Set
Δ-map Δ₁ Δ₂ f =
  (∀ {κ : Kind} {n} → TVar Δ₁ n κ → TVar Δ₂ (f n) κ)

-- -- A mapping from types to types.
τ-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) (f : ℕ-map) → Set
τ-map Δ₁ Δ₂ f = (∀ {κ : Kind}{τ : Pre.Type} → Type Δ₁ τ κ → Type Δ₂ (f <$>τ τ) κ)

-- -- A mapping from preds to preds.
π-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) (f : ℕ-map) → Set
π-map Δ₁ Δ₂ f = ∀ {κ : Kind}{p : Pre.Pred} → Pred Δ₁ p κ → Pred Δ₂ (f <$>π p) κ

-- A Context maps type vars to types.
Context : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv)(c : ℂ-map) → Set
Context Δ₁ Δ₂ c = ∀ {κ : Kind}{n} → TVar Δ₁ n κ → Type Δ₂ (c n) κ 


--------------------------------------------------------------------------------
-- Δ-map extension.


ext-Δ : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} {ι : Kind} {f : ℕ-map} →
         Δ-map Δ₁ Δ₂ f →
         Δ-map (Δ₁ , ι) (Δ₂ , ι) (ext f)
ext-Δ ρ Z     = Z
ext-Δ ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming.
--
-- Renaming lifts a Δ-map (which renames type vars) to a τ-map (which renames
-- type vars in types.)

rename : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : ℕ-map) →
           Δ-map Δ₁ Δ₂ f →
           τ-map Δ₁ Δ₂ f
renamePred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : ℕ-map) →
           Δ-map Δ₁ Δ₂ f →
           π-map Δ₁ Δ₂ f

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

-- --------------------------------------------------------------------------------
-- -- Weakening (of a typing derivation.)

weaken : ∀ {Δ : KEnv} {κ : Kind} →
           τ-map Δ (Δ , κ) suc
weaken = rename suc S

-- --------------------------------------------------------------------------------
-- -- Context extension.
-- --

ext-Context : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv}
         {ι : Kind} (c : ℂ-map) →
         Context Δ₁ Δ₂ c →
         Context (Δ₁ , ι) (Δ₂ , ι) (ext-c c)
ext-Context c θ Z = tvar zero Z
ext-Context c θ (S n) = rename suc S (θ n)

-- --------------------------------------------------------------------------------
-- -- (Simultaneous) Substitution.
-- --
-- -- Substitution of *zero or more* type variables in types.

-- N.b. need to relate ℕ- and ℂ-maps---may be as simple as indexing.
-- subst : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : ℕ-map) (c : ℂ-map) →
--            Context Δ₁ Δ₂ c →
--            τ-map Δ₁ Δ₂ f

-- substPred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} (f : ℕ-map) (c : ℂ-map) →
--           Context Δ₁ Δ₂ c →
--           π-map Δ₁ Δ₂ f

-- subst f c θ (tvar _ x) = ? -- θ x
-- subst f c θ (τ `→ υ) = subst f c θ τ `→ subst f c θ υ
-- subst f c θ (`∀ κ τ) = `∀ κ (subst (ext-Context f c θ) τ)
-- subst f c θ (`λ s τ) = `λ s (subst (ext-Context f c θ) τ)
-- subst f c θ (τ ·[ υ ]) = subst f c θ τ ·[ subst f c θ υ ]
-- subst f c θ U = U
-- subst f c θ (lab l) = lab l
-- subst f c θ (t ▹ v) = (subst f c θ t) ▹ (subst f c θ v)
-- subst f c θ (⌊ t ⌋) = ⌊ subst f c θ t ⌋
-- subst f c θ (t R▹ v) = subst f c θ t R▹ subst f c θ v
-- subst f c θ (Π r) = Π (subst f c θ r)
-- subst f c θ (Type.Σ r) = Type.Σ (subst f c θ r)
-- subst f c θ (π ⇒ τ) = substPred f c θ π ⇒ subst f c θ τ
-- subst f c θ ( r ·⌈ τ ⌉) = (subst f c θ r) ·⌈ (subst f c θ τ) ⌉
-- subst f c θ ( ⌈ τ ⌉· r) = ⌈ (subst f c θ τ) ⌉· (subst f c θ r)
-- subst f c θ (μ τ) = μ (subst f c θ τ)
-- subst f c θ (ν τ) = ν (subst f c θ τ)
-- subst _ ∅ = ∅

-- substPred f c θ (ρ₁ ≲ ρ₂)      = subst f c θ ρ₁ ≲ subst f c θ ρ₂
-- substPred f c θ (ρ₁ · ρ₂ ~ ρ₃) = subst f c θ ρ₁ ·  subst f c θ ρ₂ ~ subst f c θ ρ₃

-- --------------------------------------------------------------------------------
-- -- Single substitution.

-- -- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
-- -- Z↦ : ∀ {Δ : KEnv} {κ : Kind} →
-- --         Type Δ κ → Context (Δ , κ) Δ
-- -- Z↦ τ Z = τ
-- -- Z↦ τ (S x) = tvar x

-- -- -- Regular ol' substitution.
-- -- _β[_] : ∀ {Δ : KEnv} {κ : Kind}{ι : Kind}
-- --          → Type (Δ , ι) κ → Type Δ ι → Type Δ κ
-- -- τ β[ υ ] = subst (Z↦ υ) τ

-- --------------------------------------------------------------------------------
-- -- examples, to move elsewhere

-- -- t0 : Type (ε , ★ lzero) (★ lzero)
-- -- t0 = tvar Z `→ tvar Z

-- -- _ : subst (Z↦ U) t0 ≡ U `→ U
-- -- _ = refl
