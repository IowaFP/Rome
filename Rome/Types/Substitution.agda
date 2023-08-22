{-# OPTIONS --safe #-}
module Rome.Types.Substitution where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rome.Kinds
open import Rome.Types.Syntax

import Rome.Types.Pre as Pre
open Pre.Type

--------------------------------------------------------------------------------
-- TODO. Rewrite *all* of this. Doesn't need to be so spiffy. Just need
-- β-reduction & weakening.

-- _β[_] : ∀ {Δ : KEnv} {κ : Kind}{ι : Kind} {τ₁ τ₂ : Pre.Type}
--          → Type (Δ , ι) τ₁ κ → Type Δ ι → Type Δ κ
-- τ β[ υ ] = ?

weaken : ∀ {Δ} {τ} {ι κ} → Type Δ τ κ → Type (Δ , ι) τ κ
weaken τ = {!!}

-- --------------------------------------------------------------------------------
-- -- Defs.

-- -- A Δ-map (renaming) maps type vars in environment Δ₁ to environment Δ₂.
-- Δ-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
-- Δ-map Δ₁ Δ₂ =
--   (∀ {κ : Kind} → TVar Δ₁ κ → TVar Δ₂ κ)

-- -- A mapping from types to types.
-- τ-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
-- τ-map Δ₁ Δ₂ = (∀ {κ : Kind}{τ : Pre.Type} → Type Δ₁ τ κ → Type Δ₂ τ κ)

-- -- A mapping from preds to preds.
-- π-map : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
-- π-map Δ₁ Δ₂ = ∀ {κ : Kind}{p : Pre.Pred} → Pred Δ₁ p κ → Pred Δ₂ p κ

-- -- A Context maps type vars to types.
-- Context : ∀  (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
-- Context Δ₁ Δ₂ = ∀ {κ : Kind}{τ : Pre.Type} → TVar Δ₁ κ → Type Δ₂ τ κ

-- --------------------------------------------------------------------------------
-- -- Extension.
-- --
-- -- Given a map from variables in one Context to variables in another, extension
-- -- yields a map from the first Context extended to the second Context similarly
-- -- extended.

-- ext : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} {ι : Kind} →
--          Δ-map Δ₁ Δ₂ →
--          Δ-map (Δ₁ , ι) (Δ₂ , ι)
-- ext ρ Z     = Z
-- ext ρ (S x) = S (ρ x)

-- --------------------------------------------------------------------------------
-- -- Renaming.
-- --
-- -- Renaming is a necessary prelude to substitution, enabling us to “rebase” a
-- -- type from one Context to another.

-- rename : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
--            Δ-map Δ₁ Δ₂ →
--            τ-map Δ₁ Δ₂
-- renamePred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
--            Δ-map Δ₁ Δ₂ →
--            π-map Δ₁ Δ₂

-- rename ρ (tvar n v) = tvar n (ρ v)
-- rename ρ (τ `→ υ) = rename ρ τ `→ rename ρ υ
-- rename ρ (`∀ κ τ) = `∀ κ (rename (ext ρ) τ)
-- rename ρ (`λ s τ) = `λ s (rename (ext ρ) τ)
-- rename ρ (τ ·[ υ ]) = rename ρ τ ·[ rename ρ υ ]
-- rename ρ U = U
-- rename ρ (lab l) = lab l
-- rename ρ (t ▹ v) = (rename ρ t) ▹ (rename ρ v)
-- rename ρ (⌊ t ⌋) = ⌊ rename ρ t ⌋
-- rename ρ (t R▹ v) = rename ρ t R▹ rename ρ v
-- rename ρ (Π r) = Π (rename ρ r)
-- rename ρ (Type.Σ r) = Type.Σ (rename ρ r)
-- rename ρ (π ⇒ τ) = renamePred ρ π ⇒ rename ρ τ
-- rename ρ (r ·⌈ τ ⌉) =  (rename ρ r)  ·⌈ (rename ρ τ) ⌉
-- rename ρ (⌈ τ ⌉· r) = ⌈ (rename ρ τ) ⌉· (rename ρ r)
-- rename ρ (μ τ) = μ (rename ρ τ)
-- rename ρ (ν τ) = ν (rename ρ τ)
-- rename ρ ∅ = ∅

-- renamePred ρ (ρ₁ ≲ ρ₂) = rename ρ ρ₁ ≲ rename ρ ρ₂
-- renamePred ρ (ρ₁ · ρ₂ ~ ρ₃) = rename ρ ρ₁ ·  rename ρ ρ₂ ~ rename ρ ρ₃

-- --------------------------------------------------------------------------------
-- -- Weakening (of a typing derivation.)

-- weaken : ∀ {Δ : KEnv} {κ : Kind} →
--            τ-map Δ (Δ , κ)
-- weaken = rename S
           
-- --------------------------------------------------------------------------------
-- -- Simultaneous Substitution.
-- --
-- -- Instead of substituting a closed term for a single variable, we provide a
-- -- map that takes each free variable of the original type to another
-- -- tye. Further, the substituted terms are over an arbitrary Context, and need
-- -- not be closed.


-- exts : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv}
--          {ι : Kind} →
--          Context Δ₁ Δ₂ →
--          Context (Δ₁ , ι) (Δ₂ , ι) 
-- exts θ Z = tvar 0 Z
-- exts θ (S x) = rename S (θ x)

-- --------------------------------------------------------------------------------
-- -- Substitution.
-- --

-- subst : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
--            Context Δ₁ Δ₂ →
--            τ-map Δ₁ Δ₂

-- substPred : ∀  {Δ₁ : KEnv} {Δ₂ : KEnv} →
--           Context Δ₁ Δ₂ →
--           π-map Δ₁ Δ₂

-- subst θ (tvar x) = θ x
-- subst θ (τ `→ υ) = subst θ τ `→ subst θ υ
-- subst θ (`∀ κ τ) = `∀ κ (subst (exts θ) τ)
-- subst θ (`λ s τ) = `λ s (subst (exts θ) τ)
-- subst θ (τ ·[ υ ]) = subst θ τ ·[ subst θ υ ]
-- subst θ U = U
-- subst θ (lab l) = lab l
-- subst θ (t ▹ v) = (subst θ t) ▹ (subst θ v)
-- subst θ (⌊ t ⌋) = ⌊ subst θ t ⌋
-- subst θ (t R▹ v) = subst θ t R▹ subst θ v
-- subst θ (Π r) = Π (subst θ r)
-- subst θ (Type.Σ r) = Type.Σ (subst θ r)
-- subst θ (π ⇒ τ) = substPred θ π ⇒ subst θ τ
-- subst θ ( r ·⌈ τ ⌉) = (subst θ r) ·⌈ (subst θ τ) ⌉
-- subst θ ( ⌈ τ ⌉· r) = ⌈ (subst θ τ) ⌉· (subst θ r)
-- subst θ (μ τ) = μ (subst θ τ)
-- subst θ (ν τ) = ν (subst θ τ)
-- subst _ ∅ = ∅

-- substPred θ (ρ₁ ≲ ρ₂)      = subst θ ρ₁ ≲ subst θ ρ₂
-- substPred θ (ρ₁ · ρ₂ ~ ρ₃) = subst θ ρ₁ ·  subst θ ρ₂ ~ subst θ ρ₃

-- --------------------------------------------------------------------------------
-- -- Single substitution.

-- -- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
-- Z↦ : ∀ {Δ : KEnv} {κ : Kind} →
--         Type Δ κ → Context (Δ , κ) Δ
-- Z↦ τ Z = τ
-- Z↦ τ (S x) = tvar x

-- -- Regular ol' substitution.
-- _β[_] : ∀ {Δ : KEnv} {κ : Kind}{ι : Kind}
--          → Type (Δ , ι) κ → Type Δ ι → Type Δ κ
-- τ β[ υ ] = subst (Z↦ υ) τ

-- --------------------------------------------------------------------------------
-- -- examples, to move elsewhere

-- -- t0 : Type (ε , ★ lzero) (★ lzero)
-- -- t0 = tvar Z `→ tvar Z

-- -- _ : subst (Z↦ U) t0 ≡ U `→ U
-- -- _ = refl
