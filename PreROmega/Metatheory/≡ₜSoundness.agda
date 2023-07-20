module PreROmega.Metatheory.≡ₜSoundness where

open import Data.String using (String; _≟_)
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List 
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
import Relation.Binary.PropositionalEquality as Eq  

open import Function using (_∘_)

open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

import PreROmega.Lib.Biimplication as Bi
import PreROmega.IndexCalculus

open Bi
  using (_⇔_)
  renaming (Equivalence to E)

open import PreROmega.Lib.AssocList
open import PreROmega.Lang.Syntax
open import PreROmega.Lang.Typing

--------------------------------------------------------------------------------
-- Formal Properties of the Static Semantics:
-- soundness of typing equivalence.

--------------------------------------------------------------------------------
-- Weakening
-- TODO

--------------------------------------------------------------------------------
-- Type substitution

-- N.B. Not sure if this is totally correctly phrased. The chain (I think), is
--   weakening → typeSubstitution → ·ₜclosure → ≡ₜclosure
-- Specifically, we need all this mumbo jumbo so we can assert that the computation
-- we do in ≡ₜ (type-level substitution) is valid.
--
-- That being said. I think something about this may still be set up completely
-- wrong.
typeSubstitution1 : ∀ {Γ a t v k₁ k₂} →
                    ((a ⦂ₖ k₁) ∷ Γ) ⊢ₖ t ⦂ k₂   →   Γ ⊢ₖ v ⦂ k₁ →
                    ---------------------------------------------
                                 Γ ⊢ₖ (t ^ₜ v) ⦂ k₂
-- I think I need weakening here.                                 
typeSubstitution1 t⦂k₂ v⦂k₁ = {!!}

--------------------------------------------------------------------------------
-- Preservation under (type-level) reduction
·preservation : ∀ {Γ k k'} → ∀ t v →
          Γ ⊢ₖ `λ k' t · v ⦂ k →
          Γ ⊢ₖ t ^ₜ v ⦂ k
-- I need to prove here that opening `t` with *any* v preserves kind k.  We
-- define substitution τ[v/x] as opening τ with v. But then many of our typing
-- judgments are defined by opening with a free variable.
--
-- I need to revisit Metalib & Charguérard to see if this is right.
·preservation = {!!}
  -- {Γ} {k} {k'} t v
  -- (k-→E (k-→I _ _ _ _ L₁ cofinite) v⦂k') = {!!} -- typeSubstitution1 {Γ} {fresh L₁} {t} {v} {k} {!!} {!!}
-- ·preservation t v (⊢ₖlift₂ d d₁) = {!!}
                 
--------------------------------------------------------------------------------
--
-- Preservation under Equivalence


≡ₜpreservation : ∀ {Γ t₁ t₂ k} →
  t₁ ≡ₜ t₂ →
  Γ ⊢ₖ t₁ ⦂ k ⇔ Γ ⊢ₖ t₂ ⦂ k
≡ₜpreservation (≡ₜrefl _) = Bi.refl
≡ₜpreservation (≡ₜsym t₂≡ₜt₁) = Bi.sym (≡ₜpreservation t₂≡ₜt₁)
≡ₜpreservation (≡ₜtrans t₁≡ₜt₂ t₂≡ₜt₃) = Bi.trans (≡ₜpreservation t₁≡ₜt₂)  (≡ₜpreservation t₂≡ₜt₃)
≡ₜpreservation (≡ₜ⇒ p₁ p₂ t₁ t₂ p₁≡πp₂ t₁≡ₜt₂) = {!!}
≡ₜpreservation (≡ₜ∀ L₁ k t v x) = {!!}
≡ₜpreservation {Γ} {k = k} (≡ₜλ L₁ k₁ t v a a∉L) =
  record { to = to ; from = from }
  where
  to : Γ ⊢ₖ `λ k₁ t · v ⦂ k → Γ ⊢ₖ t ^ₜ v ⦂ k
  to = ·preservation t v

  -- My spideysenses sense this may be problematic. It may be helpful to return
  -- to Charguérard, where we define both opening a term and closing it, which
  -- are inverse.
  from : Γ ⊢ₖ t ^ₜ v ⦂ k → Γ ⊢ₖ `λ k₁ t · v ⦂ k
  from c = {!!}
≡ₜpreservation {Γ} .{t₁ · t₂} .{v₁ · v₂} {k} tᵢ≡ₜvᵢ@(≡ₜ· t₁ t₂  v₁ v₂ t₁≡ₜv₁ t₂≡ₜv₂) =
  record { to = to ; from = from }
  where
    to : Γ ⊢ₖ t₁ · t₂ ⦂ k → Γ ⊢ₖ v₁ · v₂ ⦂ k
    to (k-→E {k₁ = k₁} t₁⦂k₁→k t₂⦂k₁) = k-→E (E.to (≡ₜpreservation t₁≡ₜv₁) t₁⦂k₁→k) (E.to (≡ₜpreservation t₂≡ₜv₂) t₂⦂k₁)
    to (k-lift₁ {k₁ = k₁} {k₂ = k₂} t₁⦂R[k₁→k] t₂⦂k₁) = k-lift₁ ((E.to (≡ₜpreservation t₁≡ₜv₁) t₁⦂R[k₁→k])) (E.to (≡ₜpreservation t₂≡ₜv₂) t₂⦂k₁)
    to (k-lift₂ {k₁ = k₁} {k₂ = k₂} t₂⦂k₁ t₁⦂R[k₁→k]) = k-lift₂ (E.to (≡ₜpreservation t₂≡ₜv₂) t₂⦂k₁) ((E.to (≡ₜpreservation t₁≡ₜv₁) t₁⦂R[k₁→k])) 
    
    from : Γ ⊢ₖ v₁ · v₂ ⦂ k → Γ ⊢ₖ t₁ · t₂ ⦂ k
    from (k-→E {k₁ = k₁} v₁⦂k₁→k v₂⦂k₁) = k-→E (E.from (≡ₜpreservation t₁≡ₜv₁) v₁⦂k₁→k) (E.from (≡ₜpreservation t₂≡ₜv₂) v₂⦂k₁)
    from (k-lift₁ {k₁ = k₁} {k₂ = k₂} v₁⦂R[k₁→k] v₂⦂k₁) = k-lift₁ ((E.from (≡ₜpreservation t₁≡ₜv₁) v₁⦂R[k₁→k])) (E.from (≡ₜpreservation t₂≡ₜv₂) v₂⦂k₁)
    from (k-lift₂ {k₁ = k₁} {k₂ = k₂} v₂⦂k₁ v₁⦂R[k₁→k]) = k-lift₂ (E.from (≡ₜpreservation t₂≡ₜv₂) v₂⦂k₁) ((E.from (≡ₜpreservation t₁≡ₜv₁) v₁⦂R[k₁→k])) 
≡ₜpreservation (≡ₜ▹ t₁ t₂ v₁ v₂ t₁≡ₜt₂ t₁≡ₜt₃) = {!!}
≡ₜpreservation (≡ₜlift1 t₁ t₂ v) = {!!}
≡ₜpreservation (≡ₜlift2 t₁ t₂ v) = {!!}
≡ₜpreservation (≡ₜΠ z₁ z₂ t₁≡ₜt₂) = {!!}
≡ₜpreservation (≡ₜΣ z₁ z₂ t₁≡ₜt₂) = {!!}
≡ₜpreservation (≡ₜΠ▹ t₁ t₂) = {!!}
≡ₜpreservation (≡ₜΣ▹ t₁ t₂) = {!!}
