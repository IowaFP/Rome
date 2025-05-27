open import Rome.Preludes.Data hiding (∃)

module Rome.Denotational.Types.Semantics (g : Potatoes) where

open import Rome.Preludes.Level
open import Rome.Preludes.Relation

open import Rome.Denotational.GVars.Kinds

open import Rome.Shared.Postulates.FunExt

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types.Syntax
open import Rome.Denotational.Types.Admissible
open import Rome.Denotational.Types.Substitution

import Rome.IndexCalculus as Ix

open import Data.Empty.Polymorphic
open import Data.Product renaming (Σ to ∃) hiding (∃)

--------------------------------------------------------------------------------
-- The meaning of kinding environments and predicates (mutually recursive).

⟦_⟧t : Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦_⟧Row : Row Δ κ → ⟦ Δ ⟧ke → Ix.Row ⟦ κ ⟧k
⟦_⟧p : {κ : Kind ℓκ} → Pred Δ κ → ⟦ Δ ⟧ke → Set (lsuc ℓκ)

⟦ l ▹ τ ⟧Row H = Ix.sing (l , (⟦ τ ⟧t H))
⟦ (l ▹ τ ， ρ) ⟧Row H = (l , (⟦ τ ⟧t H)) Ix.፦ (⟦ ρ ⟧Row H)

⟦ ρ₁ ≲ ρ₂ ⟧p H = ⟦ ρ₁ ⟧t H Ix.≲ ⟦ ρ₂ ⟧t H
⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧p H = Ix._·_~_ (⟦ ρ₁ ⟧t H) (⟦ ρ₂ ⟧t H) (⟦ ρ₃ ⟧t H)

--------------------------------------------------------------------------------
-- The meaning of type vars.

⟦_⟧tv : TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

--------------------------------------------------------------------------------
-- The meaning of types.

buildΣ : ∀ {ι} → (κ : Kind ι) → ⟦ R[ κ ] ⟧k → ⟦ κ ⟧k
buildΣ (★ _) ⟦ρ⟧ = Ix.Σ ⟦ρ⟧
buildΣ (κ₁ `→ κ₂) (n , f) = {!!} -- λ X → buildΣ κ₂ (n , λ i → f i X)
buildΣ (L _) (n , P) = {!!}
buildΣ R[ κ ] (n , f) = n , {!!} -- λ i → buildΣ κ (f i)

buildΠ : ∀ {ι} → (κ : Kind ι) → ⟦ R[ κ ] ⟧k → ⟦ κ ⟧k
buildΠ (★ _) ⟦ρ⟧ = Ix.Π ⟦ρ⟧
buildΠ (κ₁ `→ κ₂) (n , f) = λ X → {!!} -- buildΠ κ₂ (n , λ i → f i X)
buildΠ (L _) ⟦ρ⟧ = {!!} -- tt
buildΠ R[ κ ] (n , f) = {!!} -- n , λ i → buildΠ κ (f i)

⟦ lab l ⟧t       H = str l
⟦_⟧t {κ = κ} (tvar v) H = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H = Maybe (⟦ t₁ ⟧t H) → Maybe (⟦ t₂ ⟧t H)
⟦ `∀ κ v ⟧t      H = (s : ⟦ κ ⟧k) → Maybe (⟦ v ⟧t  (H , s))
⟦ t₁ ·[ t₂ ] ⟧t  H = (⟦ t₁ ⟧t H) (⟦ t₂ ⟧t H)
⟦ `λ κ v ⟧t     H =  λ (s : ⟦ κ ⟧k) → ⟦ v ⟧t (H , s)
⟦ _ ▹ v ⟧t       H = ⟦ v ⟧t H
⟦ l R▹ τ ⟧t H = {!Ix.sing ( ⟦ l ⟧t H , ⟦ τ ⟧t H)!} -- Ix.sing (⟦ τ ⟧t H)
⟦ ⌊ τ ⌋ ⟧t H       = ⊤
⟦ Π {κ = κ} ρ ⟧t H = buildΠ κ (⟦ ρ ⟧t H)
⟦ Σ {κ = κ} ρ ⟧t H = buildΣ κ (⟦ ρ ⟧t H)
⟦ ↑ ϕ ⟧t H = Ix.lift₁ (⟦ ϕ ⟧t H)
⟦ ϕ ↑ ⟧t H = Ix.lift₂ (⟦ ϕ ⟧t H)
⟦ π ⇒ τ ⟧t H = ⟦ π ⟧p H → Maybe (⟦ τ ⟧t H)
⟦ ε ⟧t H = Ix.emptyRow
⟦ ⦃- ρ -⦄ ⟧t H = ⟦ ρ ⟧Row H
⟦ μ {ℓ = ℓ} F ⟧t H = Ix.Mu (⟦ F ⟧t H) g
