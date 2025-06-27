{-# OPTIONS --safe #-}
module Rome.Operational.Kinds.Decidability where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars


--------------------------------------------------------------------------------
-- Decidability of kind equality

_≡k?_ : ∀ (κ₁ κ₂ : Kind) → Dec (κ₁ ≡ κ₂)
★ ≡k? ★ = yes refl
★ ≡k? L = no (λ ())
★ ≡k? (κ₂ `→ κ₃) = no (λ ())
★ ≡k? R[ κ₂ ] = no (λ ())
L ≡k? ★ = no (λ ())
L ≡k? L = yes refl
L ≡k? (κ₂ `→ κ₃) = no (λ ())
L ≡k? R[ κ₂ ] = no (λ ())
(κ₁ `→ κ₂) ≡k? ★ = no (λ ())
(κ₁ `→ κ₂) ≡k? L = no (λ ())
(κ₁ `→ κ₂) ≡k? (κ₃ `→ κ₄) with κ₁ ≡k? κ₃ |  κ₂ ≡k? κ₄ 
... | yes refl | yes refl = yes refl
... | _ | no q = no (λ { refl → q refl })
... | no p | _ = no (λ { refl → p refl })
(κ₁ `→ κ₂) ≡k? R[ κ₃ ] = no (λ ())
R[ κ₁ ] ≡k? ★ = no (λ ())
R[ κ₁ ] ≡k? L = no (λ ())
R[ κ₁ ] ≡k? (κ₂ `→ κ₃) = no (λ ())
R[ κ₁ ] ≡k? R[ κ₂ ] = map′ (cong R[_]) (λ { refl → refl }) (κ₁ ≡k? κ₂)

--------------------------------------------------------------------------------
-- Decidability of variable equality

_≡var?_ : ∀ (x y : KVar Δ κ) → Dec (x ≡ y)
Z ≡var? Z = yes refl
Z ≡var? S y = no (λ ())
S x ≡var? Z = no (λ ()) 
S x ≡var? S y = map′ (cong S) (λ { refl → refl }) (x ≡var? y)
