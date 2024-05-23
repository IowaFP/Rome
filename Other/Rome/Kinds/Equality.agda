module Rome.Kinds.Equality where

open import Rome.Kinds.Syntax

open import Preludes.Relation

--------------------------------------------------------------------------------
-- Decidability of kind equality.

_≡?_ : ∀ (κ₁ κ₂ : Kind) → Dec (κ₁ ≡ κ₂)
-- ≡? non-trivial.
★ ≡? ★ = yes refl
L ≡? L = yes refl
R[ κ₁ ] ≡? R[ κ₂ ] with κ₁ ≡? κ₂
... | yes refl = yes refl
... | no p  = no (λ { refl → p refl })
(κ₁ `→ κ₂) ≡? (κ₃ `→  κ₄)
  with  κ₁ ≡? κ₃ | κ₂ ≡? κ₄
... | yes refl | yes refl = yes refl
... | _ | no q = no (λ { refl → q refl })
... | no p | _ = no (λ { refl → p refl })
-- ≡? trivial.
★ ≡? L = no (λ ())
★ ≡? R[ κ₂ ] = no (λ ())
★ ≡? (x `→ κ₂) = no (λ ())
L ≡? ★ = no (λ ())
L ≡? R[ κ₂ ] = no (λ ())
L ≡? (x `→ κ₂) = no (λ ())
R[ κ₁ ] ≡? ★ = no (λ ())
R[ κ₁ ] ≡? L = no (λ ())
R[ κ₁ ] ≡? (x `→ κ₂) = no (λ ())
(x `→ κ₁) ≡? ★ = no (λ ())
(x `→ κ₁) ≡? L = no (λ ())
(x `→ κ₁) ≡? R[ κ₂ ] = no (λ ())
