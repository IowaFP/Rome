module Rome.Kinds.Equality where

open import Rome.Kinds.Syntax

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

--------------------------------------------------------------------------------
-- Decidability of kind equality.

_≡?_ : ∀ (κ₁ κ₂ : Kind) → Dec (κ₁ ≡ κ₂)
_≡¹?_ : ∀ {κ} (κ₁ κ₂ : Kind¹ κ) → Dec (κ₁ ≡ κ₂)
_≡¹?_ {κ} κ₁ κ₂ with κ ≡? κ 
_≡¹?_ {★} ★¹ ★¹ | yes refl = yes refl
_≡¹?_ {L} L¹ L¹ | yes refl = yes refl
_≡¹?_ {x `→ κ} () κ₂ | yes refl 
_≡¹?_ {R[ κ ]} R₁[ κ₁ ] R₁[ κ₂ ] | yes refl with κ₁ ≡¹? κ₂
... | yes refl = yes refl
... | no p     = no (λ {refl → p refl })
_≡¹?_ _ _ | no p = no (λ _ → p refl)

-- ≡? non-trivial.
★ ≡? ★ = yes refl
L ≡? L = yes refl
R[ κ₁ ] ≡? R[ κ₂ ] with κ₁ ≡? κ₂
... | yes refl = yes refl
... | no p  = no (λ { refl → p refl })
(_`→_ {κ₁} κ₁¹ κ₂) ≡? _`→_ {κ₃} κ₃¹ κ₄
  with  κ₁ ≡? κ₃ | κ₂ ≡? κ₄
... | yes refl | no q = no (λ { refl → q refl })
... | no p | yes refl = no (λ { refl → p refl })
... | no p | no q = no λ { refl → p refl }
... | yes refl | yes refl with κ₁¹ ≡¹? κ₃¹
...   | yes refl = yes refl
...   | no p = no (λ { refl → p refl })
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
