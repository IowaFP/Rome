{-# OPTIONS --safe #-}
module Rome.Types.Normal.Properties.Decidability where 

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars
open import Rome.Kinds.Decidability

open import Rome.Types.Syntax
open import Rome.Types.Substitution

open import Rome.Types.Equivalence.Relation

open import Rome.Types.Normal.Syntax
open import Rome.Types.Normal.Renaming
open import Rome.Types.Semantic.NBE

open import Rome.Types.Theorems.Stability
open import Rome.Types.Theorems.Soundness
open import Rome.Types.Theorems.Consistency

open import Data.String.Properties using (_≟_)

--------------------------------------------------------------------------------
-- Decidability of NeutralType equality

_≡NE?_ : ∀ (τ₁ τ₂ : NeutralType Δ κ) → Dec (τ₁ ≡ τ₂) 
_≡?_ : ∀ (τ₁ τ₂ : NormalType Δ κ) → Dec (τ₁ ≡ τ₂)
_≡p?_ : ∀ (π₁ π₂ : NormalPred Δ R[ κ ]) → Dec (π₁ ≡ π₂)
_≡Row?_ : ∀ (ρ₁ ρ₂ : SimpleRow NormalType Δ R[ κ ]) → Dec (ρ₁ ≡ ρ₂)

[] ≡Row? [] = yes refl
[] ≡Row? (x ∷ ρ₂) = no (λ ())
(x ∷ ρ₁) ≡Row? [] = no (λ ())
((l₁ , τ₁) ∷ ρ₁) ≡Row? ((l₂ , τ₂) ∷ ρ₂) with l₁ ≟ l₂ | τ₁ ≡? τ₂ | ρ₁ ≡Row? ρ₂ 
... | yes refl | yes refl | yes refl = yes refl
... | yes p | no q  | yes r = no (λ { refl → q refl })
... | yes p | yes q | no  r = no (λ { refl → r refl })
... | yes p | no q  | no  r = no (λ { refl → q refl })
... | no  p | yes q | yes r = no (λ { refl → p refl })
... | no  p | no  q | yes r = no (λ { refl → q refl })
... | no  p | yes q | no  r = no (λ { refl → r refl })
... | no  p | no  q | no  r = no (λ { refl → q refl })

` x ≡NE? ` y with x ≡var? y 
... | yes refl = yes refl 
... | no  p = no (λ { refl → p refl }) 
` x ≡NE? (d · τ) = no (λ ())
(x · τ) ≡NE? ` α = no (λ ())
(_·_ {κ₁} x τ₁) ≡NE? (_·_ {κ₂} y τ₂) with κ₁ ≡k? κ₂ 
... | no  q = no (λ { refl → q refl })
... | yes refl with x ≡NE? y | τ₁ ≡? τ₂ 
... | yes refl | yes refl = yes refl
... | _ | no q = no (λ { refl → q refl })
... | no p  | _ = no (λ { refl → p refl })

--------------------------------------------------------------------------------
-- Decidability of NormalPred equality

(ρ₁ ≲ ρ₂) ≡p? (ρ₃ ≲ ρ₄) with ρ₁ ≡? ρ₃ 
... | yes refl = map′ (cong (ρ₁ ≲_)) (λ { refl → refl })  (ρ₂ ≡? ρ₄)
... | no  p = no (λ { refl → p refl })
(ρ₁ · ρ₂ ~ ρ₃) ≡p? (ρ₄ · ρ₅ ~ ρ₆) with ρ₁ ≡? ρ₄
... | no  p = no (λ { refl → p refl })
... | yes refl with ρ₂ ≡? ρ₅ 
...            | yes refl = map′ (cong (ρ₁ · ρ₂ ~_)) (λ { refl → refl })  (ρ₃ ≡? ρ₆)
...            | no p = no (λ { refl → p refl })
(ρ₁ · ρ₂ ~ ρ₃) ≡p? (ρ₄ ≲ ρ₅) = no (λ ())
(ρ₁ ≲ ρ₂) ≡p? (ρ₃ · ρ₄ ~ ρ₅) = no (λ ())

--------------------------------------------------------------------------------
-- Decidability of NormalType equality

-- meaningful cases first
_≡?_ {κ = ★} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
_≡?_ {κ = L} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
(_<$>_ {κ₁} f x) ≡? (_<$>_ {κ₂} g y) with κ₁ ≡k? κ₂ 
... | no  q = no (λ { refl → q refl })
... | yes refl with f ≡? g | x ≡NE? y
... | yes refl | yes refl = yes refl
... | _ | no q = no (λ { refl → q refl })
... | no p  | _ = no (λ { refl → p refl })
`λ τ₁ ≡? `λ τ₂ = map′ (cong `λ) (λ { refl → refl }) (τ₁ ≡? τ₂)
μ τ₁ ≡? μ τ₂ = map′ (cong μ) (λ { refl → refl})  (τ₁ ≡? τ₂)
(_⇒_ {κ₁ = κ₁} π₁ τ₁) ≡? (_⇒_ {κ₁ = κ₂} π₂ τ₂) with κ₁ ≡k? κ₂
... | no p = no (λ { refl → p refl })
... | yes refl with π₁ ≡p? π₂ 
...                 | yes refl = map′ (cong (π₁ ⇒_)) (λ { refl → refl })  (τ₁ ≡? τ₂)
...                 | no p  = no (λ { refl → p refl })
`∀ {κ₁} τ₁ ≡? `∀ {κ₂} τ₂ with κ₁ ≡k? κ₂ 
... | yes refl = map′ (cong (`∀ {κ = κ₁})) (λ { refl → refl })  (τ₁ ≡? τ₂)
... | no  p = no (λ { refl → p refl })
(τ₁ `→ τ₂) ≡? (τ₃ `→ τ₄) with τ₁ ≡? τ₃
... | no  p = no (λ { refl → p  refl })
... | yes refl = map′ (cong (τ₁ `→_)) (λ { refl → refl }) (τ₂ ≡? τ₄)
Π τ₁ ≡? Π τ₂ = map′ (cong Π) (λ { refl → refl }) (τ₁ ≡? τ₂)
lab l₁ ≡? lab l₂ = map′ (cong lab) (λ { refl → refl }) (l₁ ≟ l₂)
⌊ τ₁ ⌋ ≡? ⌊ τ₂ ⌋ = map′ (cong ⌊_⌋) (λ { refl → refl }) (τ₁ ≡? τ₂)
Σ τ₁ ≡? Σ τ₂ = map′ (cong Σ) (λ { refl → refl }) (τ₁ ≡? τ₂)
ne τ₁ ≡? ne τ₂ with τ₁ ≡NE? τ₂
... | yes refl = yes (cong-ne refl)
... | no  p = no (λ { x → p (inj-ne x) })
⦅ ρ₁ ⦆ oρ₁ ≡? ⦅ ρ₂ ⦆ oρ₂ with ρ₁ ≡Row? ρ₂ 
... | yes refl rewrite NormalIrrelevantOrdered ρ₁ oρ₁ oρ₂  = yes refl
... | no  p  = no (λ { refl → p refl })
(x₁ ─ x₂) ≡? (y₁ ─ y₂) with x₁ ≡? y₁ | x₂ ≡? y₂ 
... | yes refl | yes refl = yes (cong-─ refl refl)
... | _     | no q = no (λ { refl → q refl })
... | no p  | _ = no (λ { refl → p refl })
(l ▹ₙ x₁) ≡? (l₁ ▹ₙ y₁) with l ≡NE? l₁ | x₁ ≡? y₁ 
... | yes refl | yes refl = yes refl
... | no p     | _     = no (λ { refl → p refl }) 
... | _        | no q  = no (λ { refl → q refl }) 
-- nuisance cases
ne x ≡? (τ₂ `→ τ₃) = no (λ ())
ne x ≡? `∀ τ₂ = no (λ ())
ne x ≡? μ τ₂ = no (λ ())
ne x ≡? (π ⇒ τ₂) = no (λ ())
ne x ≡? lab l = no (λ ())
ne x ≡? ⌊ τ₂ ⌋ = no (λ ())
ne x ≡? Π τ₂ = no (λ ())
ne x ≡? Σ τ₂ = no (λ ())
ne x ≡? ⦅ x₁ ⦆ _ = no (λ ())
⦅ x ⦆ _ ≡? ne x₁ = no (λ ())
(τ₁ `→ τ₂) ≡? ne x = no (λ ())
(τ₁ `→ τ₂) ≡? `∀ τ₃ = no (λ ())
(τ₁ `→ τ₂) ≡? μ τ₃ = no (λ ())
(τ₁ `→ τ₂) ≡? (π ⇒ τ₃) = no (λ ())
(τ₁ `→ τ₂) ≡? ⌊ τ₃ ⌋ = no (λ ())
(τ₁ `→ τ₂) ≡? Π τ₃ = no (λ ())
(τ₁ `→ τ₂) ≡? Σ τ₃ = no (λ ())
`∀ τ₁ ≡? ne x = no (λ ())
`∀ τ₁ ≡? (τ₂ `→ τ₃) = no (λ ())
`∀ τ₁ ≡? μ τ₂ = no (λ ())
`∀ τ₁ ≡? (π ⇒ τ₂) = no (λ ())
`∀ τ₁ ≡? ⌊ τ₂ ⌋ = no (λ ())
`∀ τ₁ ≡? Π τ₂ = no (λ ())
`∀ τ₁ ≡? Σ τ₂ = no (λ ())
μ τ₁ ≡? ne x = no (λ ())
μ τ₁ ≡? (τ₂ `→ τ₃) = no (λ ())
μ τ₁ ≡? `∀ τ₂ = no (λ ())
μ τ₁ ≡? (π ⇒ τ₂) = no (λ ())
μ τ₁ ≡? ⌊ τ₂ ⌋ = no (λ ())
μ τ₁ ≡? Π τ₂ = no (λ ())
μ τ₁ ≡? Σ τ₂ = no (λ ())
(π ⇒ τ₁) ≡? ne x = no (λ ())
(π ⇒ τ₁) ≡? (τ₂ `→ τ₃) = no (λ ())
(π ⇒ τ₁) ≡? `∀ τ₂ = no (λ ())
(π ⇒ τ₁) ≡? μ τ₂ = no (λ ())
(π ⇒ τ₁) ≡? ⌊ τ₂ ⌋ = no (λ ())
(π ⇒ τ₁) ≡? Π τ₂ = no (λ ())
(π ⇒ τ₁) ≡? Σ τ₂ = no (λ ())
lab l ≡? ne x = no (λ ())
⌊ τ₁ ⌋ ≡? ne x = no (λ ())
⌊ τ₁ ⌋ ≡? (τ₂ `→ τ₃) = no (λ ())
⌊ τ₁ ⌋ ≡? `∀ τ₂ = no (λ ())
⌊ τ₁ ⌋ ≡? μ τ₂ = no (λ ())
⌊ τ₁ ⌋ ≡? (π ⇒ τ₂) = no (λ ())
⌊ τ₁ ⌋ ≡? Π τ₂ = no (λ ())
⌊ τ₁ ⌋ ≡? Σ τ₂ = no (λ ())
Π τ₁ ≡? ne x = no (λ ())
Π τ₁ ≡? (τ₂ `→ τ₃) = no (λ ())
Π τ₁ ≡? `∀ τ₂ = no (λ ())
Π τ₁ ≡? μ τ₂ = no (λ ())
Π τ₁ ≡? (π ⇒ τ₂) = no (λ ())
Π τ₁ ≡? ⌊ τ₂ ⌋ = no (λ ())
Π τ₁ ≡? Σ τ₂ = no (λ ())
Σ τ₁ ≡? ne x = no (λ ())
Σ τ₁ ≡? (τ₂ `→ τ₃) = no (λ ())
Σ τ₁ ≡? `∀ τ₂ = no (λ ())
Σ τ₁ ≡? μ τ₂ = no (λ ())
Σ τ₁ ≡? (π ⇒ τ₂) = no (λ ())
Σ τ₁ ≡? ⌊ τ₂ ⌋ = no (λ ())
Σ τ₁ ≡? Π τ₂ = no (λ ())
⦅ ρ ⦆ oρ ≡? (y₁ ─ y₂) = no (λ ())
⦅ ρ ⦆ oρ ≡? (l ▹ₙ y₁) = no (λ ())
⦅ ρ ⦆ oρ ≡? (_ <$> _) = no (λ ())
(x₁ ─ x₂) ≡? ne x₃ = no (λ ())
(x₁ ─ x₂) ≡? ⦅ ρ ⦆ oρ = no (λ ())
(x₁ ─ x₂) ≡? (l ▹ₙ y₁) = no (λ ())
(x₁ ─ x₂) ≡? (_ <$> _) = no (λ ())
(l ▹ₙ x₁) ≡? ne x₂ = no (λ ())
(l ▹ₙ x₁) ≡? ⦅ ρ ⦆ oρ = no (λ ())
(l ▹ₙ x₁) ≡? (y₁ ─ y₂) = no (λ ())
(l ▹ₙ x₁) ≡? (_ <$> _) = no (λ ())
_<$>_ {κ₁} f x ≡? ⦅ ρ ⦆ oρ = no (λ ())
_<$>_ {κ₁} f x ≡? (τ ─ τ₁) = no (λ ())
_<$>_ {κ₁} f x ≡? (l ▹ₙ τ) = no (λ ())

-- --------------------------------------------------------------------------------
-- -- Type equivalence is decidable

_≡t?_ : ∀ (τ₁ τ₂ : Type Δ κ) → Dec (τ₁ ≡t τ₂)
τ₁ ≡t? τ₂  with (⇓ τ₁) ≡? (⇓ τ₂)
... | yes p = yes (completeness τ₁ τ₂ p)
... | no  p = no (p ∘ soundness)
 
