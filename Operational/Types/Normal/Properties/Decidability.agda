{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Properties.Decidability where 

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Kinds.Decidability

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
-- open import Rome.Operational.Types.Semantic.NBE

-- open import Rome.Operational.Types.Theorems.Stability
-- open import Rome.Operational.Types.Theorems.Completeness
-- open import Rome.Operational.Types.Theorems.Soundness
-- open import Rome.Operational.Types.Equivalence.Relation

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
` x ≡NE? (φ <$> d) = no (λ ()) 
(x · τ) ≡NE? ` α = no (λ ())
(_·_ {κ₁} x τ₁) ≡NE? (_·_ {κ₂} y τ₂) with κ₁ ≡k? κ₂ 
... | no  q = no (λ { refl → q refl })
... | yes refl with x ≡NE? y | τ₁ ≡? τ₂ 
... | yes refl | yes refl = yes refl
... | _ | no q = no (λ { refl → q refl })
... | no p  | _ = no (λ { refl → p refl })
(x · τ) ≡NE? (φ <$> y) = no (λ ())
(φ <$> x) ≡NE? ` α = no (λ ())
(φ <$> x) ≡NE? (y · τ) = no (λ ())
(_<$>_ {κ₁} f x) ≡NE? (_<$>_ {κ₂} g y) with κ₁ ≡k? κ₂ 
... | no  q = no (λ { refl → q refl })
... | yes refl with f ≡? g | x ≡NE? y
... | yes refl | yes refl = yes refl
... | _ | no q = no (λ { refl → q refl })
... | no p  | _ = no (λ { refl → p refl })
` α ≡NE? (y ─₁ x) = no (λ ())
` α ≡NE? (x ─₂ y) = no (λ ())
(x · τ) ≡NE? (y ─₁ x₁) = no (λ ())
(x · τ) ≡NE? (x₁ ─₂ y) = no (λ ())
(φ <$> x) ≡NE? (y ─₁ x₁) = no (λ ())
(φ <$> x) ≡NE? (x₁ ─₂ y) = no (λ ())
(x ─₁ x₁) ≡NE? ` α = no (λ ())
(x ─₁ x₁) ≡NE? (y · τ) = no (λ ())
(x ─₁ x₁) ≡NE? (φ <$> y) = no (λ ())
(ρ₂ ─₁ ρ₁) ≡NE? (ρ₄ ─₁ ρ₃) with ρ₂ ≡NE? ρ₄ | ρ₁ ≡? ρ₃ 
... | yes refl | yes refl = yes refl
... | no p     | _    = no (λ { refl → p refl })
... | _        | no p = no (λ { refl → p refl })
(x ─₁ x₁) ≡NE? (x₂ ─₂ y) = no (λ ())
(x ─₂ x₁) ≡NE? ` α = no (λ ())
(x ─₂ x₁) ≡NE? (y · τ) = no (λ ())
(x ─₂ x₁) ≡NE? (φ <$> y) = no (λ ())
(x ─₂ x₁) ≡NE? (y ─₁ x₂) = no (λ ())
(ρ₂ ─₂ ρ₁) ≡NE? (ρ₄ ─₂ ρ₃) with ρ₂ ≡? ρ₄ | ρ₁ ≡NE? ρ₃ 
... | yes refl | yes refl = yes (cong-─₂ refl refl)
... | no p     | _    = no (λ { refl → p refl })
... | _        | no p = no (λ { refl → p refl })
` α ≡NE? (y ▹ₙ x) = no (λ ())
(x · τ) ≡NE? (y ▹ₙ x₁) = no (λ ())
(φ <$> x) ≡NE? (y ▹ₙ x₁) = no (λ ())
(x ▹ₙ x₁) ≡NE? ` α = no (λ ())
(x ▹ₙ x₁) ≡NE? (y · τ) = no (λ ())
(x ▹ₙ x₁) ≡NE? (φ <$> y) = no (λ ())
(x ▹ₙ τ₁) ≡NE? (y ▹ₙ τ₂) with x ≡NE? y | τ₁ ≡? τ₂ 
... | yes refl | yes refl = yes (cong₂ _▹ₙ_ refl refl)
... | no  p | _ = no (λ { refl → p refl })
... | _ | no p  = no (λ { refl → p refl })
(x ▹ₙ x₁) ≡NE? (y ─₁ ρ) = no (λ ())
(x ▹ₙ x₁) ≡NE? (ρ ─₂ y) = no (λ ())
(x ─₁ ρ) ≡NE? (y ▹ₙ x₁) = no (λ ())
(ρ ─₂ x) ≡NE? (y ▹ₙ x₁) = no (λ ())

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

_≡?_ {κ = ★} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
_≡?_ {κ = L} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
_≡?_ {κ = R[ κ ]} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
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
-- ε ≡? ε = yes refl
-- (l₁ ▹ τ₁) ≡? (l₂ ▹ τ₂) with l₁ ≡? l₂
-- ... | no  p = no (λ { refl → p  refl })
-- ... | yes refl = map′ (cong (l₁ ▹_)) (λ { refl → refl }) (τ₁ ≡? τ₂)
Π τ₁ ≡? Π τ₂ = map′ (cong Π) (λ { refl → refl }) (τ₁ ≡? τ₂)
lab l₁ ≡? lab l₂ = map′ (cong lab) (λ { refl → refl }) (l₁ ≟ l₂)
⌊ τ₁ ⌋ ≡? ⌊ τ₂ ⌋ = map′ (cong ⌊_⌋) (λ { refl → refl }) (τ₁ ≡? τ₂)
Σ τ₁ ≡? Σ τ₂ = map′ (cong Σ) (λ { refl → refl }) (τ₁ ≡? τ₂)
ne τ₁ ≡? ne τ₂ with τ₁ ≡NE? τ₂
... | yes refl = yes (cong-ne refl)
... | no  p = no (λ { x → p (inj-ne x) })
⦅ ρ₁ ⦆ oρ₁ ≡? ⦅ ρ₂ ⦆ oρ₂ with ρ₁ ≡Row? ρ₂ 
... | yes refl rewrite NormalMerePropOrdered ρ₁ oρ₁ oρ₂  = yes refl
... | no  p  = no (λ { refl → p refl })
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

-- --------------------------------------------------------------------------------
-- -- Type equivalence is decidable

-- _≡t?_ : ∀ (τ₁ τ₂ : Type Δ κ) → Dec (τ₁ ≡t τ₂)
-- τ₁ ≡t? τ₂  with (⇓ τ₁) ≡? (⇓ τ₂)
-- ... | yes p = yes 
--     (eq-trans 
--         (soundness τ₁) 
--         (embed-≡t p))
-- ... | no  p = no (λ x → p (completeness x))
 
