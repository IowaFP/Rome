module Rome.Operational.Types.Normal.Properties.Decidability where 

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Kinds.Decidability

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Equivalence

open import Data.String.Properties using (_≟_)

--------------------------------------------------------------------------------
-- Decidability of NeutralType equality

_≡NE?_ : ∀ (τ₁ τ₂ : NeutralType Δ κ) → Dec (τ₁ ≡ τ₂) 
_≡?_ : ∀ (τ₁ τ₂ : NormalType Δ κ) → Dec (τ₁ ≡ τ₂)
_≡p?_ : ∀ (ρ₁ ρ₂ : NormalPred Δ R[ κ ]) → Dec (ρ₁ ≡ ρ₂)

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
ε ≡? ε = yes refl
(l₁ ▹ τ₁) ≡? (l₂ ▹ τ₂) with l₁ ≡? l₂
... | no  p = no (λ { refl → p  refl })
... | yes refl = map′ (cong (l₁ ▹_)) (λ { refl → refl }) (τ₁ ≡? τ₂)
Π τ₁ ≡? Π τ₂ = map′ (cong Π) (λ { refl → refl }) (τ₁ ≡? τ₂)
lab l₁ ≡? lab l₂ = map′ (cong lab) (λ { refl → refl }) (l₁ ≟ l₂)
⌊ τ₁ ⌋ ≡? ⌊ τ₂ ⌋ = map′ (cong ⌊_⌋) (λ { refl → refl }) (τ₁ ≡? τ₂)
ΠL τ₁ ≡? ΠL τ₂ = map′ (cong ΠL) (λ { refl → refl }) (τ₁ ≡? τ₂)
Σ τ₁ ≡? Σ τ₂ = map′ (cong Σ) (λ { refl → refl }) (τ₁ ≡? τ₂)
ΣL τ₁ ≡? ΣL τ₂ = map′ (cong ΣL) (λ { refl → refl }) (τ₁ ≡? τ₂)
-- nuisance cases
(τ₁ ▹ τ₂) ≡? ne x = no (λ ())
(τ₁ ▹ τ₂) ≡? ε = no (λ ())
ne x ≡? (τ₂ `→ τ₃) = no (λ ())
ne x ≡? `∀ τ₂ = no (λ ())
ne x ≡? μ τ₂ = no (λ ())
ne x ≡? (π ⇒ τ₂) = no (λ ())
ne x ≡? ε = no (λ ())
ne x ≡? (τ₂ ▹ τ₃) = no (λ ())
ne x ≡? lab l = no (λ ())
ne x ≡? ⌊ τ₂ ⌋ = no (λ ())
ne x ≡? Π τ₂ = no (λ ())
ne x ≡? ΠL τ₂ = no (λ ())
ne x ≡? Σ τ₂ = no (λ ())
ne x ≡? ΣL τ₂ = no (λ ())
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
ε ≡? ne x = no (λ ())
ε ≡? (τ₂ ▹ τ₃) = no (λ ())
lab l ≡? ne x = no (λ ())
lab l ≡? ΠL τ₂ = no (λ ())
lab l ≡? ΣL τ₂ = no (λ ())
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
ΠL τ₁ ≡? ne x = no (λ ())
ΠL τ₁ ≡? lab l = no (λ ())
ΠL τ₁ ≡? ΣL τ₂ = no (λ ())
Σ τ₁ ≡? ne x = no (λ ())
Σ τ₁ ≡? (τ₂ `→ τ₃) = no (λ ())
Σ τ₁ ≡? `∀ τ₂ = no (λ ())
Σ τ₁ ≡? μ τ₂ = no (λ ())
Σ τ₁ ≡? (π ⇒ τ₂) = no (λ ())
Σ τ₁ ≡? ⌊ τ₂ ⌋ = no (λ ())
Σ τ₁ ≡? Π τ₂ = no (λ ())
ΣL τ₁ ≡? ne x = no (λ ())
ΣL τ₁ ≡? lab l = no (λ ())
ΣL τ₁ ≡? ΠL τ₂ = no (λ ())

--------------------------------------------------------------------------------
-- Type equivalence is decidable

_≡t?_ : ∀ (τ₁ τ₂ : Type Δ κ) → Dec (τ₁ ≡t τ₂)
τ₁ ≡t? τ₂  with (⇓ τ₁) ≡? (⇓ τ₂)
... | yes p = yes 
    (eq-trans 
        (soundness τ₁) 
        (embed-≡t p))
... | no  p = no (λ x → p (completeness x))
 
