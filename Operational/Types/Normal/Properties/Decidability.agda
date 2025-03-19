module Rome.Operational.Types.Normal.Properties.Decidability where 

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Equivalence

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

--------------------------------------------------------------------------------
-- Decidability of NeutralType equality

_≡NE?_ : ∀ (τ₁ τ₂ : NeutralType Δ κ) → Dec (τ₁ ≡ τ₂) 
_≡?_ : ∀ (τ₁ τ₂ : NormalType Δ κ) → Dec (τ₁ ≡ τ₂)

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
-- Decidability of NormalType equality

_≡?_ {κ = ★} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
_≡?_ {κ = L} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
_≡?_ {κ = R[ κ ]} (ne x .{tt}) (ne y .{tt}) = map′ (cong (λ x → ne x {tt})) (λ { refl → refl }) (x ≡NE? y) 
`λ τ₁ ≡? `λ τ₂ = map′ (cong `λ) (λ { refl → refl }) (τ₁ ≡? τ₂)
μ τ₁ ≡? μ τ₂ = map′ (cong μ) (λ { refl → refl})  (τ₁ ≡? τ₂)
(π ⇒ τ₁) ≡? (π₁ ⇒ τ₂) = {!  !}
`∀ τ₁ ≡? `∀ τ₂ = {! no (λ ())  !}
(τ₁ `→ τ₂) ≡? (τ₃ `→ τ₄) = {!   !}
ε ≡? ε = yes refl
(l₁ ▹ τ₁) ≡? (l₂ ▹ τ₂) with l₁ ≡? l₂ | τ₁ ≡? τ₂ 
... | yes refl | yes refl = yes refl
... | yes p | no q = no (λ x → q (inj-▹ᵣ x))
... | no p | yes q = no (λ x → p (inj-▹ₗ x))
... | no p | no q = no (λ x → p (inj-▹ₗ x))
Π τ₁ ≡? Π τ₂ = {!   !}
lab l ≡? lab l₁ = {!   !}
⌊ τ₁ ⌋ ≡? ⌊ τ₂ ⌋ = {!   !}
ΠL τ₁ ≡? ΠL τ₂ = {!   !}
Σ τ₁ ≡? Σ τ₂ = {!   !}
ΣL τ₁ ≡? ΣL τ₂ = {!   !}
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


_≡t?_ : ∀ (τ₁ τ₂ : Type Δ κ) → Dec (τ₁ ≡t τ₂)
τ₁ ≡t? τ₂  with (⇓ τ₁) ≡? (⇓ τ₂)
... | yes p = yes 
    (eq-trans 
        (soundness τ₁) 
        (embed-≡t {τ₁ = ⇓ τ₁} {τ₂ = τ₂} p))
... | no  p = no (λ x → p (completeness x))
 