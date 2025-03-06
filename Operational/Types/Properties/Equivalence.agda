module Rome.Operational.Types.Properties.Equivalence where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution


--------------------------------------------------------------------------------
-- Properties of equivalence

cong-renₖ-≡t : ∀ {τ υ : Type Δ₁ κ} (ρ : Renamingₖ Δ₁ Δ₂) → 
                τ ≡t υ → renₖ ρ τ ≡t renₖ ρ υ 
cong-renₖ-≡p : ∀ {π₁ π₂ : Pred Δ₁ R[ κ ]} (ρ : Renamingₖ Δ₁ Δ₂) → 
                π₁ ≡p π₂ → renPredₖ ρ π₁ ≡p renPredₖ ρ π₂

cong-renₖ-≡t {τ = τ} {υ} ρ eq-refl = eq-refl
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-sym e) = eq-sym (cong-renₖ-≡t ρ e)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-trans e e₁) = eq-trans (cong-renₖ-≡t ρ e) (cong-renₖ-≡t ρ e₁)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-→ e e₁) = eq-→ (cong-renₖ-≡t ρ e) (cong-renₖ-≡t ρ e₁)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-∀ e) = eq-∀ (cong-renₖ-≡t (liftₖ ρ) e)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-μ e) = eq-μ (cong-renₖ-≡t ρ e)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-λ e) = eq-λ (cong-renₖ-≡t (liftₖ ρ) e)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-· e e₁) = eq-· (cong-renₖ-≡t ρ e) (cong-renₖ-≡t ρ e₁)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-⌊⌋ e) = eq-⌊⌋ (cong-renₖ-≡t ρ e)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-▹ e e₁) = eq-▹ (cong-renₖ-≡t ρ e) (cong-renₖ-≡t ρ e₁)
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-⇒ x e) = eq-⇒ (cong-renₖ-≡p ρ x) (cong-renₖ-≡t ρ e)
cong-renₖ-≡t {τ = τ} {.(`λ (weaken τ · ` Z))} ρ eq-η = 
    eq-trans 
        (eq-η {f = renₖ ρ τ}) 
        (eq-λ (eq-· 
            (inst (sym (↻-liftₖ-weaken ρ τ) )) 
            eq-refl))
cong-renₖ-≡t {τ = `λ τ₁ · τ₂} {.(τ₁ βₖ[ τ₂ ])} ρ (eq-β {τ₁ = τ₁} {τ₂}) = 
    eq-trans 
        (eq-β {τ₁ = renₖ (liftₖ ρ) τ₁} {renₖ ρ τ₂}) 
        (eq-sym (inst (↻-renₖ-β ρ τ₁ τ₂)))
cong-renₖ-≡t {τ = τ} {υ} ρ eq-Π▹ = eq-Π▹ 
cong-renₖ-≡t {τ = τ} {υ} ρ eq-Σ▹ = eq-Σ▹
cong-renₖ-≡t {τ = (Π · (l ▹ `λ τ))} {υ} ρ (eq-Πλ {l = l} {τ}) = 
    eq-trans 
    (eq-Πλ {l = renₖ ρ l} {renₖ (liftₖ ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-liftₖ-weaken ρ l))) eq-refl)))
cong-renₖ-≡t {τ = (Σ · (l ▹ `λ τ))} {υ} ρ (eq-Σλ {l = l} {τ}) = 
    eq-trans 
    (eq-Σλ {l = renₖ ρ l} {renₖ (liftₖ ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-liftₖ-weaken ρ l))) eq-refl)))
cong-renₖ-≡t {τ = τ} {υ} ρ eq-▹$ = eq-▹$
cong-renₖ-≡t {τ = τ} {υ} ρ eq-Π-assoc = eq-Π-assoc
cong-renₖ-≡t {τ = τ} {υ} ρ eq-Σ-assoc = eq-Σ-assoc
cong-renₖ-≡t {τ = τ} {υ} ρ eq-Π = eq-Π
cong-renₖ-≡t {τ = τ} {υ} ρ eq-Σ = eq-Σ
cong-renₖ-≡t {τ = τ} {υ} ρ (eq-<$> t u) = eq-<$> (cong-renₖ-≡t ρ t) (cong-renₖ-≡t ρ u)
cong-renₖ-≡t {τ = τ} {υ} ρ eq-<$>ε = eq-trans eq-<$>ε eq-refl

cong-renₖ-≡p {π₁} {π₂} ρ (eq₁ eq-≲ eq₂) = cong-renₖ-≡t ρ eq₁ eq-≲ cong-renₖ-≡t ρ eq₂
cong-renₖ-≡p {π₁} {π₂} ρ (eq₁ eq-· eq₂ ~ eq₃) = (cong-renₖ-≡t ρ eq₁) eq-· (cong-renₖ-≡t ρ eq₂) ~ (cong-renₖ-≡t ρ eq₃)
  
