{-# OPTIONS --allow-unsolved-metas #-}
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
-- Renaming respects type equivalence

renₖ-≡t : ∀ {τ υ : Type Δ₁ κ} (ρ : Renamingₖ Δ₁ Δ₂) → 
                τ ≡t υ → renₖ ρ τ ≡t renₖ ρ υ 
renₖ-≡p : ∀ {π₁ π₂ : Pred Type Δ₁ R[ κ ]} (ρ : Renamingₖ Δ₁ Δ₂) → 
                π₁ ≡p π₂ → renPredₖ ρ π₁ ≡p renPredₖ ρ π₂
renₖ-≡r : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ₁ R[ κ ]} (r : Renamingₖ Δ₁ Δ₂) → 
                ρ₁ ≡r ρ₂ → renRowₖ r ρ₁ ≡r renRowₖ r ρ₂

renₖ-≡t {τ = τ} {υ} ρ eq-refl = eq-refl
renₖ-≡t {τ = τ} {υ} ρ (eq-sym e) = eq-sym (renₖ-≡t ρ e)
renₖ-≡t {τ = τ} {υ} ρ (eq-trans e e₁) = eq-trans (renₖ-≡t ρ e) (renₖ-≡t ρ e₁)
renₖ-≡t {τ = τ} {υ} ρ (eq-→ e e₁) = eq-→ (renₖ-≡t ρ e) (renₖ-≡t ρ e₁)
renₖ-≡t {τ = τ} {υ} ρ (eq-∀ e) = eq-∀ (renₖ-≡t (liftₖ ρ) e)
renₖ-≡t {τ = τ} {υ} ρ (eq-μ e) = eq-μ (renₖ-≡t ρ e)
renₖ-≡t {τ = τ} {υ} ρ (eq-λ e) = eq-λ (renₖ-≡t (liftₖ ρ) e)
renₖ-≡t {τ = τ} {υ} ρ (eq-· e e₁) = eq-· (renₖ-≡t ρ e) (renₖ-≡t ρ e₁)
renₖ-≡t {τ = τ} {υ} ρ (eq-⌊⌋ e) = eq-⌊⌋ (renₖ-≡t ρ e)
renₖ-≡t {τ = τ} {υ} ρ (eq-▹ e e₁) = eq-▹ (renₖ-≡t ρ e) (renₖ-≡t ρ e₁)
renₖ-≡t {τ = τ} {υ} ρ (eq-⇒ x e) = eq-⇒ (renₖ-≡p ρ x) (renₖ-≡t ρ e)
renₖ-≡t {τ = τ} {.(`λ (weakenₖ τ · ` Z))} ρ eq-η = 
    eq-trans 
        (eq-η {f = renₖ ρ τ}) 
        (eq-λ (eq-· 
            (inst (sym (↻-liftₖ-weaken ρ τ) )) 
            eq-refl))
renₖ-≡t {τ = `λ τ₁ · τ₂} {.(τ₁ βₖ[ τ₂ ])} ρ (eq-β {τ₁ = τ₁} {τ₂}) = 
    eq-trans 
        (eq-β {τ₁ = renₖ (liftₖ ρ) τ₁} {renₖ ρ τ₂}) 
        (eq-sym (inst (↻-renₖ-β ρ τ₁ τ₂)))
renₖ-≡t {τ = τ} {υ} ρ eq-Π▹ = eq-Π▹ 
renₖ-≡t {τ = τ} {υ} ρ eq-Σ▹ = eq-Σ▹
renₖ-≡t {τ = (Π · (l ▹ `λ τ))} {υ} ρ (eq-Πλ {l = l} {τ}) = 
    eq-trans 
    (eq-Πλ {l = renₖ ρ l} {renₖ (liftₖ ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-liftₖ-weaken ρ l))) eq-refl)))
renₖ-≡t {τ = (Σ · (l ▹ `λ τ))} {υ} ρ (eq-Σλ {l = l} {τ}) = 
    eq-trans 
    (eq-Σλ {l = renₖ ρ l} {renₖ (liftₖ ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-liftₖ-weaken ρ l))) eq-refl)))
renₖ-≡t {τ = τ} {υ} ρ eq-▹$ = eq-▹$
renₖ-≡t {τ = τ} {υ} ρ eq-Π-assoc = eq-Π-assoc
renₖ-≡t {τ = τ} {υ} ρ eq-Σ-assoc = eq-Σ-assoc
renₖ-≡t {τ = τ} {υ} ρ eq-Π = eq-Π
renₖ-≡t {τ = τ} {υ} ρ eq-Σ = eq-Σ
renₖ-≡t {τ = τ} {υ} ρ (eq-<$> t u) = eq-<$> (renₖ-≡t ρ t) (renₖ-≡t ρ u)
renₖ-≡t {τ = τ} {υ} r (eq-row x) = eq-row (renₖ-≡r r x)
renₖ-≡t {τ = τ} {υ} r (eq-map {F = F} {ρ = []}) = eq-map {F = renₖ r F} {ρ = []}
renₖ-≡t {τ = τ} {υ} r (eq-map {F = F} {ρ = x ∷ ρ}) = 
    eq-trans 
        (eq-map {F = renₖ r F} {ρ = renₖ r x ∷ renRowₖ r ρ}) 
        (eq-row (eq-cons eq-refl (instᵣ (↻-ren-map r F ρ))))

renₖ-≡r {ρ₁ = ρ₁} {ρ₂} r eq-[] = eq-[]
renₖ-≡r {ρ₁ = ρ₁} {ρ₂} r (eq-cons x eq) = eq-cons (renₖ-≡t _ x) (renₖ-≡r r eq )

renₖ-≡p {π₁} {π₂} ρ (eq₁ eq-≲ eq₂) = renₖ-≡t ρ eq₁ eq-≲ renₖ-≡t ρ eq₂
renₖ-≡p {π₁} {π₂} ρ (eq₁ eq-· eq₂ ~ eq₃) = (renₖ-≡t ρ eq₁) eq-· (renₖ-≡t ρ eq₂) ~ (renₖ-≡t ρ eq₃)

--------------------------------------------------------------------------------
-- Lifting of substitutions respects type equivalence

liftsₖ-cong-≡t : ∀ {σ₁  σ₂ : Substitutionₖ Δ₁ Δ₂} → 
                (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡t σ₂ x) → 
                 ∀ {κ'} (x : KVar (Δ₁ ,, κ') κ) → liftsₖ σ₁ x ≡t liftsₖ σ₂ x
liftsₖ-cong-≡t c Z = eq-refl
liftsₖ-cong-≡t c (S x) = renₖ-≡t S (c x)                 

--------------------------------------------------------------------------------
-- Equivalent substitutions are congruent over types w.r.t. type equivalence

subₖ-cong-≡t : ∀ {σ₁  σ₂ : Substitutionₖ Δ₁ Δ₂}  → 
                (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡t σ₂ x) → 
                 (τ : Type Δ₁ κ) → subₖ σ₁ τ ≡t subₖ σ₂ τ
subRowₖ-cong-≡t : ∀ {σ₁  σ₂ : Substitutionₖ Δ₁ Δ₂}  → 
                (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡t σ₂ x) → 
                 (ρ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ σ₁ ρ ≡r subRowₖ σ₂ ρ
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (` α) = c α
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (`λ τ) = eq-λ (subₖ-cong-≡t (liftsₖ-cong-≡t c) τ)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (τ · τ₁) = eq-· (subₖ-cong-≡t c τ) (subₖ-cong-≡t c τ₁)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (τ `→ τ₁) = eq-→ (subₖ-cong-≡t c τ) (subₖ-cong-≡t c τ₁)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (`∀ τ)  = eq-∀ (subₖ-cong-≡t (liftsₖ-cong-≡t c) τ)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (μ τ)  = eq-μ (subₖ-cong-≡t c τ)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) = 
    eq-⇒ 
        ((subₖ-cong-≡t c ρ₁) eq-· (subₖ-cong-≡t c ρ₂) ~ (subₖ-cong-≡t c ρ₃))
        (subₖ-cong-≡t c τ)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c ((ρ₁ ≲ ρ₂) ⇒ τ) = 
    eq-⇒ 
        ((subₖ-cong-≡t c ρ₁) eq-≲ (subₖ-cong-≡t c ρ₂))
        (subₖ-cong-≡t c τ)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (lab l)  = eq-refl
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c ⌊ τ ⌋ = eq-⌊⌋ (subₖ-cong-≡t c τ)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (τ ▹ τ₁) = eq-▹ (subₖ-cong-≡t c τ) (subₖ-cong-≡t c τ₁) 
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c (τ <$> τ₁) = eq-<$> (subₖ-cong-≡t c τ) (subₖ-cong-≡t c τ₁)
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c Π  = eq-refl    
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c Σ  = eq-refl                
subₖ-cong-≡t {σ₁ = σ₁} {σ₂} c ⦅ ρ ⦆ = eq-row (subRowₖ-cong-≡t c ρ)

subRowₖ-cong-≡t c [] = eq-[]
subRowₖ-cong-≡t c (τ ∷ ρ) = eq-cons (subₖ-cong-≡t c τ) (subRowₖ-cong-≡t c ρ)


--------------------------------------------------------------------------------
-- substitution respects type equivalence

subₖ-≡t :  ∀ {σ : Substitutionₖ Δ₁ Δ₂} {τ₁ τ₂ : Type Δ₁ κ} → 
                  τ₁ ≡t τ₂ → subₖ σ τ₁ ≡t subₖ σ τ₂
subₖ-≡r :  ∀ {σ : Substitutionₖ Δ₁ Δ₂} {ρ₁ ρ₂ : SimpleRow Type Δ₁ R[ κ ]} →
                  ρ₁ ≡r ρ₂ → subRowₖ σ ρ₁ ≡r subRowₖ σ ρ₂


subₖ-≡t {σ} eq-refl = eq-refl 
subₖ-≡t {σ} (eq-sym eq) = eq-sym (subₖ-≡t eq)
subₖ-≡t {σ} (eq-trans eq eq₁) = eq-trans (subₖ-≡t eq) (subₖ-≡t eq₁)
subₖ-≡t {σ} (eq-→ eq eq₁) = eq-→ (subₖ-≡t eq) (subₖ-≡t eq₁)
subₖ-≡t {σ} (eq-∀ eq) = eq-∀ (subₖ-≡t eq)
subₖ-≡t {σ} (eq-μ eq) = eq-μ (subₖ-≡t eq)
subₖ-≡t {σ} (eq-λ eq) = eq-λ (subₖ-≡t eq)
subₖ-≡t {σ} (eq-· eq eq₁) = eq-· (subₖ-≡t eq) (subₖ-≡t eq₁)
subₖ-≡t {σ} (eq-<$> eq eq₁) = eq-<$> (subₖ-≡t eq) (subₖ-≡t eq₁)
subₖ-≡t {σ} (eq-⌊⌋ eq) = eq-⌊⌋ (subₖ-≡t eq)
subₖ-≡t {σ} (eq-▹ eq eq₁) = eq-▹ (subₖ-≡t eq) (subₖ-≡t eq₁)
subₖ-≡t {σ} (eq-⇒ (ρ₁ eq-≲ x₂) eq) = 
  eq-⇒ 
    (subₖ-≡t ρ₁ eq-≲ subₖ-≡t x₂) 
    (subₖ-≡t eq)
subₖ-≡t {σ} (eq-⇒ (ρ₁ eq-· ρ₂ ~ ρ₃) eq) = 
  eq-⇒ 
    (subₖ-≡t ρ₁ eq-· subₖ-≡t ρ₂ ~ subₖ-≡t ρ₃) 
    (subₖ-≡t eq)
subₖ-≡t {σ = σ} {τ₁ = τ₁} eq-η = 
    eq-trans 
        (eq-η {f = subₖ σ τ₁}) 
        (eq-λ (eq-· 
            (inst (sym (trans (sym (↻-subₖ-renₖ τ₁)) (↻-renₖ-subₖ {σ = σ} {S} τ₁)) )) 
            eq-refl))
subₖ-≡t {σ = σ} {`λ τ₁ · τ₂} {.(τ₁ βₖ[ τ₂ ])} eq-β = 
    eq-trans 
        (eq-β {τ₁ = subₖ (liftsₖ σ) τ₁} {subₖ σ τ₂}) 
        (eq-sym (inst (sym (↻-subₖ-β σ τ₁ τ₂))))
subₖ-≡t {σ} eq-▹$ = eq-▹$
subₖ-≡t {σ} eq-Π▹ = eq-Π▹
subₖ-≡t {σ} eq-Σ▹ = eq-Σ▹
subₖ-≡t {σ} eq-Π = eq-Π
subₖ-≡t {σ} eq-Σ = eq-Σ
subₖ-≡t {σ = σ} {τ₁ = (Π · (l ▹ `λ τ))} {υ} (eq-Πλ {l = l} {τ}) = 
    eq-trans 
    (eq-Πλ {l = subₖ σ l} {subₖ (liftsₖ σ) τ}) 
    (eq-λ 
        (eq-· 
            eq-refl 
            (eq-▹ 
                (inst (trans 
                    (sym (↻-renₖ-subₖ {σ = σ} {S} l)) 
                    (↻-subₖ-renₖ {r = S} {liftsₖ σ} l))) 
                eq-refl)))
subₖ-≡t {σ = σ} {τ₁ = (Σ · (l ▹ `λ τ))} {υ} (eq-Σλ {l = l} {τ}) = 
    eq-trans 
    (eq-Σλ {l = subₖ σ l} {subₖ (liftsₖ σ) τ}) 
    (eq-λ 
        (eq-· 
            eq-refl 
            (eq-▹ 
                (inst (trans 
                    (sym (↻-renₖ-subₖ {σ = σ} {S} l)) 
                    (↻-subₖ-renₖ {r = S} {liftsₖ σ} l))) 
                eq-refl)))
subₖ-≡t {σ} eq-Π-assoc = eq-Π-assoc
subₖ-≡t {σ} eq-Σ-assoc = eq-Σ-assoc
subₖ-≡t {σ} (eq-row x) =  eq-row (subₖ-≡r x)
subₖ-≡t {σ = σ} (eq-map {F = F} {ρ = []}) = eq-map
subₖ-≡t {σ = σ} (eq-map {F = F} {ρ = x ∷ ρ}) = 
    eq-trans 
        (eq-map {F = subₖ σ F} {ρ = subₖ σ x ∷ subRowₖ σ ρ}) 
        (eq-row (eq-cons eq-refl (instᵣ (↻-sub-map σ F ρ))))

subₖ-≡r {ρ₁ = ρ₁} {ρ₂} eq-[] = eq-[]
subₖ-≡r {ρ₁ = ρ₁} {ρ₂} (eq-cons x eq) = eq-cons (subₖ-≡t x) (subₖ-≡r eq )
