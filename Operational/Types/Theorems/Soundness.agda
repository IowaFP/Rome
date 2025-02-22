module Rome.Operational.Types.Theorems.Soundness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Properties
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal.Syntax

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Theorems.Soundness.Relation 

--------------------------------------------------------------------------------
-- Fundamental lemma

sound-Π : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Π π-Kripke
sound-Π {κ₁ = ★} ρ {v} {left x} q = eq-· eq-refl q
sound-Π {κ₁ = L} ρ {v} {left x} q = eq-· eq-refl q
-- Need more tooling to build _≋_ 
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {f} {left g} q = λ ρ eq → {!   !}
sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {left x} q = 
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-app-lift-Π 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-≋ (sound-Π id eq-refl)))) 
                eq-refl))
sound-Π {κ₁ = ★} ρ {v} {right (l , τ)} q = eq-· eq-refl q
sound-Π {κ₁ = L} ρ {v} {right (l , τ)} q = eq-· eq-refl q
-- Need more tooling to build _≋_ 
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {v} {right (l , τ)} q = {!   !}
sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {right (l , τ)} q = 
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Π 
            (eq-▹ eq-refl (reify-≋ (sound-Π id (reify-stable τ)))))

evalSR : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitution Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          SREnv σ η → (sub σ τ) ≋ (eval τ η) 
evalSR Unit {σ} {η} e = eq-refl
evalSR (` α) {σ} {η} e = e α
evalSR (`λ τ) {σ} {η} e = {!   !}
evalSR (τ₁ · τ₂) {σ} {η} e = {! eq-·  !}
evalSR (τ₁ `→ τ₂) {σ} {η} e = eq-→ (evalSR τ₁ e) (evalSR τ₂ e)
evalSR (`∀ κ τ) {σ} {η} e = {!   !}
evalSR (μ τ) {σ} {η} e = eq-μ 
    (eq-trans 
        (eq-η {f = sub σ τ}) 
        (eq-λ (evalSR τ e S eq-refl)))
evalSR (π ⇒ τ) {σ} {η} e = {!   !}
evalSR (lab l) {σ} {η} e = eq-refl
evalSR (l ▹ τ) {σ} {η} e = eq-▹ (evalSR l e) (reify-≋ (evalSR τ e)) 
evalSR ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (evalSR τ e)
evalSR Π {σ} {η} e = sound-Π -- λ {ρ {v} {left x} q → {!   !}
                      -- ; ρ {v} {right y} q → {!   !}}
evalSR Σ {σ} {η} e = {!   !}
evalSR (τ₁ <$> τ₂) {σ} {η} e = {!   !}        

idSR : ∀ {Δ₁} → SREnv ` (idEnv {Δ₁})
idSR α = reflect-≋ eq-refl

--------------------------------------------------------------------------------
-- Soundness claim  

soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ)   
soundness τ = subst (_≡t ⇑ (⇓ τ)) (sub-id τ) ((reify-≋ (evalSR τ idSR))) 