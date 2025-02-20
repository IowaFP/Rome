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

evalSR : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitution Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          SREnv σ η → (sub σ τ) ≋ (eval τ η) 
evalSR Unit {σ} {η} e = eq-refl
evalSR (` α) {σ} {η} e = e α
evalSR (`λ τ) {σ} {η} e = {!   !}
evalSR (τ₁ · τ₂) {σ} {η} e = {! eq-·  !}
evalSR (τ₁ `→ τ₂) {σ} {η} e = eq-→ (evalSR τ₁ e) (evalSR τ₂ e)
evalSR (`∀ κ τ) {σ} {η} e = {!   !}
evalSR (μ τ) {σ} {η} e = eq-μ (reify-≋ (evalSR τ e))
evalSR (π ⇒ τ) {σ} {η} e = {!   !}
evalSR (lab l) {σ} {η} e = eq-refl
evalSR (l ▹ τ) {σ} {η} e = eq-▹ (evalSR l e) (reify-≋ (evalSR τ e)) 
evalSR ⌊ τ ⌋ {σ} {η} e = {!   !}
-- Yeah I need eta equality. Fuck.
evalSR Π {σ} {η} e = Π · ` Z , (eq-η , {!   !}) -- ⇑ (reify (π (reflect (` Z)))) , ({! π  !} , (λ ρ x → {!   !}))
evalSR Σ {σ} {η} e = {!   !}
evalSR (τ₁ <$> τ₂) {σ} {η} e = {!   !}        

idSR : ∀ {Δ₁} → SREnv ` (idEnv {Δ₁})
idSR α = reflect-≋ eq-refl

--------------------------------------------------------------------------------
-- Soundness claim

soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 
soundness τ = subst (_≡t ⇑ (⇓ τ)) (sub-id τ) ((reify-≋ (evalSR τ idSR)))