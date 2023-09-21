{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Terms.Checking where

open import Prelude

open import Rome.Kinds.Syntax
-- open import Rome.Kinds.Equality
open import Rome.Entailment.Syntax
open import Rome.Entailment.Checking
open import Rome.Equivalence.Syntax
open import Rome.Equivalence.Checking
open import Rome.Types.Syntax
open import Rome.Types.Checking
open import Rome.Terms.Syntax

import Rome.Pre as Pre

open import Shared.Monads.Fuck
open import Function

--------------------------------------------------------------------------------
-- Var lookup

-- Syntax here means _∈[_] is TVar lookup and _∈[_∣_] is Var lookup, and so
-- later, should _∈[_∣_∣_] be PVar lookup? This is sort of janky, but I also
-- dislike indexing every name with κ, τ, and π.
_∈[_∣_] : (n : ℕ) (Δ : KEnv) (Γ : Env Δ) → Fuck? (∃[ τ ] (Var Γ τ))
n ∈[ Δ ∣ ε ] = wtf? 
  ("You tried to look up the variable " ++ (show n) ++ " in an empty environment")
zero ∈[ Δ ∣ Γ , τ ] = yiss (τ , Z)
suc n ∈[ Δ ∣ Γ , τ ] = do
  (τ , v) ← n ∈[ Δ ∣ Γ ]
  yiss (τ , (S v))

--------------------------------------------------------------------------------
-- Type synthesis & checking signatures.
-- (mutually recursive.)

-- Synthesis.
[_∣_∣_]⊢?_ : ∀ (Δ : KEnv) (Φ : PEnv Δ) (Γ : Env Δ) → Pre.Term → Fuck? (∃[ τ ] (Term Δ Φ Γ τ))

-- Checking.
[_∣_∣_]⊢_⦂?_ : ∀ (Δ : KEnv) (Φ : PEnv Δ) (Γ : Env Δ) → Pre.Term → (τ : Type Δ ★) → Fuck? (Term Δ Φ Γ τ)

--------------------------------------------------------------------------------
-- Synthesis.

-- vars.
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.var x = do
  (τ , v) ← x ∈[ Δ ∣ Γ ]
  yiss (τ , (var v))
-- bindings.
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.`λ x M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.`ƛ x M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.`Λ x M = {!!}

-- applications.
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre.· x) = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre.·[ x ]) = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre.·⟨ x ⟩) = {!!}

[ Δ ∣ Φ ∣ Γ ]⊢? Pre.lab l = yiss (⌊ lab l ⌋ , lab (lab l))
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre.▹ M₁) = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre./ M₁) = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.∅ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre.⊹ M₁) = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.prj M M₁ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.Π M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.Π⁻¹ M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.Σ M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.Σ⁻¹ M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.inj M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? (M Pre.▿ M₁) = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.syn M M₁ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.ana x x₁ M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.fold M M₁ M₂ M₃ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.In M = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢? Pre.Out M = {!!}

--------------------------------------------------------------------------------
-- Checking.
postulate
  -- this may be a doozy.
  mkPred : ∀ {Δ} {κ} → Pre.Pred → Pred Δ κ
  _≡p?_ : ∀ {Δ} {κ} → (π₁ π₂ : Pred Δ κ) → Fuck? (π₁ ≡p π₂)
  
-- vars.
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.var x ⦂? τ = do
  (τ' , v ) ← x ∈[ Δ ∣ Γ ]
  eq ← τ' ≡? τ
  yiss (t-≡ (var v) eq)

-- binding sites.
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`λ u M ⦂? (υ `→ τ) = do
  ⊢u ← Δ ⊢ u ⦂? ★
  _ ← ⊢u ≡? υ
  ⊢M ← [ Δ ∣ Φ ∣ (Γ , υ) ]⊢ M ⦂? τ
  yiss (`λ υ ⊢M)
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`Λ u M ⦂? (`∀ κ τ) = do
  ⊢υ ← Δ ⊢ u ⦂? κ
  ⊢M ← [ (Δ , κ) ∣ weakΦ Φ ∣ weakΓ Γ ]⊢ M ⦂? τ
  yiss (`Λ κ ⊢M)
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`ƛ p M ⦂? (π ⇒ τ) = do
  eq ← (mkPred p) ≡p? π
  ⊢M ← [ Δ ∣ (Φ , π) ∣ Γ ]⊢ M ⦂? τ
  yiss (`ƛ π ⊢M)
  
-- applications.
[ Δ ∣ Φ ∣ Γ ]⊢ (M Pre.· N) ⦂? τ = do
  ( υ₁ `→ υ₂ , ⊢M) ← [ Δ ∣ Φ ∣ Γ ]⊢? M
  eq ← υ₂ ≡? τ
  ⊢N ← [ Δ ∣ Φ ∣ Γ ]⊢ N ⦂? υ₁
  yiss (t-≡ (⊢M · ⊢N) eq)
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.·[ N ] ⦂? τ = {!!}

[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.·⟨ N ⟩ ⦂? τ = {!!}

-- label and row singletons.
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.lab l ⦂? (⌊ ℓ ⌋) = do
  yiss (lab ℓ)

[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.▹ N ⦂? (ℓ ▹ τ) = do
  l ← [ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? ⌊ ℓ ⌋
  n ←  [ Δ ∣ Φ ∣ Γ ]⊢ N ⦂? τ
  yiss (l ▹ n)
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre./ N ⦂? τ = {!!}
-- Need to check if M has type (ℓ ▹ τ)
-- and N has type ⌊ ℓ ⌋, which means
-- synthesizing ⌊ ℓ ⌋.
--  do
  -- l ← [ Δ | Γ ]⊢ N ⦂? ⌊ ℓ ⌋
  -- m ← [ Δ | Γ ]⊢ M ⦂? (ℓ ▹ τ)
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.∅ ⦂? ∅ = yiss ∅

-- Row primitives.
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⊹ N ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.prj M M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Π M ⦂? (Π (τ R▹ υ))  = Π <$> [ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? (τ ▹ υ)
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Π⁻¹ M ⦂? (τ ▹ υ) = Π⁻¹ <$> [ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? (Π (τ R▹ υ))
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Σ M ⦂? (Σ (τ R▹ υ))  = Σ <$> [ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? (τ ▹ υ)
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Σ⁻¹ M ⦂? (τ ▹ υ) = Σ⁻¹ <$> [ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? (Σ (τ R▹ υ))
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.inj M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.▿ M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.syn M M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.ana f M N ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.fold M M₁ M₂ M₃ ⦂? τ = {!!}

-- recursion
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.In M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Out M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? τ = wtf? "M does not have type τ. (I'll write printers for these later.)"
