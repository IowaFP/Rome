module Rome.Terms.Checking where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String ; _++_)

open import Rome.Kinds.Syntax
open import Rome.Kinds.Equality
open import Rome.Types.Syntax
open import Rome.Types.Checking
open import Rome.Terms.Syntax
open import Rome.Entailment.Syntax

import Rome.Pre as Pre

open import Shared.Monads.Fuck

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
-- 

-- Synthesis.
[_∣_∣_]⊢?_ : ∀ (Δ : KEnv) (Φ : PEnv Δ) (Γ : Env Δ) → Pre.Term → Fuck? (∃[ τ ] (Term Δ Φ Γ τ))

-- Checking.
[_∣_∣_]⊢_⦂?_ : ∀ (Δ : KEnv) (Φ : PEnv Δ) (Γ : Env Δ) → Pre.Term → (τ : Type Δ ★) → Fuck? (Term Δ Φ Γ τ)

[_∣_∣_]⊢?_ = {!!}


-- vars.
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.var x ⦂? τ = do
  (τ' , v ) ← x ∈[ Δ ∣ Γ ]
  -- must check if τ ≡ τ'
  yiss (var {!!})

-- binding sites.
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`λ x M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`ƛ x M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`Λ x M ⦂? τ = {!!}

-- applications.
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⦂ M₁ · x ⦂? τ = {!!}

[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⦂ x ·[ x₁ ] ⦂? τ = {!!}

[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⦂ x ·⟨ x₁ ⟩ ⦂? τ = {!!}

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
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⊹ M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.prj M M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Π M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Π⁻¹ M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Σ M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Σ⁻¹ M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.inj M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.▿ M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.syn M M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.ana x x₁ M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.fold M M₁ M₂ M₃ ⦂? τ = {!!}

-- recursion
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.In M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Out M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M ⦂? τ = wtf? "M does not have type τ. (I'll write printers for these later.)"
