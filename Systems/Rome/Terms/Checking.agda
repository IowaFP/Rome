module Rome.Terms.Checking where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)
open import Data.Nat using (ℕ ; zero ; suc)

open import Rome.Kinds.Syntax
open import Rome.Kinds.Equality
open import Rome.Types.Syntax
open import Rome.Types.Checking
open import Rome.Terms.Syntax
open import Rome.Entailment.Syntax

import Rome.Pre as Pre

open import Shared.Lib.Monads.Fuck

--------------------------------------------------------------------------------
-- 

_∣_∣_⊢?_ : ∀ (Δ : KEnv) (Φ : PEnv Δ) (Γ : Env Δ) → Pre.Term → Fuck? (Term Δ Φ Γ)
[_∣_∣_]⊢_⦂?_ : ∀ (Δ : KEnv) (Φ : PEnv Δ) (Γ : Env Δ) → Pre.Term → (τ : Pre.Type) → Fuck? (Term Δ Φ Γ)
_∣_∣_⊢?_ = {!!}

[ Δ ∣ Φ ∣ Γ ]⊢ Pre.var x ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`λ x M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⦂ M₁ · x ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`Λ x M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⦂ x ·[ x₁ ] ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.`ƛ x M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.⦂ x ·⟨ x₁ ⟩ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.lab l ⦂? t = do
  τ ← Δ ⊢ t ⦂? L
  yiss (lab τ)
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre.▹ M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ M Pre./ M₁ ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.∅ ⦂? τ = {!!}
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
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.In M ⦂? τ = {!!}
[ Δ ∣ Φ ∣ Γ ]⊢ Pre.Out M ⦂? τ = {!!}
