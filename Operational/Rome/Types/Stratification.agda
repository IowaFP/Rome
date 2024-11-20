module Operational.Rome.Types.Stratification where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars
open import Operational.Rome.Types.Syntax

import Rome.Types.Syntax as Stratified
open import Operational.Rome.Kinds.Stratification

--------------------------------------------------------------------------------
--

stratify-type : Type Δ κ → (ℓ : Level) → Stratified.Type {ℓ = ℓ} {ι = ℓ} {!!} (stratify-kind κ ℓ)
stratify-type (` x) ℓ = {!!}
stratify-type (`λ τ) ℓ = {!!}
stratify-type (τ₁ · τ₂) ℓ = (stratify-type τ₁ ℓ) Stratified.·[ (stratify-type τ₂ ℓ) ]
stratify-type (τ₁ `→ τ₂) ℓ = {!!}
stratify-type (`∀ κ τ) ℓ = Stratified.`∀ {!stratify-kind κ ℓ!} {!stratify-type τ ℓ!}
stratify-type (μ F) ℓ = (Stratified.`λ _ {!( !}) Stratified.·[ {!!} ]
stratify-type (lab x) ℓ = Stratified.lab x
stratify-type (τ₁ ▹ τ₂) = {!!}
stratify-type (τ₁ R▹ τ₂) = {!!}
stratify-type ⌊ τ ⌋ ℓ = Stratified.⌊ (stratify-type τ ℓ) ⌋
stratify-type (Π τ) ℓ = Stratified.Π (stratify-type τ ℓ)
stratify-type (Σ τ) ℓ = Stratified.Σ (stratify-type τ ℓ)
