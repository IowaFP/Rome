module Rome.Operational.Types.Normal.Properties.Substitution where


open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Eta-expansion
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Stability


--------------------------------------------------------------------------------
--

postulate

  -- renaming commutes with beta-reduction.
  ↻-ren-β      : (ρ : Renaming Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                    ren ρ (τ₁ β[ τ₂ ]) ≡ (ren (lift ρ) τ₁) β[ (ren ρ τ₂) ]

  ↻-ren-app      : (ρ : Renaming Δ₁ Δ₂) (τ₁ : NeutralType Δ₁ (κ₁ `→ κ₂)) (τ₂ : NormalType Δ₁ κ₁) → 
                    renNE ρ (τ₁ · τ₂) ≡ (renNE ρ τ₁) · (ren ρ τ₂)

  -- weakening commutes with substitution.
  ↻-weaken-sub : ∀ (σ : Substitution Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ'} → 
                    weaken {κ₁ = κ'} (sub σ τ) ≡ sub (lifts σ) (weaken τ)

  ↻-sub-↑      : ∀ (σ : Substitution Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                      sub (lifts σ) τ 
                    ≡ 
                      eval (Types.sub (Types.lifts (⇑ ∘ σ)) (⇑ τ)) (lifte (idEnv))

  ↻-sub-β      : ∀ (σ : Substitution Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                      sub σ (τ₁ β[ τ₂ ])
                    ≡ 
                      eval (Types.sub (Types.lifts (⇑ ∘ σ)) (⇑ τ₁)) (lifte (idEnv))
                      β[ sub σ τ₂ ]

  -- Weakening followed by application of τ equals τ (eta expansion w.r.t. weakening)
  weaken-η   : ∀ (τ : NormalType Δ ★) {τ₂ : NormalType Δ κ} → τ ≡ (weaken τ) β[ τ₂ ]


id-when-ground : ∀ {κ} → Ground κ → (x : KVar Δ κ) → (⇑ ∘ η-norm ∘ `) x ≡ Types.` x
id-when-ground {κ = ★} g x = refl
id-when-ground {κ = L} g x = refl
id-when-ground {κ = R[ κ ]} g x = refl

sub-id-η-norm : ∀ (τ : NormalType Δ κ) → Types.sub (⇑ ∘ η-norm ∘ `) (⇑ τ) ≡ (⇑ τ)
sub-id-η-norm Unit = refl
sub-id-η-norm {κ = κ} (ne x {ground = g}) = {!!} -- trans (TypeProps.sub-cong (id-when-ground (toWitness g)) (⇑NE x)) (TypeProps.sub-id (⇑ (ne x)))
sub-id-η-norm (`λ τ) = cong Types.`λ (trans {!TypeProps.sub-cong TypeProps.lifts-id (⇑ τ)!} {!!})
sub-id-η-norm (τ `→ τ₁) = {!!}
sub-id-η-norm (`∀ κ τ) = {!!}
sub-id-η-norm (μ τ) = {!!}
sub-id-η-norm (π₁ ⇒ τ) = {!!}
sub-id-η-norm ε = {!!}
sub-id-η-norm (τ ▹ τ₁) = {!!}
sub-id-η-norm (lab l) = {!!}
sub-id-η-norm ⌊ τ ⌋ = {!!}
sub-id-η-norm (Π τ) = {!!}
sub-id-η-norm (ΠL τ) = {!!}
sub-id-η-norm (Σ τ) = {!!}
sub-id-η-norm (ΣL τ) = {!!}

sub-id          : ∀ (τ : NormalType Δ κ) → sub (η-norm ∘ `) τ ≡ τ
sub-id τ = {!stability τ!}

-- trans 
--   (cong ⇓ (sub-id-η-norm τ)) 
--   (stability τ)


cong-·' :  ∀ (σ : Substitution Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             sub σ (f ·' v) ≡ sub σ f ·' sub σ v
cong-·' σ (`λ f) v = trans (↻-sub-β σ f v) refl
