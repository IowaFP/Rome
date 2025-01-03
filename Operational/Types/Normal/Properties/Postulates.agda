module Rome.Operational.Types.Normal.Properties.Postulates where


open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
--

postulate
  -- renaming functor laws
  ren-id    : ∀ (τ : NormalType Δ κ) → ren id τ ≡ τ

  -- renaming commutes with beta-reduction.
  comm-ren-β      : (ρ : Renaming Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                    ren ρ (τ₁ β[ τ₂ ]) ≡ (ren (lift ρ) τ₁) β[ (ren ρ τ₂) ]

  -- weakening commutes with substitution.
  comm-weaken-sub : ∀ (σ : Sub Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ'} → 
                    weaken {κ₁ = κ'} (sub σ τ) ≡ sub (↑s σ) (weaken τ)

  comm-sub-↑      : ∀ (σ : Sub Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                      sub (↑s σ) τ 
                    ≡ 
                      reflect (Types.sub (Types.↑s (⇑ ∘ σ)) (⇑ τ)) (↑e (idEnv))

  comm-sub-β      : ∀ (σ : Sub Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                      sub σ (τ₁ β[ τ₂ ])
                    ≡ 
                      reflect (Types.sub (Types.↑s (⇑ ∘ σ)) (⇑ τ₁)) (↑e (idEnv))
                      β[ sub σ τ₂ ]

  -- Weakening followed by application of τ equals τ (eta expansion w.r.t. weakening)
  weaken-η   : ∀ (τ : NormalType Δ ★) {τ₂ : NormalType Δ κ} → τ ≡ (weaken τ) β[ τ₂ ]

  sub-id          : ∀ (τ : NormalType Δ κ) → sub (ne ∘ `) τ ≡ τ
