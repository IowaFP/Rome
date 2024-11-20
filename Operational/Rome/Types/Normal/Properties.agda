module Operational.Rome.Types.Normal.Properties where

open import Operational.Rome.Prelude

open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

import Operational.Rome.Types as Types
import Operational.Rome.Types.Properties as TypeProps
open TypeProps using (↑-cong ; ↑-id ; ↑-comp)
open import Operational.Rome.Types.Renaming using (Renaming ; _≈_ ; ↑)

open import Operational.Rome.Types.Normal

--------------------------------------------------------------------------------
-- Renaming respects congruence of Renamings

ren-cong-ne :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                 (τ : NeutralType Δ₁ κ) → renNE ρ₁ τ ≡ renNE ρ₂ τ
ren-cong    :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                 (τ : NormalType Δ₁ κ) → ren ρ₁ τ ≡ ren ρ₂ τ

ren-cong-ne eq (` x) rewrite eq x = refl
ren-cong-ne eq (ν · τ) rewrite
    ren-cong-ne eq ν
  | ren-cong eq τ = refl

ren-cong eq (ne ν) rewrite 
  ren-cong-ne eq ν = refl
ren-cong eq (`λ τ) rewrite 
  ren-cong (TypeProps.↑-cong eq) τ = refl 
ren-cong eq (τ₁ `→ τ₂) rewrite 
    ren-cong eq τ₁ 
  | ren-cong eq τ₂ = refl
ren-cong eq (`∀ κ τ) rewrite 
  ren-cong (TypeProps.↑-cong eq) τ = refl 
ren-cong eq (μ τ) rewrite 
  ren-cong (TypeProps.↑-cong eq) τ = refl 

--------------------------------------------------------------------------------
-- Renaming preserves identities (functor law #1)

ren-id    : ∀ (τ : NormalType Δ κ) → ren id τ ≡ τ
ren-id-ne : ∀ (τ : NeutralType Δ κ) → renNE id τ ≡ τ

ren-id-ne (` x) = refl
ren-id-ne (τ₁ · τ₂) rewrite
    ren-id-ne τ₁
  | ren-id τ₂ = refl

ren-id (ne ν) rewrite ren-id-ne ν = refl
ren-id (`λ τ) rewrite 
    ren-cong ↑-id τ 
  | ren-id τ = refl 
ren-id (τ₁ `→ τ₂) rewrite 
    ren-id τ₁ 
  | ren-id τ₂ = refl
ren-id (`∀ κ τ) rewrite 
    ren-cong ↑-id τ 
  | ren-id τ = refl
ren-id (μ τ) rewrite 
    ren-cong ↑-id τ 
  | ren-id τ = refl

--------------------------------------------------------------------------------
-- Renaming preserves Composition (functor law #2)

ren-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
           ∀ (τ : NormalType Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
ren-comp-ne : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
              ∀ (τ : NeutralType Δ₁ κ) → renNE (ρ₂ ∘ ρ₁) τ ≡ renNE ρ₂ (renNE ρ₁ τ)
ren-comp-ne ρ₁ ρ₂ (` x) = refl
ren-comp-ne ρ₁ ρ₂ (ν · τ) rewrite
    ren-comp-ne ρ₁ ρ₂ ν
  | ren-comp ρ₁ ρ₂ τ = refl

ren-comp ρ₁ ρ₂ (ne ν) rewrite ren-comp-ne ρ₁ ρ₂ ν  = refl
ren-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (ren-cong (↑-comp ρ₁ ρ₂) τ) (ren-comp (↑ ρ₁) (↑ ρ₂) τ) = refl
ren-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (`∀ κ τ) rewrite
  (trans (ren-cong (↑-comp ρ₁ ρ₂) τ) (ren-comp (↑ ρ₁) (↑ ρ₂) τ)) = refl
ren-comp ρ₁ ρ₂ (μ τ) rewrite
  (trans (ren-cong (↑-comp ρ₁ ρ₂) τ) (ren-comp (↑ ρ₁) (↑ ρ₂) τ)) = refl

--------------------------------------------------------------------------------
-- Auxiliary lemmas
-- 

postulate
  -- renaming commutes with beta-reduction.
  comm-ren-β      : (ρ : Renaming Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
               ren ρ (τ₁ β[ τ₂ ]) ≡ (ren (↑ ρ) τ₁) β[ (ren ρ τ₂) ]
  -- weakening commutes with substitution.
  comm-weaken-sub : ∀ (σ : Sub Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ'} → 
                    weaken {κ₁ = κ'} (sub σ τ) ≡ sub (↑s σ) (weaken τ)

  comm-sub-↑      : ∀ (σ : Sub Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                      sub (↑s σ) τ 
                    ≡ 
                      eval (Types.sub (Types.↑s (embed ∘ σ)) (embed τ)) (↑e (idEnv))

  comm-sub-β      : ∀ (σ : Sub Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                      sub σ (τ₁ β[ τ₂ ])
                    ≡ 
                      eval (Types.sub (Types.↑s (embed ∘ σ)) (embed τ₁)) (↑e (idEnv))
                      β[ sub σ τ₂ ]

  -- Weakening followed by application of τ equals τ (eta expansion w.r.t. weakening)
  weaken-η   : ∀ (τ : NormalType Δ ★) {τ₂ : NormalType Δ κ} → τ ≡ (weaken τ) β[ τ₂ ]

  sub-id          : ∀ (τ : NormalType Δ κ) → sub (ne ∘ `) τ ≡ τ
