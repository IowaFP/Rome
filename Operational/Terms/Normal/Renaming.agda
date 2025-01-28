module Rome.Operational.Terms.Normal.Renaming where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars


import Rome.Operational.Types.Normal as Normal
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.GVars


private
  variable
    ρ : Types.Renaming Δ₁ Δ₂
    τ τ₁ τ₂ : NormalType Δ κ

--------------------------------------------------------------------------------
-- 5. Operational semantics.
--
-- 5.1 Renaming for terms

-- Renamings are functions from term variables to terms.
Renaming : ∀ Γ₁ Γ₂ → (ρ : Types.Renaming Δ₁ Δ₂) → Set
Renaming Γ₁ Γ₂ ρ = (∀ {τ : NormalType _ ★} → Var Γ₁ τ → Var Γ₂ (Normal.ren ρ τ))

renType : ∀ {Γ₁ Γ₂} {ρ : Types.Renaming Δ₁ Δ₂} → Renaming Γ₁ Γ₂ ρ → NormalType Δ₁ κ → NormalType Δ₂ κ
renType {ρ = ρ} P = Normal.ren ρ

-- -- -- We can lift a renaming both over a new term variable and over a new type variable.
lift : Renaming Γ₁ Γ₂ ρ → {τ : NormalType Δ₁ ★} → Renaming (Γ₁ , τ) (Γ₂ , Normal.ren ρ τ) ρ
lift P Z = Z
lift P (S x) = S (P x)

-- -- Needs type renaming composition functor law
liftKVar : Renaming Γ₁ Γ₂ ρ → Renaming (Γ₁ ,, κ) (Γ₂ ,, κ) (Types.lift ρ)
liftKVar {ρ = ρ} Ρ (T {τ = τ} x) = 
  convVar 
  (trans 
    (sym (ren-comp ρ S τ)) 
    (ren-comp S (Types.lift ρ) τ)) 
  (T (Ρ x))

ren : ∀ {τ} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      NormalTerm Γ₁ τ →
      NormalTerm Γ₂ (Normal.ren ρ τ)
ren P (` x) = ` (P x)
ren P (`λ M) = `λ (ren (lift P) M)
ren P (M · N) = (ren P M) · (ren P N)
ren P (Λ M) = Λ (ren (liftKVar P) M)
ren {ρ = ρ} P (_·[_] {τ₂ = τ₂} M τ) = conv (sym (↻-ren-β ρ τ₂ τ)) ((ren P M) ·[ Normal.ren ρ τ ])
ren P (roll τ M) = roll (renType P τ) {! ren P M  !} -- roll _ (conv (↻-ren-β _ τ _) (ren P M))
ren {ρ = ρ} P (unroll τ M) = {!   !} -- conv (sym (↻-ren-β _ τ (μ τ))) (unroll _ (ren P M))
ren P (lab l) = lab (renType P l)
ren P (l Π▹ M) = (ren P l) Π▹ (ren P M)
ren P (M Π/ l) = ren P M Π/ ren P l
ren P (l Σ▹ M) = (ren P l) Σ▹ (ren P M)
ren P (M Σ/ l) = ren P M Σ/ ren P l

weakenByType : NormalTerm Γ τ₁ → NormalTerm (Γ , τ₂) τ₁
weakenByType {τ₁ = τ₁} M = conv (ren-id τ₁) (ren ((convVar (sym (ren-id _))) ∘ S) M)

weakenByKind : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → NormalTerm (Γ ,, κ) (Normal.weaken τ)
weakenByKind = ren T


