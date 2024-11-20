module Operational.Rome.Terms.Normal.Renaming where

open import Operational.Rome.Prelude

open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars


open import Operational.Rome.Types.Normal.Syntax
import Operational.Rome.Types as Types
import Operational.Rome.Types.Normal as Normal
open import Operational.Rome.Types.Normal.Properties
open import Operational.Rome.Terms.Normal.Syntax
open import Operational.Rome.Terms.Normal.GVars


private
  variable
    ρ : Types.Renaming Δ₁ Δ₂
    τ τ₁ τ₂ : NormalType Δ κ

--------------------------------------------------------------------------------
-- 5. Operational semantics.
--
-- 5.1 Renaming for terms

-- Renamings are functions from term variables to terms.
Renaming : ∀ Γ₁ Γ₂ → Types.Renaming Δ₁ Δ₂ → Set
Renaming Γ₁ Γ₂ ρ = {τ : NormalType _ ★} → Var Γ₁ τ → Var Γ₂ (Normal.ren ρ τ)

-- -- We can ↑ a renaming both over a new term variable and over a new type variable.
↑ : Renaming Γ₁ Γ₂ ρ → {τ : NormalType Δ₁ ★} → Renaming (Γ₁ , τ) (Γ₂ , Normal.ren ρ τ) ρ
↑ ρ Z = Z
↑ ρ (S x) = S (ρ x)

-- -- Needs type renaming composition functor law
↑KVar : Renaming Γ₁ Γ₂ ρ → Renaming (Γ₁ ,, κ) (Γ₂ ,, κ) (Types.↑ ρ)
↑KVar {ρ = ρ} Ρ (T {τ = τ} x) = 
  convVar 
  (trans 
    (sym (ren-comp ρ S τ)) 
    (ren-comp S (Types.↑ ρ) τ)) 
  (T (Ρ x))

ren : ∀ {τ} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      NormalTerm Γ₁ τ →
      NormalTerm Γ₂ (Normal.ren ρ τ)
ren Ρ (` x) = ` (Ρ x)
ren Ρ (`λ M) = `λ (ren (↑ Ρ) M)
ren Ρ (M · N) = (ren Ρ M) · (ren Ρ N)
ren Ρ (Λ M) = Λ (ren (↑KVar Ρ) M)
ren {ρ = ρ} Ρ (_·[_] {τ₂ = τ₂} M τ) = conv (sym (comm-ren-β ρ τ₂ τ)) ((ren Ρ M) ·[ Normal.ren ρ τ ])
ren Ρ (roll τ M) = roll _ (conv (comm-ren-β _ τ _) (ren Ρ M))
ren {ρ = ρ} Ρ (unroll τ M) = conv (sym (comm-ren-β _ τ (μ τ))) (unroll _ (ren Ρ M))

weakenByType : NormalTerm Γ τ₁ → NormalTerm (Γ , τ₂) τ₁
weakenByType {τ₁ = τ₁} M = conv (ren-id τ₁) (ren ((convVar (sym (ren-id _))) ∘ S) M)

weakenByKind : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → NormalTerm (Γ ,, κ) (Normal.weaken τ)
weakenByKind = ren T


