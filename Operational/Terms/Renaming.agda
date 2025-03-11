{-# OPTIONS --allow-unsolved-metas #-}

module Rome.Operational.Terms.Renaming where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Renaming

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.GVars

open import Rome.Operational.Types.Theorems.Completeness

private
  variable
    ρ : Renamingₖ Δ₁ Δ₂
    τ τ₁ τ₂ : NormalType Δ κ

--------------------------------------------------------------------------------
-- 5. Operational semantics.
--
-- 5.1 Renaming for terms

-- Renamings are functions from term variables to terms.
Renaming : ∀ Γ₁ Γ₂ → Renamingₖ Δ₁ Δ₂ → Set
Renaming Γ₁ Γ₂ ρ = (∀ {τ : NormalType _ ★} → Var Γ₁ τ → Var Γ₂ (renₖNF ρ τ))

renType : ∀ {Γ₁ Γ₂} {ρ : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ ρ → NormalType Δ₁ κ → NormalType Δ₂ κ
renType {ρ = ρ} P = renₖNF ρ

lift : Renaming Γ₁ Γ₂ ρ → {τ : NormalType Δ₁ ★} → Renaming (Γ₁ , τ) (Γ₂ , renₖNF ρ τ) ρ
lift P Z = Z
lift P (S x) = S (P x)

liftKVar : Renaming Γ₁ Γ₂ ρ → Renaming (Γ₁ ,, κ) (Γ₂ ,, κ) (liftₖ ρ)
liftKVar {ρ = ρ} Ρ (T {τ = τ} x) = 
  convVar 
  (trans 
    (sym (renₖNF-comp ρ S τ)) 
    (renₖNF-comp S (liftₖ ρ) τ)) 
  (T (Ρ x))

ren : ∀ {τ} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      Term Γ₁ τ →
      Term Γ₂ (renₖNF ρ τ)
ren P (` x) = ` (P x)
ren P (`λ M) = `λ (ren (lift P) M)
ren P (M · N) = (ren P M) · (ren P N)
ren P (Λ M) = Λ (ren (liftKVar P) M)
ren {ρ = ρ} P (_·[_] {τ₂ = τ₂} M τ) = conv (sym (↻-renₖNF-β ρ τ₂ τ)) ((ren P M) ·[ renₖNF ρ τ ])
ren {ρ = ρ} P (In F@(`λ τ) N) = 
  In 
    (renType P F) 
    (conv (↻-renₖNF-β  ρ τ (μ F)) 
      (ren P N))
ren {ρ = ρ} P (Out F@(`λ τ) M) = conv (sym (↻-renₖNF-β ρ τ ((μ F)))) (Out (renType P F) (ren P M))
ren P (# l) = # l
ren P (l Π▹ M) = (ren P l) Π▹ (ren P M)
ren P (M Π/ l) = ren P M Π/ ren P l
ren P (l Σ▹ M) = (ren P l) Σ▹ (ren P M)
ren P (M Σ/ l) = ren P M Σ/ ren P l

weakenByType : Term Γ τ₁ → Term (Γ , τ₂) τ₁
weakenByType {τ₁ = τ₁} M = conv (renₖNF-id τ₁) (ren ((convVar (sym (renₖNF-id _))) ∘ S) M)

weakenByKind : ∀ {τ : NormalType Δ ★} → Term Γ τ → Term (Γ ,, κ) (weakenₖNF τ)
weakenByKind = ren T


