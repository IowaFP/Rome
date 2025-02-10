module Rome.Operational.Terms.Normal.Substitution where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars



import Rome.Operational.Types as Types
import Rome.Operational.Types.Normal as Normal
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Renaming

open Reasoning

--------------------------------------------------------------------------------
--

-- Sub ...

Sub : ∀ Γ₁ Γ₂ → Normal.Sub Δ₁ Δ₂ → Set
Sub Γ₁ Γ₂ σ = {τ : NormalType _ ★} → Var Γ₁ τ → NormalTerm Γ₂ (Normal.sub σ τ)

lifts : ∀ {σ : Normal.Sub Δ₁ Δ₂} → 
            Sub Γ₁ Γ₂ σ → Sub (Γ₁ ,, κ) (Γ₂ ,, κ) (Normal.lifts σ)
lifts {σ = σ} Σ (T {τ = τ} x) = conv (comm-weaken-sub σ τ) (weakenByKind (Σ x))

lifts-τ : ∀ {σ : Normal.Sub _ _} →
        Sub Γ₁ Γ₂ σ → {τ : NormalType _ ★} → Sub (Γ₁ , τ) (Γ₂ , Normal.sub σ τ) σ
lifts-τ Σ Z     = ` Z
lifts-τ Σ (S x) = weakenByType (Σ x)

sub : (σ : Normal.Sub Δ₁ Δ₂) → Sub Γ₁ Γ₂ σ → ∀ {τ} → 
      NormalTerm Γ₁ τ → NormalTerm Γ₂ (Normal.sub σ τ)
sub σ Σ {τ} (` x) = Σ x
sub σ Σ {.(_ `→ _)} (`λ M) = `λ (sub σ (lifts-τ {σ = σ} Σ) M)
sub σ Σ {τ} (M · N) = sub σ Σ M · sub σ Σ N
sub σ Σ {.(`∀ _ _)} (Λ {τ = τ} M) = 
  Λ (conv (comm-sub-↑ σ τ) (sub (Normal.lifts σ) (lifts Σ) M))
sub σ Σ {.(τ₁ Normal.β[ τ₂ ])} (_·[_] {τ₂ = τ₁} M τ₂) = 
  conv (sym (comm-sub-β σ τ₁ τ₂)) (sub σ Σ M ·[ Normal.sub σ τ₂ ] )
sub σ Σ {.(μ τ)} (roll τ M) = 
  roll _ (conv (comm-sub-β σ τ (μ τ)) (sub σ Σ M))
sub σ Σ {.(τ Normal.β[ μ τ ])} (unroll τ M) = 
  conv (sym (comm-sub-β σ τ (μ τ))) (unroll _ (sub σ Σ M))

extend : (σ : Normal.Sub Δ₁ Δ₂) → Sub Γ₁ Γ₂ σ → 
         {τ : NormalType Δ₁ ★} → 
         (M : NormalTerm Γ₂ (Normal.sub σ τ)) → 
         Sub (Γ₁ , τ) Γ₂ σ
extend σ Σ M Z = M
extend σ Σ M (S x) = Σ x
       

lem : ∀ {τ₂} → Sub (Γ ,, κ) Γ (Normal.extend (λ x → ne (` x)) τ₂)
lem (T {τ = τ} x) = conv (weaken-η τ) (` x)

_β[_] : ∀ {τ₁ τ₂} → NormalTerm (Γ , τ₂) τ₁ → NormalTerm Γ τ₂ → NormalTerm Γ τ₁
_β[_] {τ₁ = τ₁} {τ₂} M N = 
  conv (sub-id τ₁) 
  (sub 
    (ne ∘ `) 
    (extend 
      (ne ∘ `) 
      (conv (sym (sub-id _)) ∘ `) 
      (conv (sym (sub-id τ₂)) N)) 
      M)

_β·[_] : ∀ {τ₁ : NormalType (Δ ,, κ) ★} → 
         NormalTerm (Γ ,, κ) τ₁ → (τ₂ : NormalType Δ κ) → NormalTerm Γ (τ₁ Normal.β[ τ₂ ])
M β·[ τ₂ ] =  sub (Normal.extend (ne ∘ `) τ₂) lem M

