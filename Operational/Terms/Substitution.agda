module Rome.Operational.Terms.Substitution where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars



import Rome.Operational.Types as Types
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties
open import Rome.Operational.Types.Normal.Eta-expansion
import Rome.Operational.Types.Normal.Substitution as T

open import Rome.Operational.Types.Semantic.NBE 

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Renaming

open Reasoning

--------------------------------------------------------------------------------
--

-- Sub ...

Sub : ∀ Γ₁ Γ₂ → T.Substitution Δ₁ Δ₂ → Set
Sub Γ₁ Γ₂ σ = {τ : NormalType _ ★} → Var Γ₁ τ → Term Γ₂ (T.sub σ τ)

lifts : ∀ {σ : T.Substitution Δ₁ Δ₂} → 
            Sub Γ₁ Γ₂ σ → Sub (Γ₁ ,, κ) (Γ₂ ,, κ) (T.lifts σ)
lifts {σ = σ} s (T {τ = τ} x) = conv (↻-weaken-sub σ τ) (weakenByKind (s x))

lifts-τ : ∀ {σ : T.Substitution _ _} →
        Sub Γ₁ Γ₂ σ → {τ : NormalType _ ★} → Sub (Γ₁ , τ) (Γ₂ , T.sub σ τ) σ
lifts-τ s Z     = ` Z
lifts-τ s (S x) = weakenByType (s x)

sub : (σ : T.Substitution Δ₁ Δ₂) → Sub Γ₁ Γ₂ σ → ∀ {τ} → 
      Term Γ₁ τ → Term Γ₂ (T.sub σ τ)
sub σ s {τ} (` x) = s x
sub σ s {.(_ `→ _)} (`λ M) = `λ (sub σ (lifts-τ {σ = σ} s) M)
sub σ s {τ} (M · N) = sub σ s M · sub σ s N
sub σ s {.(`∀ _ _)} (Λ {τ = τ} M) = 
  Λ (conv (↻-sub-↑ σ τ) (sub (T.lifts σ) (lifts s) M))
sub σ s {.(τ₁ T.β[ τ₂ ])} (_·[_] {τ₂ = τ₁} M τ₂) = 
  conv (sym (↻-sub-β σ τ₁ τ₂)) (sub σ s M ·[ T.sub σ τ₂ ])
sub σ s {.(μ F)} (roll F M) = 
  roll (T.sub σ F) (conv (cong-·' σ F (μ F)) (sub σ s M))
sub σ s {_} (unroll F M) = 
  conv (sym (cong-·' σ F (μ F))) (unroll (T.sub σ F) (sub σ s M))
sub σ s {x} (lab l) = lab (T.sub σ l)
sub σ s {x} (l Π▹ τ) = sub σ s l Π▹ sub σ s τ
sub σ s {x} (τ Π/ l) = sub σ s τ Π/ sub σ s l
sub σ s {x} (l Σ▹ τ) = sub σ s l Σ▹ sub σ s τ
sub σ s {x} (τ Σ/ l) = sub σ s τ Σ/ sub σ s l

extend : (σ : T.Substitution Δ₁ Δ₂) → Sub Γ₁ Γ₂ σ → 
         {τ : NormalType Δ₁ ★} → 
         (M : Term Γ₂ (T.sub σ τ)) → 
         Sub (Γ₁ , τ) Γ₂ σ
extend σ s M Z = M
extend σ s M (S x) = s x
       

lem : ∀ {τ₂} → Sub (Γ ,, κ) Γ (T.extend (λ x → η-norm (` x)) τ₂)
lem (T {τ = τ} x) = conv (weaken-η τ) (` x)

_β[_] : ∀ {τ₁ τ₂} → Term (Γ , τ₂) τ₁ → Term Γ τ₂ → Term Γ τ₁
_β[_] {τ₁ = τ₁} {τ₂} M N = 
  conv (sub-id τ₁) 
  (sub 
    (η-norm ∘ `) 
    (extend 
      (η-norm ∘ `) 
      (conv (sym (sub-id _)) ∘ `) 
      (conv (sym (sub-id τ₂)) N)) 
      M)

_β·[_] : ∀ {τ₁ : NormalType (Δ ,, κ) ★} → 
         Term (Γ ,, κ) τ₁ → (τ₂ : NormalType Δ κ) → Term Γ (τ₁ T.β[ τ₂ ])
M β·[ τ₂ ] =  sub (T.extend (η-norm ∘ `) τ₂) lem M

