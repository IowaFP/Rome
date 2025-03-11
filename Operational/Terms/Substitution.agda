module Rome.Operational.Terms.Substitution where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars


open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence 

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Types.Semantic.NBE 

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.GVars
open import Rome.Operational.Terms.Renaming

open Reasoning

--------------------------------------------------------------------------------
--

-- Sub ...

Substitution : ∀ Γ₁ Γ₂ → SubstitutionₖNF Δ₁ Δ₂ → Set
Substitution Γ₁ Γ₂ σ = {τ : NormalType _ ★} → Var Γ₁ τ → Term Γ₂ (subₖNF σ τ)

lifts : ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} → 
            Substitution Γ₁ Γ₂ σ → Substitution (Γ₁ ,, κ) (Γ₂ ,, κ) (liftsₖNF σ)
lifts {σ = σ} s (T {τ = τ} x) = conv (↻-weakenₖNF-subₖNF σ τ) (weakenByKind (s x))

liftsType : ∀ {σ : SubstitutionₖNF _ _} →
        Substitution Γ₁ Γ₂ σ → {τ : NormalType _ ★} → Substitution (Γ₁ , τ) (Γ₂ , subₖNF σ τ) σ
liftsType s Z     = ` Z
liftsType s (S x) = weakenByType (s x)

sub : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → ∀ {τ} → 
      Term Γ₁ τ → Term Γ₂ (subₖNF σ τ)
sub σ s {τ} (` x) = s x
sub σ s {.(_ `→ _)} (`λ M) = `λ (sub σ (liftsType {σ = σ} s) M)
sub σ s {τ} (M · N) = sub σ s M · sub σ s N
sub σ s {.(`∀ _ _)} (Λ {τ = τ} M) = 
  Λ (conv (↻-lifted-subₖNF-eval σ τ) (sub (liftsₖNF σ) (lifts s) M))
sub σ s {.(τ₁ βₖNF[ τ₂ ])} (_·[_] {τ₂ = τ₁} M τ₂) = 
  conv 
    (sym (↻-subₖNF-β σ τ₁ τ₂)) (sub σ s M ·[ subₖNF σ τ₂ ])
sub σ s {.(μ F)} (In F M) = 
  In (subₖNF σ F) (conv (subₖNF-cong-·' σ F (μ F)) (sub σ s M))
sub σ s {_} (Out F M) = 
  conv (sym (subₖNF-cong-·' σ F (μ F))) (Out (subₖNF σ F) (sub σ s M))
sub σ s {x} (# l) = # l
sub σ s {x} (l Π▹ τ) = sub σ s l Π▹ sub σ s τ
sub σ s {x} (τ Π/ l) = sub σ s τ Π/ sub σ s l
sub σ s {x} (l Σ▹ τ) = sub σ s l Σ▹ sub σ s τ
sub σ s {x} (τ Σ/ l) = sub σ s τ Σ/ sub σ s l

extend : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → 
         {τ : NormalType Δ₁ ★} → 
         (M : Term Γ₂ (subₖNF σ τ)) → 
         Substitution (Γ₁ , τ) Γ₂ σ
extend σ s M Z = M
extend σ s M (S x) = s x

lem : ∀ {τ₂} → Substitution (Γ ,, κ) Γ (extendₖNF (λ x → η-norm (` x)) τ₂)
lem (T {τ = τ} x) = conv (weakenₖNF-β-id τ) (` x)

_β[_] : ∀ {τ₁ τ₂} → Term (Γ , τ₂) τ₁ → Term Γ τ₂ → Term Γ τ₁
_β[_] {τ₁ = τ₁} {τ₂} M N = 
  conv (subₖNF-id τ₁) 
  (sub idSubst 
    (extend 
      idSubst 
      (conv (sym (subₖNF-id _)) ∘ `) 
      (conv (sym (subₖNF-id τ₂)) N)) 
      M)

_β·[_] : ∀ {τ₁ : NormalType (Δ ,, κ) ★} → 
         Term (Γ ,, κ) τ₁ → (τ₂ : NormalType Δ κ) → Term Γ (τ₁ βₖNF[ τ₂ ])
M β·[ τ₂ ] =  sub (extendₖNF idSubst τ₂) lem M

 