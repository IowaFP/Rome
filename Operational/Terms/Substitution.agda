module Rome.Operational.Terms.Substitution where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars


open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence 

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE 
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.GVars
open import Rome.Operational.Terms.Renaming


open Reasoning

--------------------------------------------------------------------------------
-- Term and entailment substitutions

Substitution : ∀ Γ₁ Γ₂ → SubstitutionₖNF Δ₁ Δ₂ → Set
Substitution Γ₁ Γ₂ σ = 
  (∀ {τ : NormalType _ ★} → Var Γ₁ τ → Term Γ₂ (subₖNF σ τ)) 
  × 
  (∀ {κ} {π : NormalPred _ R[ κ ]} → PVar Γ₁ π → Ent Γ₂ (subPredₖNF σ π))

--------------------------------------------------------------------------------
-- Lifting substitutions over times, predicates, and more!

lifts : ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} → 
            Substitution Γ₁ Γ₂ σ → Substitution (Γ₁ ,, κ) (Γ₂ ,, κ) (liftsₖNF σ)
lifts {σ = σ} (s , p) = 
  (λ { (K {τ = τ} x) →  conv (↻-weakenₖNF-subₖNF σ τ) (weakenTermByKind (s x))}) , 
  λ { (K x) → convEnt (↻-weakenPredₖNF-subPredₖNF σ _) (weakenEntByKind (p x)) }

liftsType : ∀ {σ : SubstitutionₖNF _ _} →
        Substitution Γ₁ Γ₂ σ → {τ : NormalType _ ★} → Substitution (Γ₁ , τ) (Γ₂ , subₖNF σ τ) σ
liftsType (s , p) = 
  (λ { Z → ` Z
      ; (S x) →  weakenTermByType (s x)}) , 
   λ { {κ} {π} (T x) → weakenEntByType (p x) }

liftsPred : ∀ {σ : SubstitutionₖNF _ _} →
            Substitution Γ₁ Γ₂ σ → {π : NormalPred _ R[ κ ]} → Substitution (Γ₁ ,,, π) (Γ₂ ,,, subPredₖNF σ π) σ
liftsPred (s , p) = 
  (λ { (P x) → weakenTermByPred (s x) }) , 
  (λ { Z → n-var Z
     ; (S x) → weakenEntByPred (p x) }) 

--------------------------------------------------------------------------------
-- This identity pops up as a nuisance. Needs renaming and refactoring

lemPred : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (s : Substitution Γ₁ Γ₂ σ) (π : NormalPred _ R[ κ ]) → 
         subPredₖNF σ π ≡ evalPred (subPredₖ (λ x₁ → ⇑ (σ x₁)) (⇑Pred π)) idEnv
lemPred σ s (ρ₁ · ρ₂ ~ ρ₃) = refl
lemPred σ s (ρ₁ ≲ ρ₂) = refl

--------------------------------------------------------------------------------
-- Defining substitution of variables in evidence and term variables in terms
-- and entailments.

sub : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → ∀ {τ} → 
      Term Γ₁ τ → Term Γ₂ (subₖNF σ τ)
subEnt : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → ∀ {π : NormalPred Δ₁ R[ κ ]} → 
          Ent Γ₁ π → Ent Γ₂ (subPredₖNF σ π)
sub σ (s , p) {τ} (` x) = s x
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
-- Aids!
sub {Γ₂ = Γ₂} σ s {x} (`ƛ {π = π} {τ = τ} M) = 
  `ƛ (subst 
        (λ x → Term (Γ₂ ,,, x) (subₖNF σ τ)) 
        (lemPred σ s π) 
        (sub σ (liftsPred {σ = σ} s) {τ} M))
sub σ s {x} (_·⟨_⟩ {κ = κ} {π = π} τ e) = sub σ s τ ·⟨ convEnt (lemPred σ s π) (subEnt σ s e) ⟩
sub σ s (prj M e) = prj (sub σ s M) (subEnt σ s e)
sub σ s (inj M e) = inj (sub σ s M) (subEnt σ s e)

subEnt σ (s , p) {π} (n-var x) = p x
subEnt σ s {π} n-refl = n-refl
subEnt σ s {π} (n-trans e₁ e₂) = n-trans (subEnt σ s e₁) (subEnt σ s e₂)
subEnt σ s {π} (n-·≲L e) = (n-·≲L (subEnt σ s e))
subEnt σ s {π} (n-·≲R e) = (n-·≲R (subEnt σ s e))
subEnt σ s {π} n-ε-R = n-ε-R
subEnt σ s {π} n-ε-L = n-ε-L
subEnt σ s {π} (n-≲lift {ρ₁ = ρ₁} {ρ₂ = ρ₂} {F = F} e) = 
  convEnt 
    (cong₂ _≲_ (↻-sub-⇓-<$> σ F ρ₁) (↻-sub-⇓-<$> σ F ρ₂)) 
    (n-≲lift {F = subₖNF σ F} (subEnt σ s e))   
subEnt σ s {π} (n-·lift {ρ₁ = ρ₁} {ρ₂ = ρ₂} {ρ₃ = ρ₃} {F = F} e) = 
  convEnt 
    (cong₃ _·_~_ 
      (↻-sub-⇓-<$> σ F ρ₁) 
      (↻-sub-⇓-<$> σ F ρ₂) 
      (↻-sub-⇓-<$> σ F ρ₃))  
      (n-·lift {F = subₖNF σ F} (subEnt σ s e))

extend : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → 
         {τ : NormalType Δ₁ ★} → 
         (M : Term Γ₂ (subₖNF σ τ)) → 
         Substitution (Γ₁ , τ) Γ₂ σ
extend σ (s , p) M = 
  (λ { Z    → M 
    ; (S x) → s x }) , 
   λ { (T x) → p x } 

lem : ∀ {τ} → Substitution (Γ ,, κ) Γ (extendₖNF (λ x → η-norm (` x)) τ)
lem {τ = τ} = 
  (λ { (K {τ = τ'} x) → conv (weakenₖNF-β-id τ') (` x) }) , 
  λ { (K {π = π} x) → convEnt (weakenPredₖNF-Β-id π) (n-var x) }

idSubstitution : Substitution Γ Γ idSubst
idSubstitution = (λ x → conv (sym (subₖNF-id _) ) (` x)) , λ x → convEnt (sym (subPredₖNF-id _)) (n-var x)

_β[_] : ∀ {τ₁ τ₂} → Term (Γ , τ₂) τ₁ → Term Γ τ₂ → Term Γ τ₁
_β[_] {τ₁ = τ₁} {τ₂} M N = 
  conv (subₖNF-id τ₁) 
  (sub idSubst 
    (extend 
      idSubst 
      idSubstitution
      (conv (sym (subₖNF-id τ₂)) N)) 
      M)

_β·[_] : ∀ {τ₁ : NormalType (Δ ,, κ) ★} → 
         Term (Γ ,, κ) τ₁ → (τ₂ : NormalType Δ κ) → Term Γ (τ₁ βₖNF[ τ₂ ])
M β·[ τ₂ ] =  sub (extendₖNF idSubst τ₂) lem M
  
   
