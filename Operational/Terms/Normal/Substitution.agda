module Rome.Operational.Terms.Normal.Substitution where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars


open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.SynAna
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

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Entailment.Properties
open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Renaming

open import Rome.Operational.Containment


open Reasoning

--------------------------------------------------------------------------------
-- Term and entailment substitutions

Substitution : ∀ Γ₁ Γ₂ → SubstitutionₖNF Δ₁ Δ₂ → Set
Substitution Γ₁ Γ₂ σ = 
  (∀ {τ : NormalType _ ★} → NormalVar Γ₁ τ → NormalTerm Γ₂ (subₖNF σ τ)) 
  × 
  (∀ {κ} {π : NormalPred _ R[ κ ]} → NormalPVar Γ₁ π → NormalEnt Γ₂ (subPredₖNF σ π))

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
-- This identity pops up as a nuisance. 

lemPred : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (s : Substitution Γ₁ Γ₂ σ) (π : NormalPred _ R[ κ ]) → 
         subPredₖNF σ π ≡ evalPred (subPredₖ (λ x₁ → ⇑ (σ x₁)) (⇑Pred π)) idEnv
lemPred σ s (ρ₁ · ρ₂ ~ ρ₃) = refl
lemPred σ s (ρ₁ ≲ ρ₂) = refl

--------------------------------------------------------------------------------
-- Substitution of evidence variables in entailments and term variables in terms.

sub : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → ∀ {τ} → 
      NormalTerm Γ₁ τ → NormalTerm Γ₂ (subₖNF σ τ)
subEnt : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → ∀ {π : NormalPred Δ₁ R[ κ ]} → 
          NormalEnt Γ₁ π → NormalEnt Γ₂ (subPredₖNF σ π)
sub σ (s , p) {τ} (` x) = s x
sub σ s {.(_ `→ _)} (`λ M) = `λ (sub σ (liftsType {σ = σ} s) M)
sub σ s {τ} (M · N) = sub σ s M · sub σ s N
sub σ s {.(`∀ _)} (Λ {τ = τ} M) = 
  Λ (conv (↻-lifted-subₖNF-eval σ τ) (sub (liftsₖNF σ) (lifts s) M))
sub σ s {.(τ₁ βₖNF[ τ₂ ])} (_·[_] {τ₂ = τ₁} M τ₂) = 
  conv 
    (sym (↻-subₖNF-β σ τ₁ τ₂)) (sub σ s M ·[ subₖNF σ τ₂ ])
sub σ s {.(μ F)} (In F M) = 
  In (subₖNF σ F) (conv (↻-subₖNF-·' σ F (μ F)) (sub σ s M))
sub σ s {_} (Out F M) = 
  conv (sym (↻-subₖNF-·' σ F (μ F))) (Out (subₖNF σ F) (sub σ s M))
sub σ s {x} (# l) = # (subₖNF σ l)
sub σ s {x} (l Π▹ τ) = sub σ s l Π▹ sub σ s τ
sub σ s {x} (τ Π/ l) = sub σ s τ Π/ sub σ s l
sub σ s {x} (l Σ▹ τ) = sub σ s l Σ▹ sub σ s τ
sub σ s {x} (τ Σ/ l) = sub σ s τ Σ/ sub σ s l
sub {Γ₂ = Γ₂} σ s {x} (`ƛ {π = π} {τ = τ} M) = 
  `ƛ (subst 
        (λ x → NormalTerm (Γ₂ ,,, x) (subₖNF σ τ)) 
        (lemPred σ s π) 
        (sub σ (liftsPred {σ = σ} s) {τ} M))
sub σ s {x} (_·⟨_⟩ {κ = κ} {π = π} τ e) = sub σ s τ ·⟨ convEnt (lemPred σ s π) (subEnt σ s e) ⟩
sub σ s (prj M e) = prj (sub σ s M) (subEnt σ s e)
sub σ s (inj M e) = inj (sub σ s M) (subEnt σ s e)
sub σ s ((M ⊹ N) e) = (sub σ s M ⊹ sub σ s N) (subEnt σ s e)
sub σ s ((M ▿ N) e) = (sub σ s M ▿ sub σ s N) (subEnt σ s e)
sub σ s (fix M) = fix (sub σ s M)
sub σ s (syn ρ φ M) = 
  conv (cong Π (↻-sub-⇓-<$> σ φ ρ)) 
    (syn (subₖNF σ ρ) (subₖNF σ φ) 
    (conv
      (trans 
        (trans 
          (sym (↻-⇓-sub σ (SynT (⇑ ρ) (⇑ φ))) ) 
          (cong ⇓ (sym (↻-sub-syn (⇑ ∘ σ) (⇑ ρ) (⇑ φ))))) 
        (completeness (eq-sym (SynT-cong-≡t (↻-sub-⇑ σ ρ) (↻-sub-⇑ σ φ))))) 
      (sub σ s M)))
sub σ s (ana ρ φ τ M) = 
  conv 
    (cong₂ _`→_ (cong Σ (↻-sub-⇓-<$> σ φ ρ)) refl) 
    (ana (subₖNF σ ρ) (subₖNF σ φ) (subₖNF σ τ) 
    (conv 
      ((trans 
        (trans 
          (sym (↻-⇓-sub σ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ) 
          (cong ⇓ (sym (↻-sub-ana (⇑ ∘ σ) (⇑ ρ) (⇑ φ) (⇑ τ))))) 
        (completeness (eq-sym (AnaT-cong-≡t (↻-sub-⇑ σ ρ) (↻-sub-⇑ σ φ) (↻-sub-⇑ σ τ)))))) 
      (sub σ s M)))
sub σ s (comp M n) = comp (sub σ s M) (subEnt σ s n)


subEnt σ s {π} (n-≲ {xs = xs} {ys} i) = 
  n-≲ 
    (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) 
    (⊆-cong (subₖ (⇑ ∘ σ)) (subRowₖ (⇑ ∘ σ)) (subRowₖ-isMap (⇑ ∘ σ)) 
    (⊆-cong ⇑ ⇑Row ⇑Row-isMap i)))
subEnt σ s {π} (n-· {xs = xs} {ys} {zs} i₁ i₂ i₃) = 
    n-· 
      (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) 
        (⊆-cong (subₖ (⇑ ∘ σ)) (subRowₖ (⇑ ∘ σ)) (subRowₖ-isMap (⇑ ∘ σ)) 
        (⊆-cong ⇑ ⇑Row ⇑Row-isMap i₁))) 
      (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) 
        (⊆-cong (subₖ (⇑ ∘ σ)) (subRowₖ (⇑ ∘ σ)) (subRowₖ-isMap (⇑ ∘ σ)) 
        (⊆-cong ⇑ ⇑Row ⇑Row-isMap i₂))) 
      (⊆-cong-or ⇓ ⇓Row (⇓Row-isMap idEnv) 
        (⊆-cong-or (subₖ (⇑ ∘ σ)) (subRowₖ (⇑ ∘ σ)) (subRowₖ-isMap (⇑ ∘ σ)) 
        (⊆-cong-or ⇑ ⇑Row ⇑Row-isMap i₃))) 
subEnt σ (s , p) {π} (n-var x) = p x
subEnt σ s {π} n-refl = n-refl
subEnt σ s {π} (n-trans e₁ e₂) = n-trans (subEnt σ s e₁) (subEnt σ s e₂)
subEnt σ s {π} (n-·≲L e) = (n-·≲L (subEnt σ s e))
subEnt σ s {π} (n-·≲R e) = (n-·≲R (subEnt σ s e))
subEnt σ s {π} n-ε-R = n-ε-R
subEnt σ s {π} n-ε-L = n-ε-L
subEnt σ s {π} (n-≲lift {ρ₁ = ρ₁} {ρ₂ = ρ₂} {F = F} e {x} {y} ρ₁-eq ρ₂-eq) 
  rewrite
    ρ₁-eq 
  | ρ₂-eq 
  | stability-<$> F ρ₁ 
  | stability-<$> F ρ₂ = 
    n-≲lift 
    {F = subₖNF σ F} 
    (subEnt σ s e) 
    (trans (sym (↻-sub-⇓-<$> σ F ρ₁)) (sym (stability-<$> (subₖNF σ F) (subₖNF σ ρ₁)))) 
    (trans (sym (↻-sub-⇓-<$> σ F ρ₂)) (sym (stability-<$> (subₖNF σ F) (subₖNF σ ρ₂))))
  
subEnt σ s {π} (n-·lift {ρ₁ = ρ₁} {ρ₂ = ρ₂} {ρ₃ = ρ₃} {F = F} e  ρ₁-eq ρ₂-eq ρ₃-eq) 
  rewrite
    ρ₁-eq 
  | ρ₂-eq 
  | ρ₃-eq 
  | stability-<$> F ρ₁ 
  | stability-<$> F ρ₂ 
  | stability-<$> F ρ₃ = 
    n-·lift 
    {F = subₖNF σ F} 
    (subEnt σ s e) 
    (trans (sym (↻-sub-⇓-<$> σ F ρ₁)) (sym (stability-<$> (subₖNF σ F) (subₖNF σ ρ₁)))) 
    (trans (sym (↻-sub-⇓-<$> σ F ρ₂)) (sym (stability-<$> (subₖNF σ F) (subₖNF σ ρ₂))))
    (trans (sym (↻-sub-⇓-<$> σ F ρ₃)) (sym (stability-<$> (subₖNF σ F) (subₖNF σ ρ₃))))
  

--------------------------------------------------------------------------------
-- Extending substitutions

extendByNormalTerm : (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → 
         {τ : NormalType Δ₁ ★} → 
         (M : NormalTerm Γ₂ (subₖNF σ τ)) → 
         Substitution (Γ₁ , τ) Γ₂ σ
extendByNormalTerm σ (s , p) M = 
  (λ { Z    → M 
    ; (S x) → s x }) , 
   λ { (T x) → p x } 

extendByEnt : 
         (σ : SubstitutionₖNF Δ₁ Δ₂) → Substitution Γ₁ Γ₂ σ → 
         {π : NormalPred Δ₁ R[ κ ]} → 
         (e : NormalEnt Γ₂ (subPredₖNF σ π)) → 
         Substitution (Γ₁ ,,, π) Γ₂ σ
extendByEnt σ (s , p) e = (λ { (P x) → s x }) , λ { Z → e
                                                  ; (S x) → p x }         


--------------------------------------------------------------------------------
-- Weakening of a substitution by a kind variable

lem : ∀ {τ} → Substitution (Γ ,, κ) Γ (extendₖNF (λ x → η-norm (` x)) τ)
lem {τ = τ} = 
  (λ { (K {τ = τ'} x) → conv (weakenₖNF-β-id τ') (` x) }) , 
  λ { (K {π = π} x) → convEnt (weakenPredₖNF-Β-id π) (n-var x) }


--------------------------------------------------------------------------------
-- The identity substitution

idSubstitution : Substitution Γ Γ idSubst
idSubstitution = (λ x → conv (sym (subₖNF-id _) ) (` x)) , λ x → convEnt (sym (subPredₖNF-id _)) (n-var x)

--------------------------------------------------------------------------------
-- β-reduction of a term by a term

_β[_] : ∀ {τ₁ τ₂} → NormalTerm (Γ , τ₂) τ₁ → NormalTerm Γ τ₂ → NormalTerm Γ τ₁
_β[_] {τ₁ = τ₁} {τ₂} M N = 
  conv (subₖNF-id τ₁) 
  (sub idSubst 
    (extendByNormalTerm 
      idSubst 
      idSubstitution
      (conv (sym (subₖNF-id τ₂)) N)) 
      M)

--------------------------------------------------------------------------------
-- β-reduction of a term by an entailment

_βπ[_] : ∀ {τ : NormalType Δ ★} {π : NormalPred Δ R[ κ ]} → NormalTerm (Γ ,,, π) τ → NormalEnt Γ π → NormalTerm Γ τ
_βπ[_] {τ = τ} {π} M e = 
  conv (subₖNF-id τ) 
    (sub idSubst 
      (extendByEnt 
        idSubst 
        idSubstitution 
        (convEnt ((sym (subPredₖNF-id π))) e)) 
        M)

--------------------------------------------------------------------------------
-- β-reduction of a term by a type

_β·[_] : ∀ {τ₁ : NormalType (Δ ,, κ) ★} → 
         NormalTerm (Γ ,, κ) τ₁ → (τ₂ : NormalType Δ κ) → NormalTerm Γ (τ₁ βₖNF[ τ₂ ])
M β·[ τ₂ ] =  sub (extendₖNF idSubst τ₂) lem M
  
   
