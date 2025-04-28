{-# OPTIONS --allow-unsolved-metas #-}

module Rome.Operational.Terms.Normal.Renaming where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Equivalence
open import Rome.Operational.Types.Properties.Equivalence

open import Rome.Operational.Types.Renaming

open import Rome.Operational.Terms.Syntax

open import Rome.Operational.Terms.Normal.Syntax

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Containment

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : NormalContext Δ
    ρ : Renamingₖ Δ₁ Δ₂
    τ τ₁ τ₂ : NormalType Δ κ

--------------------------------------------------------------------------------
-- Renamings are functions from term variables to term variables
-- and from evidence variables to evidence variables

Renaming : ∀ Γ₁ Γ₂ → Renamingₖ Δ₁ Δ₂ → Set
Renaming Γ₁ Γ₂ ρ = 
  (∀ {τ : NormalType _ ★} → NormalVar Γ₁ τ → NormalVar Γ₂ (renₖNF ρ τ))
  ×
  (∀ {κ} {π : NormalPred _ R[ κ ]} → NormalPVar Γ₁ π → NormalPVar Γ₂ (renPredₖNF ρ π))

renType : ∀ {Γ₁ Γ₂} {ρ : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ ρ → NormalType Δ₁ κ → NormalType Δ₂ κ
renType {ρ = ρ} R = renₖNF ρ

renPred : ∀ {Γ₁ Γ₂} {ρ : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ ρ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
renPred {ρ = ρ} R = renPredₖNF ρ

--------------------------------------------------------------------------------
-- Lifting of renamings

lift : Renaming Γ₁ Γ₂ ρ → {τ : NormalType Δ₁ ★} → Renaming (Γ₁ , τ) (Γ₂ , renₖNF ρ τ) ρ
lift (r , p) = 
  (λ { Z → Z
     ; (S x) → S (r x) }) , 
   λ { (T x) → T (p x) }

liftNormalPVar : Renaming Γ₁ Γ₂ ρ → {π : NormalPred Δ R[ κ ]} → Renaming (Γ₁ ,,, π) (Γ₂ ,,, renPredₖNF ρ π) ρ
liftNormalPVar (r , p) = 
  (λ { (P x) → P (r x) }) , 
  λ { Z → Z
    ; (S x) → S (p x) }

liftKVar : Renaming Γ₁ Γ₂ ρ → Renaming (Γ₁ ,, κ) (Γ₂ ,, κ) (liftₖ ρ)
liftKVar {ρ = ρ} (r , p)  = 
  (λ { (K {τ = τ} x) → convVar (sym (↻-weakenₖNF-renₖNF ρ τ)) (K (r x)) }) , 
  (λ { (K {π = π} x) → convPVar (sym (↻-weakenPredₖNF-renPredₖNF ρ π)) (K (p x)) })

--------------------------------------------------------------------------------
-- Renaming terms

ren : ∀ {τ} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      NormalTerm Γ₁ τ →
      NormalTerm Γ₂ (renₖNF ρ τ)
renEnt : ∀ {π : NormalPred Δ R[ κ ]} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      NormalEnt Γ₁ π →
      NormalEnt Γ₂ (renPredₖNF ρ π)
renRecord : ∀ {xs : SimpleRow NormalType Δ R[ ★ ]}
            (Ρ : Renaming Γ₁ Γ₂ ρ) → 
            Record Γ₁ xs →
            Record Γ₂ (renRowₖNF ρ xs)

--------------------------------------------------------------------------------
-- Useful lemma for commuting renaming over the lift entailment rules

↻-ren-⇓-<$> : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → 
          (F : NormalType Δ₁ (κ₁ `→ κ₂))
          (ρ₁ : NormalType Δ₁ R[ κ₁ ]) → 
          ⇓ (⇑ (renₖNF ρ F) <$> ⇑ (renₖNF ρ ρ₁)) ≡  renₖNF ρ (⇓ (⇑ F <$> ⇑ ρ₁))
↻-ren-⇓-<$> ρ F ρ₁ rewrite 
    (↻-ren-⇑ ρ ρ₁) 
  | (↻-ren-⇑ ρ F) = 
      (trans 
        (reify-≋ 
          (trans-≋ (↻-renₖ-eval ρ (⇑ F <$> ⇑ ρ₁) idEnv-≋) 
          (trans-≋ 
            (idext (sym-≋ ∘ ↻-ren-reflect ρ ∘ `) (⇑ F <$> ⇑ ρ₁)) 
            (sym-≋ (↻-renSem-eval ρ (⇑ F <$> ⇑ ρ₁) idEnv-≋))))) 
        (sym (↻-ren-reify ρ 
          {V₁ = (↓ F <$>V ↓ ρ₁)} 
          {V₂ = (↓ F <$>V ↓ ρ₁)} 
          (fundC 
            {τ₁ = ⇑ F <$> ⇑ ρ₁} 
            {τ₂ = ⇑ F <$> ⇑ ρ₁} 
            idEnv-≋ 
            (eq-<$> 
              eq-refl 
              eq-refl)))))   

--------------------------------------------------------------------------------
-- Renaming definitions

ren (r , p) (` x) = ` (r x)
ren R (`λ M) = `λ (ren (lift R) M)
ren R (M · N) = (ren R M) · (ren R N)
ren R (Λ M) = Λ (ren (liftKVar R) M)
ren {ρ = ρ} R (_·[_] {τ₂ = τ₂} M τ) = 
  conv 
    (sym (↻-renₖNF-β ρ τ₂ τ)) 
    ((ren R M) ·[ renₖNF ρ τ ])
ren {ρ = ρ} R (In F@(`λ τ) N) = 
  In 
    (renType R F) 
    (conv (↻-renₖNF-β  ρ τ (μ F)) 
      (ren R N))
ren R (In F@(ne x {()}) τ)
ren {ρ = ρ} R (Out F@(`λ τ) M) = 
  conv 
    (sym (↻-renₖNF-β ρ τ ((μ F)))) 
    (Out (renType R F) (ren R M))
ren R (Out F@(ne x {()}) τ)
ren R (# l) = # (renType R l)
ren R (l Π▹ M) = (ren R l) Π▹ (ren R M)
ren R (M Π/ l) = ren R M Π/ ren R l
ren R (l Σ▹ M) = (ren R l) Σ▹ (ren R M)
ren R (M Σ/ l) = ren R M Σ/ ren R l
ren R (`ƛ τ) = `ƛ (ren (liftNormalPVar R) τ)
ren R (τ ·⟨ e ⟩) = ren R τ ·⟨ renEnt R e ⟩
ren {ρ = ρ} R (prj m e) = prj (ren R m) (renEnt R e)
ren {ρ = ρ} R (inj m e) = inj (ren R m) (renEnt R e)
ren {ρ = ρ} R ((M ⊹ N) e) = ((ren R M) ⊹ (ren R N)) (renEnt R e)
ren {ρ = ρ} R ((M ▿ N) e) = ((ren R M) ▿ (ren R N)) (renEnt R e)
ren {ρ = ρ} R (fix M) = fix (ren R M)
ren {ρ = r} R (syn ρ φ M) = 
  conv (cong Π (↻-ren-⇓-<$> r φ ρ)) 
    (syn (renₖNF r ρ) (renₖNF r φ) 
  (conv (cong ⇓ (sym (SynT-cong (↻-ren-⇑ r ρ) (↻-ren-⇑ r φ))))
  (conv-≡t (inst (↻-ren-syn r (⇑ ρ) (⇑ φ)) ) (conv (↻-ren-⇓ r (SynT (⇑ ρ) (⇑ φ))) (ren R M)))))
ren {ρ = r} R (ana ρ φ τ M) = 
  conv 
    (cong₂ _`→_ (cong Σ (↻-ren-⇓-<$> r φ ρ)) refl) 
  (ana (renₖNF r ρ) (renₖNF r φ) (renₖNF r τ) 
    (conv 
      ((cong ⇓ (sym (AnaT-cong (↻-ren-⇑ r ρ) (↻-ren-⇑ r φ) (↻-ren-⇑ r τ)))))
    (conv (cong ⇓ (↻-ren-ana r (⇑ ρ) (⇑ φ) (⇑ τ))) 
    (conv (↻-ren-⇓ r (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) (ren R M)))))
ren R (comp M n) = comp (ren R M) (renEnt R n)
ren R ⦅ xs ⦆ = ⦅ renRecord R xs ⦆
ren {ρ = r} R (⟨ M ⟩ x) = ⟨ ren R M ⟩ ( ⊆-cong (renₖNF r) (renRowₖNF r) (renRowₖNF-isMap r) x)

renRecord {ρ = r} R ∅ = ∅
renRecord {ρ = r} R (x ⨾ xs) = ren R x ⨾ renRecord R xs

renEnt {ρ = ρ} {π} (r , p) (n-var x) = n-var (p x)
renEnt {ρ = φ} {π} R (n-≲ {xs = xs} {ys} i) rewrite 
  renRowₖNF-isMap φ xs | renRowₖNF-isMap φ ys = n-≲ (⊆-map (renₖNF φ) i)
renEnt {ρ = φ} {π} R (n-· {xs = xs} {ys} {zs} i₁ i₂ i₃) rewrite 
    renRowₖNF-isMap φ xs 
  | renRowₖNF-isMap φ ys
  | renRowₖNF-isMap φ zs = n-· (⊆-map (renₖNF φ) i₁) (⊆-map (renₖNF φ) i₂) (⊆-map-or (renₖNF φ) i₃)
renEnt R n-refl = n-refl
renEnt R (n-trans e₁ e₂) = n-trans (renEnt R e₁) (renEnt R e₂)
renEnt R (n-·≲L e) = n-·≲L (renEnt R e)
renEnt R (n-·≲R e) = n-·≲R (renEnt R e)
renEnt R n-ε-R = n-ε-R
renEnt R n-ε-L = n-ε-L
renEnt {Γ₂ = Γ₂} {ρ = ρ} R (n-≲lift {ρ₁ = ρ₁} {ρ₂} {F} e eq-ρ₁ eq-ρ₂) 
  rewrite 
    eq-ρ₁ 
  | eq-ρ₂
  | stability-<$> F ρ₁ 
  | stability-<$> F ρ₂ 
  = n-≲lift 
    {F = renₖNF ρ F} 
    (renEnt R e) 
    (trans (sym (↻-ren-⇓-<$> ρ F ρ₁)) (sym (stability-<$> (renₖNF ρ F) (renₖNF ρ ρ₁)))) 
    (trans (sym (↻-ren-⇓-<$> ρ F ρ₂)) (sym (stability-<$> (renₖNF ρ F) (renₖNF ρ ρ₂))))
renEnt {ρ = ρ} R (n-·lift {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} e eq-ρ₁ eq-ρ₂ eq-ρ₃)
  rewrite 
    eq-ρ₁ 
  | eq-ρ₂
  | eq-ρ₃
  | stability-<$> F ρ₁ 
  | stability-<$> F ρ₂ 
  | stability-<$> F ρ₃
  = n-·lift 
    {F = renₖNF ρ F} 
    (renEnt R e) 
    (trans (sym (↻-ren-⇓-<$> ρ F ρ₁)) (sym (stability-<$> (renₖNF ρ F) (renₖNF ρ ρ₁)))) 
    (trans (sym (↻-ren-⇓-<$> ρ F ρ₂)) (sym (stability-<$> (renₖNF ρ F) (renₖNF ρ ρ₂))))
    (trans (sym (↻-ren-⇓-<$> ρ F ρ₃)) (sym (stability-<$> (renₖNF ρ F) (renₖNF ρ ρ₃))))
  

--------------------------------------------------------------------------------
-- Weakening is a special case of renaming (but we must convert types)

weakenTermByType : NormalTerm Γ τ₁ → NormalTerm (Γ , τ₂) τ₁
weakenTermByType {τ₁ = τ₁} M = conv (renₖNF-id τ₁) (ren ((convVar (sym (renₖNF-id _))) ∘ S , convPVar (sym (renₖNF-id-pred _)) ∘ T) M)

weakenTermByKind : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → NormalTerm (Γ ,, κ) (weakenₖNF τ)
weakenTermByKind = ren (K , K)

weakenTermByPred : ∀ {τ : NormalType Δ ★} {π : NormalPred Δ R[ κ ]} → NormalTerm Γ τ → NormalTerm (Γ ,,, π) τ
weakenTermByPred {Γ = Γ} {τ = τ} {π} M = conv (renₖNF-id τ) (ren ((convVar (sym (renₖNF-id _))) ∘ P , convPVar (sym (renₖNF-id-pred _)) ∘ S) M)

--------------------------------------------------------------------------------
-- Weakening of an entailment

weakenEntByType : ∀ {π : NormalPred Δ R[ κ ]} → NormalEnt Γ π → NormalEnt (Γ , τ) π 
weakenEntByType {π = π} M = convEnt (renₖNF-id-pred π) (renEnt (convVar (sym (renₖNF-id _)) ∘ S , convPVar (sym (renₖNF-id-pred _)) ∘ T) M)


weakenEntByKind : ∀ {π : NormalPred Δ R[ κ₁ ]} → NormalEnt Γ π → NormalEnt (Γ ,, κ₂) (weakenPredₖNF π)
weakenEntByKind = renEnt (K , K)

weakenEntByPred : ∀ {π₁ : NormalPred Δ R[ κ₁ ]} {π₂ : NormalPred Δ R[ κ₂ ]} → NormalEnt Γ π₁ → NormalEnt (Γ ,,, π₂) π₁
weakenEntByPred M = convEnt (renₖNF-id-pred _) (renEnt (convVar (sym (renₖNF-id _)) ∘ P , convPVar (sym (renₖNF-id-pred _)) ∘ S) M)
