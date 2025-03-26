{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Theorems.Completeness.Relation public 
open import Rome.Operational.Types.Theorems.Completeness.Congruence public 
open import Rome.Operational.Types.Theorems.Completeness.Commutativity public

open import Rome.Operational.Types.Equivalence

-------------------------------------------------------------------------------
-- Fundamental theorem

fundC : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → 
       Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fundC-pred : ∀ {π₁ π₂ : Pred Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂

fundC-pred e (τ₁ eq-≲ τ₂) = cong₂ _≲_ (reify-≋ (fundC e τ₁)) (reify-≋ (fundC e τ₂))
fundC-pred e (τ₁ eq-· τ₂ ~ τ₃) rewrite
    reify-≋ (fundC e τ₁) 
  | reify-≋ (fundC e τ₂) 
  | reify-≋ (fundC e τ₃) = refl

fundC {τ₁ = τ} e eq-refl = idext e τ
fundC e (eq-sym eq) = sym-≋ (fundC (sym-≋ ∘ e) eq)
fundC e (eq-trans eq₁ eq₂) = trans-≋ (fundC (refl-≋ₗ ∘ e) eq₁) (fundC e eq₂)
fundC e (eq-→ {τ₁ = τ₁} {υ₁ = υ₁} eq-τ eq-υ) = cong₂ _`→_ (fundC e eq-τ) (fundC e eq-υ)
fundC {κ = κ} e (eq-· eq₁ eq₂) = cong-App (fundC e eq₁) (fundC e eq₂)
fundC e (eq-∀ eq) = cong `∀ (fundC (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) eq)
fundC {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) with eval τ η₁ | eval υ η₂ | fundC e eq
... | y | y₁ | Unif-F , Unif-G , Ext = cong μ (cong `λ (Ext S refl))
fundC e (eq-⌊⌋ eq) rewrite fundC e eq = refl
fundC e (eq-λ {τ = τ} {υ = υ} eq) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ τ (extend-≋ (λ x → ren-≋ ρ₁ (e x)) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (e x)) }) τ))  , 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ υ (extend-≋ (λ x → ren-≋ ρ₁ (sym-≋ (e x))) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (sym-≋ (e x))) }) υ)), 
    λ ρ q → fundC (extend-≋ (λ x → ren-≋ ρ (e x)) q) eq
fundC {η₁ = η₁} {η₂ = η₂} e (eq-η {f = f}) = 
  fst (idext e f) , 
  fst (snd (idext {η₁ = η₁} {η₂ = η₂} e (`λ (weakenₖ f · (` Z))))) , 
  λ ρ {V₁} {V₂} v → 
  sym-≋ 
    (trans-≋ 
        (third (↻-renₖ-eval S f 
                    {η₂ = (extende (λ {κ} v' → renSem ρ (η₂ v')) V₂)} 
                    (extend-≋ (λ x → ren-≋ ρ (refl-≋ᵣ (e x))) (refl-≋ᵣ v))) 
                    id 
                    (sym-≋ v)) 
        ((↻-eval-Kripke f ρ (refl-≋ₗ v) (sym-≋ ∘ e))))

fundC {η₁ = η₁} {η₂ = η₂} e (eq-β {τ₁ = τ₁} {τ₂}) = 
    trans-≋ 
        (idext 
            {η₂ = extende η₁ (eval τ₂ η₁)} 
            (λ { Z → idext {η₂ = η₁}  (refl-≋ₗ ∘ e) τ₂
           ; (S x) → renSem-id-≋ (refl-≋ₗ  (e x)) }) τ₁) 
        (sym-≋ 
            (trans-≋ 
                ((↻-subₖ-eval τ₁ (sym-≋ ∘ e) (extendₖ ` τ₂))) 
                (idext (λ { Z → idext (refl-≋ₗ ∘ e) τ₂
                          ; (S x) → (refl-≋ₗ ∘ e) x }) τ₁)))
fundC e (eq-▹ eq-l eq-τ) rewrite fundC e eq-l = cong-▹ refl (fundC e eq-τ)
fundC e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fundC-pred e eq-π) (fundC e eq-τ)
fundC {κ = R[ κ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Π▹ {l = l} {τ}) = (idext e l) , cong-Π {τ₁ = eval τ η₁} {τ₂ = eval τ η₂} (idext e τ)
fundC {κ = R[ κ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Σ▹ {l = l} {τ}) = (idext e l) , cong-Σ {τ₁ = eval τ η₁} {τ₂ = eval τ η₂} (idext e τ)
-- clean this shit up
fundC {η₁ = η₁} {η₂ = η₂} e (eq-Πλ {κ₁ = κ₁} {κ₂ = κ₂} {l = l} {τ = τ}) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
        (↻-renSem-Π ρ₂ 
            (renₖNF ρ₁ (eval l η₁) ▹V eval τ (extende _ (renSem id V₁))) 
            (renₖNF ρ₁ (eval l η₁) ▹V eval τ (extende _ (renSem id V₂))) 
            (refl , (idext (extend-≋ (ren-≋ ρ₁ ∘ e) (ren-≋ id q)) τ))) 
        (cong-Π 
            ((sym-≋ {κ = L} (renₖNF-comp {κ = L} ρ₁ ρ₂ (eval l η₁))) , 
            (trans-≋ 
                (↻-renSem-eval ρ₂ τ (extend-≋ (refl-≋ᵣ ∘ ren-≋ ρ₁ ∘ e) (ren-≋ id (refl-≋ᵣ q)) )) 
                (idext (λ { Z     → renSem-comp-≋ ρ₂ id (renSem-id-≋ (refl-≋ᵣ q))
                          ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (e x)) }) τ))))) , 
    (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
        (↻-renSem-Π ρ₂ 
            (eval (weakenₖ l ▹ τ) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁)) 
            ((eval (weakenₖ l ▹ τ) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁))) 
            (refl , idext (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q)) τ)) 
        (cong-Π 
            ((trans 
                (↻-renSem-eval ρ₂ (weakenₖ l) (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q))) 
                (idext (λ { Z     →  ren-≋ ρ₂ q
                          ; (S x) → (sym-≋ ∘ (renSem-comp-≋ ρ₁ ρ₂) ∘ refl-≋ᵣ ∘ e) x }) (weakenₖ l))) , 
            trans-≋ 
                (↻-renSem-eval ρ₂ τ ((extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q)))) 
                (idext (λ { Z     → ren-≋ ρ₂ q
                          ; (S x) → (sym-≋ ∘ (renSem-comp-≋ ρ₁ ρ₂) ∘ refl-≋ᵣ ∘ e) x }) τ)))) , 
    λ ρ v → 
    cong-Π 
        ((trans 
            (↻-renSem-eval ρ l e) 
            (sym (trans 
                (↻-renₖ-eval S l (extend-≋ (refl-≋ᵣ ∘ ren-≋ ρ ∘ e) (refl-≋ᵣ v)))
                (idext (ren-≋ ρ ∘ refl-≋ᵣ ∘ e) l)))) ,
        idext (extend-≋ (ren-≋ ρ ∘ e) (renSem-id-≋ v)) τ)
fundC {η₁ = η₁} {η₂ = η₂} e (eq-Σλ {l = l} {τ = τ}) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
        (↻-renSem-Σ ρ₂ 
            (renₖNF ρ₁ (eval l η₁) ▹V eval τ (extende _ (renSem id V₁))) 
            (renₖNF ρ₁ (eval l η₁) ▹V eval τ (extende _ (renSem id V₂))) 
            (refl , (idext (extend-≋ (ren-≋ ρ₁ ∘ e) (ren-≋ id q)) τ))) 
        (cong-Σ 
            ((sym-≋ {κ = L} (renₖNF-comp {κ = L} ρ₁ ρ₂ (eval l η₁))) , 
            (trans-≋ 
                (↻-renSem-eval ρ₂ τ (extend-≋ (refl-≋ᵣ ∘ ren-≋ ρ₁ ∘ e) (ren-≋ id (refl-≋ᵣ q)) )) 
                (idext (λ { Z     → renSem-comp-≋ ρ₂ id (renSem-id-≋ (refl-≋ᵣ q))
                          ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (e x)) }) τ))))) , 
    (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
        (↻-renSem-Σ ρ₂ 
            (eval (weakenₖ l ▹ τ) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁)) 
            ((eval (weakenₖ l ▹ τ) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁))) 
            (refl , idext (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q)) τ)) 
        (cong-Σ 
            ((trans 
                (↻-renSem-eval ρ₂ (weakenₖ l) (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q))) 
                (idext (λ { Z     →  ren-≋ ρ₂ q
                          ; (S x) → (sym-≋ ∘ (renSem-comp-≋ ρ₁ ρ₂) ∘ refl-≋ᵣ ∘ e) x }) (weakenₖ l))) , 
            trans-≋ 
                (↻-renSem-eval ρ₂ τ ((extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q)))) 
                (idext (λ { Z     → ren-≋ ρ₂ q
                          ; (S x) → (sym-≋ ∘ (renSem-comp-≋ ρ₁ ρ₂) ∘ refl-≋ᵣ ∘ e) x }) τ)))) , 
    λ ρ v → 
    cong-Σ 
        ((trans 
            (↻-renSem-eval ρ l e) 
            (sym (trans 
                (↻-renₖ-eval S l (extend-≋ (refl-≋ᵣ ∘ ren-≋ ρ ∘ e) (refl-≋ᵣ v)))
                (idext (ren-≋ ρ ∘ refl-≋ᵣ ∘ e) l)))) ,
        idext (extend-≋ (ren-≋ ρ ∘ e) (renSem-id-≋ v)) τ)
fundC {η₁ = η₁} {η₂} e (eq-▹$ {l = l} {τ} {F}) = 
    (idext e l) , 
    cong-App 
      {V₁ = eval F η₁} 
      {V₂ = eval F η₂} 
      (idext e F) 
      {W₁ = eval τ η₁} 
      {W₂ = eval τ η₂} 
      (idext e τ)
fundC {κ = κ} {η₁ = η₁} {η₂} e (eq-Π-assoc {κ₁ = κ₁} {κ₂ = κ₂} {ρ = ρ} {τ}) with eval ρ η₁ | eval ρ η₂ | idext e ρ
... | just (right (l , F)) | just (right (.l , G)) | refl , q rewrite 
      renₖNF-id l 
    | renSem-id {κ = κ₁ `→ κ₂} F 
    | renSem-id {κ = κ₁ `→ κ₂} G = cong-Π 
        (refl , third q id (ren-≋ id (idext e τ)))
... | just (left x) | just (left .x) | refl rewrite renₖNE-id x = 
    cong-Π 
        (cong (_<$> x) 
            (cong `λ 
                (cong (reify ∘ reflect ∘ (` Z ·_)) 
                    (reify-≋ (ren-≋ S (idext e τ))))))
... | nothing | nothing | _ = cong-Π tt
fundC {κ = κ} {η₁ = η₁} {η₂} e (eq-Σ-assoc {κ₁ = κ₁} {κ₂ = κ₂} {ρ = ρ} {τ}) with eval ρ η₁ | eval ρ η₂ | idext e ρ
... | just (right (l , F)) | just (right (.l , G)) | refl , q rewrite 
      renₖNF-id l 
    | renSem-id {κ = κ₁ `→ κ₂} F 
    | renSem-id {κ = κ₁ `→ κ₂} G = cong-Σ 
        (refl , third q id (ren-≋ id (idext e τ)))
... | just (left x) | just (left .x) | refl rewrite renₖNE-id x = 
    cong-Σ 
        (cong (_<$> x) 
            (cong `λ 
                (cong (reify ∘ reflect ∘ (` Z ·_)) 
                    (reify-≋ (ren-≋ S (idext e τ))))))
... | nothing | nothing | _ = cong-Σ tt    
fundC {κ = κ} {η₁ = η₁} {η₂} e (eq-Π {τ = τ}) with eval τ η₁ | eval τ η₂ | idext e τ 
... | just (left _) | just (left _) | refl = refl
... | just (right (l , τ)) | just (right (_ , υ)) | refl , q = refl , (cong-Π q)
... | nothing | nothing | _ = tt
fundC {κ = κ} {η₁ = η₁} {η₂} e (eq-Σ {τ = τ}) with eval τ η₁ | eval τ η₂ | idext e τ 
... | just (left _) | just (left _) | refl = refl
... | just (right (l , τ)) | just (right (_ , υ)) | refl , q = refl , (cong-Σ q)
... | nothing | nothing | _ = tt
fundC {κ = κ} {η₁ = η₁} {η₂} e (eq-<$> t u) = cong-<$> (fundC e t) (fundC e u)
fundC {κ = κ} {η₁ = η₁} {η₂} e eq-<$>ε = tt 

idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflect-≋ refl

-------------------------------------------------------------------------------
-- Completeness

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fundC idEnv-≋ eq)  
 
 
 -------------------------------------------------------------------------------
-- Helper to substitute under an eval
 
evalCRSubst : ∀ {η₁ η₂ : Env Δ₁ Δ₂}
    → Env-≋ η₁ η₂
    → {τ₁ τ₂ : Type Δ₁ κ}
    → τ₁ ≡ τ₂
    → (eval τ₁ η₁) ≋ (eval τ₂ η₂)
evalCRSubst p {τ₁ = τ} refl = idext p τ
