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
fundC e (eq-→ eq-τ eq-υ) = cong₂ _`→_ (fundC e eq-τ) (fundC e eq-υ)
fundC {κ = κ} e (eq-· eq₁ eq₂) = cong-App (fundC e eq₁) (fundC e eq₂)
fundC e (eq-∀ eq) = cong `∀ (fundC (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) eq)
fundC {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) 
  with eval τ η₁ | eval υ η₂ | fundC e eq
... |  y         | y₁        | Unif-F , Unif-G , Ext = 
  cong μ (cong `λ (Ext S refl))
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
fundC e (eq-▹ eq-l eq-τ) = cong-⁅⁆ (fundC e eq-τ)
fundC e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fundC-pred e eq-π) (fundC e eq-τ)
fundC e (eq-Π▹ {τ = τ}) = refl , (λ { refl fzero → cong-Π (idext e τ) })
fundC e (eq-Σ▹ {τ = τ}) = refl , (λ { refl fzero → cong-Σ (idext e τ) })
fundC e (eq-Πλ {l = l} {τ}) =  
  fst (idext e (Π · (l ▹ `λ τ))) , 
  fst (snd (idext e (`λ (Π · (weakenₖ l ▹ τ))))) , 
  λ ρ v → cong-Π (refl , (λ { refl fzero → idext (extend-≋ (ren-≋ ρ ∘ e) (renSem-id-≋ v)) τ }))
fundC e (eq-Σλ {l = l} {τ = τ}) =
  fst (idext e (Σ · (l ▹ `λ τ))) , 
  fst (snd (idext e (`λ (Σ · (weakenₖ l ▹ τ))))) , 
  λ ρ v → cong-Σ (refl , (λ { refl fzero → idext (extend-≋ (ren-≋ ρ ∘ e) (renSem-id-≋ v)) τ }))
fundC e (eq-▹$ {τ = τ} {F}) = 
  refl , (λ { refl fzero → cong-App (idext e F) (idext e τ) })
fundC e (eq-Π-assoc {ρ = ρ} {τ}) = 
  cong-Π 
    (cong-<$> 
      (cong-apply (idext e τ))
      (ren-≋ id (idext e ρ))) 
fundC e (eq-Σ-assoc {ρ = ρ} {τ}) =
  cong-Σ 
    (cong-<$> 
      (cong-apply (idext e τ))
      (ren-≋ id (idext e ρ))) 
fundC e (eq-Π {τ = τ}) = cong-<$> (idext e Π) (idext e τ) 
fundC e (eq-Σ {τ = τ}) = cong-<$> (idext e Σ) (idext e τ) 
fundC e (eq-<$> t u) = cong-<$> (fundC e t) (fundC e u)
fundC e (eq-map {ρ = []}) = refl , (λ { refl () })
fundC {η₁ = η₁} e (eq-map {F = F} {ρ = x ∷ ρ}) 
  with evalRow ρ η₁ | fundC e (eq-map {F = F} {ρ})
... |  n , P        | refl , eq = 
  refl , (λ { refl fzero → cong-App  (idext e F) (idext e x)
            ; refl (fsuc i) → eq refl i })
fundC e (eq-row ρ₁ ρ₂ eq-[]) = refl , (λ { _ () })
fundC {η₁ = η₁} e (eq-row ρ₁ ρ₂ (eq-cons {xs = xs} {ys} x eq-ρ)) 
  with evalRow xs η₁ | fundC e (eq-row xs ys eq-ρ)
... |  (n , P)       | refl , eq = 
  refl , λ { refl fzero → fundC e x
           ; refl (fsuc i) → eq refl i }

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
