{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
import Rome.Operational.Types.Normal.Renaming as NR
import Rome.Operational.Types.Normal.Properties.Renaming as NRP

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

-- open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness.Relation
open import Rome.Operational.Types.Theorems.Completeness.Congruence
open import Rome.Operational.Types.Theorems.Completeness.Commutativity

open import Rome.Operational.Types.Equivalence

-------------------------------------------------------------------------------
-- Fundamental theorem

fund : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → 
       Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fund-pred : ∀ {π₁ π₂ : Pred Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂

fund-pred e (τ₁ eq-≲ τ₂) = cong₂ _≲_ (reify-≋ (fund e τ₁)) (reify-≋ (fund e τ₂))
fund-pred e (τ₁ eq-· τ₂ ~ τ₃) rewrite
    reify-≋ (fund e τ₁) 
  | reify-≋ (fund e τ₂) 
  | reify-≋ (fund e τ₃) = refl

fund {τ₁ = τ} e eq-refl = idext e τ
fund e (eq-sym eq) = sym-≋ (fund (sym-≋ ∘ e) eq)
fund e (eq-trans eq₁ eq₂) = trans-≋ (fund (refl-≋ₗ ∘ e) eq₁) (fund e eq₂)
fund e (eq-→ {τ₁ = τ₁} {υ₁ = υ₁} eq-τ eq-υ) = cong₂ _`→_ (fund e eq-τ) (fund e eq-υ)
fund {κ = κ} e (eq-· eq₁ eq₂) = cong-App (fund e eq₁) (fund e eq₂)
fund e (eq-∀ eq) = cong (`∀ _) (fund (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) eq)
fund {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) with eval τ η₁ | eval υ η₂ | fund e eq
... | y | y₁ | Unif-F , Unif-G , Ext = cong μ (cong `λ (Ext S refl))
fund e (eq-⌊⌋ eq) rewrite fund e eq = refl
fund e (eq-λ {τ = τ} {υ = υ} eq) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ τ (extend-≋ (λ x → ren-≋ ρ₁ (e x)) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (e x)) }) τ))  , 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ υ (extend-≋ (λ x → ren-≋ ρ₁ (sym-≋ (e x))) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (sym-≋ (e x))) }) υ)), 
    λ ρ q → fund (extend-≋ (λ x → ren-≋ ρ (e x)) q) eq
fund {η₁ = η₁} {η₂ = η₂} e (eq-η {f = f}) = 
  fst (idext e f) , 
  fst (snd (idext {η₁ = η₁} {η₂ = η₂} e (`λ (weaken f · (` Z))))) , 
  λ ρ {V₁} {V₂} v → 
  sym-≋ 
    (trans-≋ 
        (third (↻-ren-eval S f 
                    {η₂ = (extende (λ {κ} v' → renSem ρ (η₂ v')) V₂)} 
                    (extend-≋ (λ x → ren-≋ ρ (refl-≋ᵣ (e x))) (refl-≋ᵣ v))) 
                    id 
                    (sym-≋ v)) 
        ((↻-eval-Kripke f ρ (refl-≋ₗ v) (sym-≋ ∘ e))))

fund {η₁ = η₁} {η₂ = η₂} e (eq-β {τ₁ = τ₁} {τ₂}) = 
    trans-≋ 
        (idext 
            {η₂ = extende η₁ (eval τ₂ η₁)} 
            (λ { Z → idext {η₂ = η₁}  (refl-≋ₗ ∘ e) τ₂
           ; (S x) → renSem-id-≋ (refl-≋ₗ  (e x)) }) τ₁) 
        (sym-≋ 
            (trans-≋ 
                ((↻-subst-eval τ₁ (sym-≋ ∘ e) (extend ` τ₂))) 
                (idext (λ { Z → idext (refl-≋ₗ ∘ e) τ₂
                          ; (S x) → (refl-≋ₗ ∘ e) x }) τ₁)))
fund e (eq-▹ eq-l eq-τ) rewrite fund e eq-l = cong-▹ refl (fund e eq-τ)
fund e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fund-pred e eq-π) (fund e eq-τ)
fund {κ = R[ κ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Π {l = l} {τ}) = (idext e l) , cong-π {τ₁ = eval τ η₁} {τ₂ = eval τ η₂} (idext e τ)
fund {κ = R[ κ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Σ {l = l} {τ}) = (idext e l) , cong-σ {τ₁ = eval τ η₁} {τ₂ = eval τ η₂} (idext e τ)
fund {η₁ = η₁} {η₂ = η₂} e (eq-Πλ {l = l} {τ = τ}) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → 
      trans-≋ 
        (↻-ren-ξ Π-rec ρ₂ 
            (right (NR.ren ρ₁ (eval l η₁) , eval τ (extende (λ {κ} v' → renSem (λ x → ρ₁ x) (η₁ v')) V₁))) 
            (right (NR.ren ρ₁ (eval l η₁) , eval τ (extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₂))) 
            (refl , (idext (extend-≋ (refl-≋ₗ ∘ ren-≋ ρ₁ ∘  e) q) τ))) 
        (cong-π 
            {τ₁ = (right (NR.ren ρ₂ (NR.ren ρ₁ (eval l η₁)) ,
                   renSem ρ₂ (eval τ (extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₂))))} 
            {τ₂ = (right (NR.ren (λ x → ρ₂ (ρ₁ x)) (eval l η₁) ,
                   eval τ (extende (λ {κ} v' → renSem (λ x → ρ₂ (ρ₁ x)) (η₁ v')) (renSem ρ₂ V₂))))} 
            ((sym (NRP.ren-comp ρ₁ ρ₂ (eval l η₁))) , 
            (trans-≋ 
                (↻-renSem-eval ρ₂ τ 
                    {(extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₂)} 
                    {(extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₂)} 
                    (extend-≋ (refl-≋ₗ ∘ ren-≋ ρ₁ ∘ e) (refl-≋ᵣ q))) 
                (idext (λ { Z      → ren-≋ ρ₂ (refl-≋ᵣ q)
                          ; (S x)  → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) τ)))))  ,
    (λ ρ₁ ρ₂ V₁ V₂ q → 
        trans-≋ 
          (↻-ren-ξ Π-rec ρ₂ 
            (right
                (eval (ren S l) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁) ,
                eval τ (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁))) 
            (right
                (eval (ren S l) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁) ,
                eval τ (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁))) 
            (refl , (idext (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q)) τ))) 
          (cong-π
             {τ₁ = right (NR.ren ρ₂
                (eval (ren S l) (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁))
                , renSem ρ₂ (eval τ (extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁)))}
             {τ₂ = eval (weaken l)
              (extende (λ {κ} v' → renSem (λ x → ρ₂ (ρ₁ x)) (η₂ v'))
               (renSem ρ₂ V₂)) ▹V eval τ (extende (λ {κ} v' → renSem (λ x → ρ₂ (ρ₁ x)) (η₂ v')) 
               (renSem ρ₂ V₂))}
             ((trans 
                (↻-renSem-eval ρ₂ (weaken l) {extende (renSem ρ₁ ∘ η₂) V₁} {extende (renSem ρ₁ ∘ η₂) V₁} 
                    (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q))) 
                (idext (λ { Z → ren-≋ ρ₂ q
                          ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e x))) }) (weaken l))) , 
             trans-≋ 
                (↻-renSem-eval ρ₂ τ 
                    {(extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁)} 
                    {(extende (λ {κ} v' → renSem ρ₁ (η₂ v')) V₁)} (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e) (refl-≋ₗ q))) 
                (idext (λ { Z → ren-≋ ρ₂ q
                          ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e x))) }) τ)))) , 
    λ ρ {V₁ = V₁} {V₂} v → cong-π
      {τ₁ = right (NR.ren ρ (eval l η₁) ,
                  eval τ (extende (λ {κ} v' → renSem (λ x → ρ x) (η₁ v')) V₁))}
      {τ₂ = right (eval (ren S l) (extende (λ {κ} v' → renSem ρ (η₂ v')) V₂) ,
                  eval τ (extende (λ {κ} v' → renSem ρ (η₂ v')) V₂))}
      ((trans 
        (↻-renSem-eval ρ l {η₁} {η₂} e) 
        (sym (trans 
            (↻-ren-eval S l {extende (renSem ρ ∘ η₂) V₂} {extende (renSem ρ ∘ η₂) V₂} (extend-≋ (refl-≋ᵣ ∘ ren-≋ ρ ∘ e) (refl-≋ᵣ v)))
            (idext (ren-≋ ρ ∘ refl-≋ᵣ ∘ e) l)))) , 
      idext (extend-≋ (ren-≋ ρ ∘ e) v) τ)
fund {η₁ = η₁} {η₂} e (eq-▹$ {l = l} {τ} {F}) = 
    (idext e l) , 
    cong-App 
      {V₁ = eval F η₁} 
      {V₂ = eval F η₂} 
      (idext e F) 
      {W₁ = eval τ η₁} 
      {W₂ = eval τ η₂} 
      (idext e τ)
fund {κ = κ} {η₁ = η₁} {η₂} e (eq-assoc-Π {κ₁ = κ₁} {κ₂ = κ₂} {ρ = ρ} {τ}) with eval ρ η₁ | eval ρ η₂ | idext e ρ
... | right (l , F) | right (.l , G) | refl , q rewrite 
      NRP.ren-id l 
    | renSem-id {κ = κ₁ `→ κ₂} F 
    | renSem-id {κ = κ₁ `→ κ₂} G
    | renSem-id (eval τ η₂) = cong-π 
        {τ₁ = right (l , (F ·V eval τ η₁))}
        {τ₂ = right (l , (G ·V eval τ η₂))} 
        (refl , (cong-App q (idext e τ)))
... | left x | left .x | refl rewrite NRP.ren-id-ne x = 
    cong-π 
        (cong (_<$> x) 
            (cong `λ 
                (cong (reify ∘ reflect ∘ (` Z ·_)) 
                    (reify-≋ (ren-≋ S (idext e τ))))))
fund {κ = κ} {η₁ = η₁} {η₂} e (eq-assoc-Σ {κ₁ = κ₁} {κ₂ = κ₂} {ρ = ρ} {τ}) with eval ρ η₁ | eval ρ η₂ | idext e ρ
... | right (l , F) | right (.l , G) | refl , q rewrite 
      NRP.ren-id l 
    | renSem-id {κ = κ₁ `→ κ₂} F 
    | renSem-id {κ = κ₁ `→ κ₂} G
    | renSem-id (eval τ η₂) = cong-σ 
        {τ₁ = right (l , (F ·V eval τ η₁))}
        {τ₂ = right (l , (G ·V eval τ η₂))} 
        (refl , (cong-App q (idext e τ)))
... | left x | left .x | refl rewrite NRP.ren-id-ne x =     
    cong-σ 
        (cong (_<$> x) 
            (cong `λ 
                (cong (reify ∘ reflect ∘ (` Z ·_)) 
                    (reify-≋ (ren-≋ S (idext e τ))))))         
fund {κ = κ} {η₁ = η₁} {η₂} e (eq-app-lift-Π {τ = τ}) with eval τ η₁ | eval τ η₂ | idext e τ 
... | left _ | left _ | refl = refl
... | right (l , τ) | right (_ , υ) | refl , q = refl , (cong-π q)
fund {κ = κ} {η₁ = η₁} {η₂} e (eq-<$> t u) = cong-<$> (fund e t) (fund e u)

idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflect-≋ refl

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fund idEnv-≋ eq)  
 
 
 