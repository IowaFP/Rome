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

open import Rome.Operational.Types.Equivalence.Relation

--------------------------------------------------------------------------------
-- Equivalence of membership in syntactic and semantic spaces

∈L→∈Row : ∀ {l : Label} {η₁ : Env Δ₁ Δ₂} {ys : SimpleRow Type Δ₁ R[ κ ]} → l ∈L ys → l ∈Row (evalRow ys η₁ .snd)
∈L→∈Row {ys = ys} Here = fzero , refl
∈L→∈Row {ys = (l' , τ) ∷ ys} (There ev) = (fsuc (∈L→∈Row ev .fst)) , (∈L→∈Row ev .snd)

∈Row→∈L : ∀ {l : Label} {η₁ : Env Δ₁ Δ₂} {ys : SimpleRow Type Δ₁ R[ κ ]} → l ∈Row (evalRow ys η₁ .snd) → l ∈L ys
∈Row→∈L {ys = (l , τ) ∷ ys} (fzero , refl) = Here
∈Row→∈L {ys = (l , τ) ∷ ys} (fsuc i , refl) = There (∈Row→∈L (i , refl))

--------------------------------------------------------------------------------
-- Commutativity of syntactic and semantic complement

↻-syn/sem-compl : ∀ {η₁ η₂ : Env Δ₁ Δ₂} (xs ys : SimpleRow Type Δ₁ R[ κ ]) → 
                  Env-≋ η₁ η₂ → 
                  (evalRow xs η₁ ─v evalRow ys η₁) ≋R (evalRow (xs ─s ys) η₂)
↻-syn/sem-compl [] ys e = refl , (λ ())
↻-syn/sem-compl {η₁ = η₁} {η₂} ((l , τ) ∷ xs) ys e with l ∈Row? (evalRow ys η₁ .snd) | l ∈L? ys
... | yes p | yes q = ↻-syn/sem-compl xs ys e
... | yes p | no q = ⊥-elim (q (∈Row→∈L p)) 
... | no q | yes p = ⊥-elim (q (∈L→∈Row p)) 
... | no p | no q  with compl (evalRow xs η₁ .snd) (evalRow ys η₁ .snd) | evalRow (xs ─s ys) η₂ | ↻-syn/sem-compl xs ys e
↻-syn/sem-compl ((l , τ) ∷ xs) ys e | no p | no q | x | y | (refl , ih') = refl , λ { fzero → refl , idext e τ ; (fsuc i) → ih' i }

--------------------------------------------------------------------------------
-- Commutativity of syntactic/semantic complement as a strict equality

↻-─s-─v : ∀ {n m} 
          (P : Fin n → Label × SemType Δ κ) → 
          (Q : Fin m → Label × SemType Δ κ) → 
          (⇑Row (reifyRow' n P) ─s ⇑Row (reifyRow' m Q)) ≡
          ⇑Row (reifyRow (compl P Q))
↻-─s-─v {n = zero} P Q = refl
↻-─s-─v {n = suc n} {m} P Q with P fzero .fst ∈L? ⇑Row (reifyRow' m Q) | P fzero .fst ∈Row? Q 
... | yes p | yes q = ↻-─s-─v (P ∘ fsuc) Q
... | yes p | no  q = ⊥-elim (q (In p))
  where
    In : ∀ {l} {m} {Q : Fin m → Label × SemType Δ κ} → l ∈L ⇑Row (reifyRow' m Q) → l ∈Row Q
    In {l} {m = suc m} Here = fzero , refl
    In {m = suc m} (There ev) = fsuc (In ev .fst) ,  In ev .snd
... | no  p | yes q = ⊥-elim (p (In q))
  where
    In : ∀ {l} {m} {Q : Fin m → Label × SemType Δ κ} → l ∈Row Q → l ∈L ⇑Row (reifyRow' m Q)
    In {l} {m = suc m} (fzero , refl) = Here
    In {l} {m = suc m} (fsuc i , eq) = There (In (i , eq))
    
... | no  p | no  q = cong₂ _∷_ refl (↻-─s-─v (P ∘ fsuc) Q) 

-------------------------------------------------------------------------------
-- Fundamental theorem

fundC : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → 
       Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fundC-pred : ∀ {π₁ π₂ : Pred Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂
fundC-Row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → ρ₁ ≡r ρ₂ → evalRow ρ₁ η₁ ≋R evalRow ρ₂ η₂


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
fundC {η₁ = η₁} {η₂} e (eq-▹ {l₁ = l₁} {l₂} eq-l eq-τ) with eval l₁ η₁ | eval l₂ η₂ | fundC e eq-l 
... | ne x | ne x | refl = refl , fundC e eq-τ
... | lab l | lab l | refl = refl , (λ { fzero → refl , fundC e eq-τ } )
fundC e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fundC-pred e eq-π) (fundC e eq-τ)
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
fundC e (eq-Π {ρ = ρ} {nl}) = cong-<$> (idext e (Π {notLabel = nl})) (idext e ρ)
fundC e (eq-Σ {ρ = ρ} {nl}) = cong-<$> (idext e (Σ {notLabel = nl})) (idext e ρ) 
fundC e (eq-<$> t u) = cong-<$> (fundC e t) (fundC e u)
fundC {Δ₁ = Δ₁} {κ = κ} {η₁ = η₁} {η₂} e (eq-map {κ₁ = κ₁} {κ₂} {F = F} {ρ = ρ} {oρ}) = go ρ
  where
    go : (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) → (evalRow ρ η₁ .fst ,
       (λ x₁ → overᵣ (eval F η₁ id) (evalRow ρ η₁ .snd x₁)))
      ≋R
      (evalRow (map (overᵣ (_·_ F)) ρ) η₂ .fst ,
       evalRow (map (overᵣ (_·_ F)) ρ) η₂ .snd)
    go [] = refl , (λ ())
    go (x ∷ ρ) with evalRow ρ η₁ | go ρ
    ... | n , P | refl , eq = refl , (λ { fzero → refl , (cong-App (idext e F) (idext e (x . snd))) ; (fsuc i) → eq i })
fundC e (eq-row eq) = fundC-Row e eq
fundC e (eq-lab refl) = refl
fundC {η₁ = η₁} {η₂} e (eq-▹$ {l = l} {τ = τ} {F}) with eval l η₁ | eval l η₂ | idext e l
... | ne x | ne x | refl = refl , cong-App (idext e F) (idext e τ)
... | lab l | lab l | refl = refl , λ { fzero → refl , idext e (F · τ) }
fundC {η₁ = η₁} {η₂} e (eq-─ eq₂ eq₁) = cong-─V (fundC e eq₂) (fundC e eq₁)
fundC {η₁ = η₁} {η₂} e (eq-labTy {l = l} {τ = τ} eq) with eval l η₁ | fundC e eq 
... | lab ℓ | refl = refl , (λ { fzero → refl , idext e τ })
fundC {η₁ = η₁} {η₂} e (eq-<$>-─ {F = F} {ρ₂} {ρ₁}) 
  with eval ρ₂ η₁ | eval ρ₂ η₂ | idext e ρ₂
fundC {η₁ = η₁} {η₂} e (eq-<$>-─ {F = F} {ρ₂} {ρ₁}) | ne x₁ | ne .x₁ | refl = 
  cong (_<$> x₁) (cong `λ (reify-≋ (idext e F .snd .snd S (reflect-≋ refl)))) , cong-<$> (idext e F) (idext e ρ₁)
fundC {η₁ = η₁} {η₂} e (eq-<$>-─ {F = F} {ρ₂} {ρ₁}) | x₁ ▹ x₂ | x₃ ▹ x₄ | fst₁ , snd₁ = 
  (fst₁ , idext e F .snd .snd id snd₁) , (cong-<$> (idext e F) (idext e ρ₁))
fundC {η₁ = η₁} {η₂} e (eq-<$>-─ {F = F} {ρ₂} {ρ₁}) | x₁ ─ x₂ | y₁ ─ y₂ | fst₁ , snd₁ = 
  ((cong-<$> (idext e F) fst₁) , (cong-<$> (idext e F) snd₁)) , (cong-<$> (idext e F) (idext e ρ₁))
fundC {η₁ = η₁} {η₂} e (eq-<$>-─ {F = F} {ρ₂} {ρ₁}) | row (n , P) oρ₂-1 | row (.n , P') oρ₂-2 | refl , I
  with eval ρ₁ η₁ | eval ρ₁ η₂ | idext e ρ₁ 
... | ne x₃ | ne .x₃ | refl = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , 
  (cong (_<$> x₃) (cong `λ (reify-≋ (idext e F .snd .snd S (reflect-≋ refl)))))
... | x₃ ▹ x₄ | x₅ ▹ x₆ | fst₂ , snd₂ = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , fst₂ , (idext e F .snd .snd id snd₂)
... | c₂ ─ c₁ | d₂ ─ d₁ | fst₂ , snd₂ = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , (cong-<$> (idext e F) fst₂) , (cong-<$> (idext e F) snd₂)
... | row (m , Q) oρ₁-1 | row (.m , Q') oρ₁-2 | refl , J = 
  ↻-<$>V-─V 
    (eval F η₁) (eval F η₂) 
    n m P P' {oρ₂-1} {oρ₂-2} 
    Q Q' {oρ₁-1} {oρ₁-2} 
    (idext e F) (refl , I) (refl , J)
fundC {Δ₁ = Δ₁} {η₁ = η₁} {η₂} e (eq-compl {xs = xs} {ys}) = ↻-syn/sem-compl xs ys e


fundC-Row e eq-[] = refl , (λ ())
fundC-Row {η₁ = η₁} e (eq-cons {xs = xs} eq-l eq-τ eq-r) with 
  evalRow xs η₁ | fundC-Row e eq-r 
... | n , P | refl , eq = refl , (λ { fzero → eq-l , (fundC e eq-τ) ; (fsuc i) → eq i })

idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflect-≋ refl

-------------------------------------------------------------------------------
-- Completeness

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fundC idEnv-≋ eq)  

-------------------------------------------------------------------------------
-- Completeness for rows

completeness-row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → ρ₁ ≡r ρ₂ → ⇓Row ρ₁ ≡ ⇓Row ρ₂
completeness-row {ρ₁ = ρ₁} {ρ₂} eq with 
    evalRow ρ₁ idEnv 
  | evalRow ρ₂ idEnv
  | fundC-Row {ρ₁ = ρ₁} {ρ₂} idEnv-≋ eq 
... | n , P | m , Q | refl , I = reifyRow-≋ P Q I

 

--------------------------------------------------------------------------------
-- renaming commutes with ⇓ 

↻-ren-⇓ : ∀ (r : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → renₖNF r (⇓ τ) ≡ ⇓ (renₖ r τ)
↻-ren-⇓ r τ = 
  trans 
    (↻-ren-reify r {V₁ = eval τ idEnv} {V₂ = eval τ idEnv} (fundC {τ₁ = τ} idEnv-≋ eq-refl)) 
    (reify-≋ 
      (trans-≋ 
        (↻-renSem-eval r τ idEnv-≋) 
        (trans-≋ (idext (λ { x → ↻-ren-reflect r (` x) }) τ) (sym-≋ (↻-renₖ-eval r τ idEnv-≋)))))

↻-ren-⇓Row : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ : SimpleRow Type Δ₁ R[ κ ]) → 
               renRowₖNF r (⇓Row ρ) ≡ ⇓Row (renRowₖ r ρ)
↻-ren-⇓Row r ρ with 
    evalRow ρ idEnv 
  |  evalRow ρ (idEnv ∘ r)
  |  evalRow (renRowₖ r ρ) idEnv
  | fundC-Row {ρ₁ = ρ} idEnv-≋ reflᵣ 
  | ↻-renₖ-evalRow r ρ idEnv-≋ 
  | ↻-renSem-evalRow r ρ idEnv-≋ 
  | idext-row (λ { x → ↻-ren-reflect r (` x) }) ρ
... | n , P | m , Q | j , K | (refl , d) | (refl , rel₁) | (refl , rel₂) | (refl , rel₃) =
  trans 
    (↻-ren-reifyRow P P r (λ { i → refl , d i .snd })   ) 
    (reifyRow-≋ (λ i → overᵣ (renSem r) (P i)) K (λ { i → (trans (rel₂ i .fst) (trans (rel₃ i .fst) (sym (rel₁ i .fst)))) , (trans-≋ (rel₂ i .snd) (trans-≋ (rel₃ i .snd) (sym-≋ (rel₁ i .snd)))) }))
 
-------------------------------------------------------------------------------
-- Helper to substitute under an eval
 
evalCRSubst : ∀ {η₁ η₂ : Env Δ₁ Δ₂}
    → Env-≋ η₁ η₂
    → {τ₁ τ₂ : Type Δ₁ κ}
    → τ₁ ≡ τ₂
    → (eval τ₁ η₁) ≋ (eval τ₂ η₂)
evalCRSubst p {τ₁ = τ} refl = idext p τ
