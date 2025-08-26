{-# OPTIONS --safe #-}
module Rome.Operational.Types.Theorems.Soundness where

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

open import Rome.Operational.Types.Theorems.Soundness.Relation public 
open import Rome.Operational.Types.Theorems.Soundness.Congruence public 
open import Rome.Operational.Types.Theorems.Soundness.Commutativity public

open import Rome.Operational.Types.Equivalence.Relation

--------------------------------------------------------------------------------
-- Equivalence of membership in syntactic and semantic spaces

∈L→∈Row : ∀ {l : Label} {η₁ : SemEnv Δ₁ Δ₂} {ys : SimpleRow Type Δ₁ R[ κ ]} → l ∈L ys → l ∈Row (evalRow ys η₁ .snd)
∈L→∈Row {ys = ys} Here = fzero , refl
∈L→∈Row {ys = (l' , τ) ∷ ys} (There ev) = (fsuc (∈L→∈Row ev .fst)) , (∈L→∈Row ev .snd)

∈Row→∈L : ∀ {l : Label} {η₁ : SemEnv Δ₁ Δ₂} {ys : SimpleRow Type Δ₁ R[ κ ]} → l ∈Row (evalRow ys η₁ .snd) → l ∈L ys
∈Row→∈L {ys = (l , τ) ∷ ys} (fzero , refl) = Here
∈Row→∈L {ys = (l , τ) ∷ ys} (fsuc i , refl) = There (∈Row→∈L (i , refl))

--------------------------------------------------------------------------------
-- Commutativity of syntactic and semantic complement

↻-syn/sem-compl : ∀ {η₁ η₂ : SemEnv Δ₁ Δ₂} (xs ys : SimpleRow Type Δ₁ R[ κ ]) → 
                  SemEnv-≋ η₁ η₂ → 
                  (evalRow xs η₁ ∖v evalRow ys η₁) ≋R (evalRow (xs ∖s ys) η₂)
↻-syn/sem-compl [] ys e = refl , (λ ())
↻-syn/sem-compl {η₁ = η₁} {η₂} ((l , τ) ∷ xs) ys e with l ∈Row? (evalRow ys η₁ .snd) | l ∈L? ys
... | yes p | yes q = ↻-syn/sem-compl xs ys e
... | yes p | no q = ⊥-elim (q (∈Row→∈L p)) 
... | no q | yes p = ⊥-elim (q (∈L→∈Row p)) 
... | no p | no q  with compl (evalRow xs η₁ .snd) (evalRow ys η₁ .snd) | evalRow (xs ∖s ys) η₂ | ↻-syn/sem-compl xs ys e
↻-syn/sem-compl ((l , τ) ∷ xs) ys e | no p | no q | x | y | (refl , ih') = refl , λ { fzero → refl , idext e τ ; (fsuc i) → ih' i }

-------------------------------------------------------------------------------
-- Fundamental theorem (soundness)

fundS : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
       SemEnv-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fundS-pred : ∀ {π₁ π₂ : Pred Type Δ₁ R[ κ ]} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
            SemEnv-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂
fundS-Row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ₁ R[ κ ]} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
            SemEnv-≋ η₁ η₂ → ρ₁ ≡r ρ₂ → evalRow ρ₁ η₁ ≋R evalRow ρ₂ η₂

fundS-pred e (τ₁ eq-≲ τ₂) = cong₂ _≲_ (reify-≋ (fundS e τ₁)) (reify-≋ (fundS e τ₂))
fundS-pred e (τ₁ eq-· τ₂ ~ τ₃) rewrite
    reify-≋ (fundS e τ₁) 
  | reify-≋ (fundS e τ₂) 
  | reify-≋ (fundS e τ₃) = refl

fundS {τ₁ = τ} e eq-refl = idext e τ
fundS e (eq-sym eq) = sym-≋ (fundS (sym-≋ ∘ e) eq)
fundS e (eq-trans eq₁ eq₂) = trans-≋ (fundS (refl-≋ₗ ∘ e) eq₁) (fundS e eq₂)
fundS e (eq-→ eq-τ eq-υ) = cong₂ _`→_ (fundS e eq-τ) (fundS e eq-υ)
fundS {κ = κ} e (eq-· eq₁ eq₂) = cong-App (fundS e eq₁) (fundS e eq₂)
fundS e (eq-∀ eq) = cong `∀ (fundS (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) eq)
fundS {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) 
  with eval τ η₁ | eval υ η₂ | fundS e eq
... |  y         | y₁        | Unif-F , Unif-G , Ext = 
  cong μ (cong `λ (Ext S refl))
fundS e (eq-⌊⌋ eq) rewrite fundS e eq = refl
fundS e (eq-λ {τ = τ} {υ = υ} eq) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ τ (extend-≋ (λ x → ren-≋ ρ₁ (e x)) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (e x)) }) τ))  , 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ υ (extend-≋ (λ x → ren-≋ ρ₁ (sym-≋ (e x))) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (sym-≋ (e x))) }) υ)), 
    λ ρ q → fundS (extend-≋ (λ x → ren-≋ ρ (e x)) q) eq
fundS {η₁ = η₁} {η₂ = η₂} e (eq-η {f = f}) = 
  fst (idext e f) , 
  fst (snd (idext {η₁ = η₁} {η₂ = η₂} e (`λ (weakenₖ f · (` Z))))) , 
  λ r {V₁} {V₂} v → weaken-η-≋ f e r v V₂ (refl-≋ᵣ v)

fundS {η₁ = η₁} {η₂ = η₂} e (eq-β {τ₁ = τ₁} {τ₂}) = 
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
fundS {η₁ = η₁} {η₂} e (eq-▹ {l₁ = l₁} {l₂} eq-l eq-τ) with eval l₁ η₁ | eval l₂ η₂ | fundS e eq-l 
... | ne x | ne x | refl = refl , fundS e eq-τ
... | lab l | lab l | refl = refl , (λ { fzero → refl , fundS e eq-τ } )
fundS e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fundS-pred e eq-π) (fundS e eq-τ)
fundS e (eq-Π-assoc {ρ = ρ} {τ}) = 
  cong-Π 
    (cong-<$> 
      (cong-apply (idext e τ))
      (ren-≋ id (idext e ρ))) 
fundS e (eq-Σ-assoc {ρ = ρ} {τ}) =
  cong-Σ 
    (cong-<$> 
      (cong-apply (idext e τ))
      (ren-≋ id (idext e ρ))) 
fundS e (eq-Π {ρ = ρ} {nl}) = cong-<$> (idext e (Π {notLabel = nl})) (idext e ρ)
fundS e (eq-Σ {ρ = ρ} {nl}) = cong-<$> (idext e (Σ {notLabel = nl})) (idext e ρ) 
fundS e (eq-<$> t u) = cong-<$> (fundS e t) (fundS e u)
fundS {Δ₁ = Δ₁} {κ = κ} {η₁ = η₁} {η₂} e (eq-map {κ₁ = κ₁} {κ₂} {F = F} {ρ = ρ} {oρ}) = go ρ
  where
    go : (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) → (evalRow ρ η₁ .fst ,
       (λ x₁ → map₂ (eval F η₁ id) (evalRow ρ η₁ .snd x₁)))
      ≋R
      (evalRow (map (map₂ (_·_ F)) ρ) η₂ .fst ,
       evalRow (map (map₂ (_·_ F)) ρ) η₂ .snd)
    go [] = refl , (λ ())
    go (x ∷ ρ) with evalRow ρ η₁ | go ρ
    ... | n , P | refl , eq = refl , (λ { fzero → refl , (cong-App (idext e F) (idext e (x . snd))) ; (fsuc i) → eq i })
fundS e (eq-row eq) = fundS-Row e eq
fundS e (eq-lab refl) = refl
fundS {η₁ = η₁} {η₂} e (eq-▹$ {l = l} {τ = τ} {F}) with eval l η₁ | eval l η₂ | idext e l
... | ne x | ne x | refl = refl , cong-App (idext e F) (idext e τ)
... | lab l | lab l | refl = refl , λ { fzero → refl , idext e (F · τ) }
fundS {η₁ = η₁} {η₂} e (eq-∖ eq₂ eq₁) = cong-∖V (fundS e eq₂) (fundS e eq₁)
fundS {η₁ = η₁} {η₂} e (eq-labTy {l = l} {τ = τ} eq) with eval l η₁ | fundS e eq 
... | lab ℓ | refl = refl , (λ { fzero → refl , idext e τ })
fundS {η₁ = η₁} {η₂} e (eq-<$>-∖ {F = F} {ρ₂} {ρ₁}) 
  with eval ρ₂ η₁ | eval ρ₂ η₂ | idext e ρ₂
fundS {η₁ = η₁} {η₂} e (eq-<$>-∖ {F = F} {ρ₂} {ρ₁}) | x₁ ▹ x₂ | x₃ ▹ x₄ | fst₁ , snd₁ = 
  (fst₁ , idext e F .snd .snd id snd₁) , (cong-<$> (idext e F) (idext e ρ₁))
fundS {η₁ = η₁} {η₂} e (eq-<$>-∖ {F = F} {ρ₂} {ρ₁}) | x₁ ∖ x₂ | y₁ ∖ y₂ | fst₁ , snd₁ = 
  ((cong-<$> (idext e F) fst₁) , (cong-<$> (idext e F) snd₁)) , (cong-<$> (idext e F) (idext e ρ₁))
fundS {η₁ = η₁} {η₂} e (eq-<$>-∖ {F = F} {ρ₂} {ρ₁}) | φ₁ <$> n₁ | φ₂ <$> n₂ | refl , Unif-φ₁ , Unif-φ₂ , Ext-φ , refl = 
  (refl , 
  (λ r₁ r₂ n → trans-≋ 
      (idext e F .fst r₁ r₂ (φ₁ r₁ n) (φ₂ r₁ n) (Ext-φ r₁ n)) 
      (refl-Extₗ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≋ 
        (Unif-φ₂ r₁ r₂ n) 
        (sym-≋ (Ext-φ (r₂ ∘ r₁) (renₖNE r₂ n)))))) , 
  (λ r₁ r₂ n → trans-≋
    (idext e F .snd .fst r₁ r₂ (φ₂ r₁ n) (φ₁ r₁ n)
     (sym-≋ (Ext-φ r₁ n)))
    (refl-Extᵣ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≋
      (Unif-φ₁ r₁ r₂ n) 
      (Ext-φ (r₂ ∘ r₁) (renₖNE r₂ n))))) , 
  (λ r v → idext e F .snd .snd  r (Ext-φ r v)) , 
  refl) ,
  (cong-<$> (idext e F) (idext e ρ₁))
fundS {η₁ = η₁} {η₂} e (eq-<$>-∖ {F = F} {ρ₂} {ρ₁}) | row (n , P) oρ₂-1 | row (.n , P') oρ₂-2 | refl , I
  with eval ρ₁ η₁ | eval ρ₁ η₂ | idext e ρ₁ 
... | x₃ ▹ x₄ | x₅ ▹ x₆ | fst₂ , snd₂ = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , fst₂ , (idext e F .snd .snd id snd₂)
... | c₂ ∖ c₁ | d₂ ∖ d₁ | fst₂ , snd₂ = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , (cong-<$> (idext e F) fst₂) , (cong-<$> (idext e F) snd₂)
... | row (m , Q) oρ₁-1 | row (.m , Q') oρ₁-2 | refl , J = 
  ↻-<$>V-∖V 
    (eval F η₁) (eval F η₂) 
    n m P P' {oρ₂-1} {oρ₂-2} 
    Q Q' {oρ₁-1} {oρ₁-2} 
    (idext e F) (refl , I) (refl , J)
... | φ₁ <$> n₁ | φ₂ <$> n₂ | refl , Unif-φ₁ , Unif-φ₂ , Ext-φ , refl = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , 
  refl , 
  (λ r₁ r₂ n → trans-≋ 
      (idext e F .fst r₁ r₂ (φ₁ r₁ n) (φ₂ r₁ n) (Ext-φ r₁ n)) 
      (refl-Extₗ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≋ 
        (Unif-φ₂ r₁ r₂ n) 
        (sym-≋ (Ext-φ (r₂ ∘ r₁) (renₖNE r₂ n)))))) , 
  (λ r₁ r₂ n → trans-≋
    (idext e F .snd .fst r₁ r₂ (φ₂ r₁ n) (φ₁ r₁ n)
     (sym-≋ (Ext-φ r₁ n)))
    (refl-Extᵣ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≋
      (Unif-φ₁ r₁ r₂ n) 
      (Ext-φ (r₂ ∘ r₁) (renₖNE r₂ n))))) , 
  (λ r v → idext e F .snd .snd  r (Ext-φ r v)) , 
  refl
fundS {Δ₁ = Δ₁} {η₁ = η₁} {η₂} e (eq-compl {xs = xs} {ys}) = ↻-syn/sem-compl xs ys e
fundS {η₁ = η₁} {η₂} e (eq-map-id {τ = τ}) = map-id-≋ (idext e τ) 
fundS {η₁ = η₁} {η₂} e (eq-map-∘ {f = f} {g = g} {τ = τ}) = map-∘-≋ f g e id (idext e τ)


fundS-Row e eq-[] = refl , (λ ())
fundS-Row {η₁ = η₁} e (eq-cons {xs = xs} eq-l eq-τ eq-r) with 
  evalRow xs η₁ | fundS-Row e eq-r 
... | n , P | refl , eq = refl , (λ { fzero → eq-l , (fundS e eq-τ) ; (fsuc i) → eq i })

idEnv-≋ : ∀ {Δ} → SemEnv-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflect-≋ refl

-------------------------------------------------------------------------------
-- Soundness

soundness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
soundness eq = reify-≋ (fundS idEnv-≋ eq)  

-------------------------------------------------------------------------------
-- Soundness for rows

soundness-row : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → ρ₁ ≡r ρ₂ → ⇓Row ρ₁ ≡ ⇓Row ρ₂
soundness-row {ρ₁ = ρ₁} {ρ₂} eq with 
    evalRow ρ₁ idEnv 
  | evalRow ρ₂ idEnv
  | fundS-Row {ρ₁ = ρ₁} {ρ₂} idEnv-≋ eq 
... | n , P | m , Q | refl , I = reifyRow-≋ P Q I

 

--------------------------------------------------------------------------------
-- renaming commutes with ⇓ 

↻-ren-⇓ : ∀ (r : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → renₖNF r (⇓ τ) ≡ ⇓ (renₖ r τ)
↻-ren-⇓ r τ = 
  trans 
    (↻-ren-reify r {V₁ = eval τ idEnv} {V₂ = eval τ idEnv} (fundS {τ₁ = τ} idEnv-≋ eq-refl)) 
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
  | fundS-Row {ρ₁ = ρ} idEnv-≋ reflᵣ 
  | ↻-renₖ-evalRow r ρ idEnv-≋ 
  | ↻-renSem-evalRow r ρ idEnv-≋ 
  | idext-row (λ { x → ↻-ren-reflect r (` x) }) ρ
... | n , P | m , Q | j , K | (refl , d) | (refl , rel₁) | (refl , rel₂) | (refl , rel₃) =
  trans 
    (↻-ren-reifyRow P P r (λ { i → refl , d i .snd })   ) 
    (reifyRow-≋ (λ i → map₂ (renSem r) (P i)) K (λ { i → (trans (rel₂ i .fst) (trans (rel₃ i .fst) (sym (rel₁ i .fst)))) , (trans-≋ (rel₂ i .snd) (trans-≋ (rel₃ i .snd) (sym-≋ (rel₁ i .snd)))) }))
 
-------------------------------------------------------------------------------
-- Helper to substitute under an eval
 
evalCRSubst : ∀ {η₁ η₂ : SemEnv Δ₁ Δ₂}
    → SemEnv-≋ η₁ η₂
    → {τ₁ τ₂ : Type Δ₁ κ}
    → τ₁ ≡ τ₂
    → (eval τ₁ η₁) ≋ (eval τ₂ η₂)
evalCRSubst p {τ₁ = τ} refl = idext p τ
