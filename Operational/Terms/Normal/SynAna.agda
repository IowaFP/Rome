{-# OPTIONS --safe #-}
module Rome.Operational.Terms.Normal.SynAna where

open import Rome.Operational.Prelude
open import Rome.Operational.Containment

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Properties.Substitution

open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.SynAna
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Types.Equivalence.Relation
open import Rome.Operational.Types.Equivalence.Properties

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Soundness


open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Substitution

open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Renaming
open import Rome.Operational.Terms.Normal.Entailment.Properties

--------------------------------------------------------------------------------
--
soundness-under-subₖ : ∀ (σ : SubstitutionₖNF (Δ₁ ,, κ) Δ₂)  (τ₂ : Type (Δ₁ ,, κ) κ₂) → 
                  subₖ (⇑ ∘ σ)
                  (⇑ (reify (eval τ₂ (lifte idEnv)))) ≡t subₖ (⇑ ∘ σ) τ₂
soundness-under-subₖ σ τ₂ = 
  eq-trans (subₖ-≡t⇑ {σ = σ}
              {τ₁ = ⇑ (reify (eval τ₂ (lifte idEnv)))} (eq-sym (soundness-liftsₖ τ₂))) 
  (eq-trans 
    (inst (sym (subₖ-comp τ₂))) (subₖ-cong-≡t {σ₁ = subₖ (⇑ ∘ σ) ∘ liftsₖ `}
                                   {σ₂ = ⇑ ∘ σ} (λ { Z → eq-refl ; (S x₁) → eq-refl }) τ₂))
η-norm-under-subₖ : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (x : KVar Δ₁ κ) → 
              subₖ (⇑ ∘ σ) ((⇑ ∘ η-norm ∘ `) x) ≡t ⇑ (σ x)
η-norm-under-subₖ σ x = (subₖ-≡t⇑ {σ = σ} {τ₁ = (⇑ ∘ η-norm ∘ `) x} {τ₂ = ` x} (η-norm-≡t (` x)))

η-norm-under-subₖ-liftsₖ : ∀ (σ₁ : SubstitutionₖNF Δ₁ Δ₂) (σ₂ : SubstitutionₖNF (Δ₂ ,, κ₁) Δ₃) (x : KVar (Δ₁ ,, κ₁) κ) → 
                      subₖ (⇑ ∘ σ₂) (subₖ (liftsₖ (⇑ ∘ σ₁)) ((⇑ ∘ η-norm ∘ `) x)) ≡t subₖ (⇑ ∘ σ₂) (liftsₖ (⇑ ∘ σ₁) x)
η-norm-under-subₖ-liftsₖ σ₁ σ₂ x = 
  eq-trans (inst (sym (subₖ-comp ((⇑ ∘ η-norm ∘ `) x)))) 
  (subₖ-≡t (η-norm-≡t (` x)))
  

--------------------------------------------------------------------------------
-- Lemma 1
              
lem₁ : ∀ (l : NormalType Δ κ₁) (τ : NormalType Δ κ₂) → 
     subₖ (⇑ ∘ extendₖNF idSubst τ) 
      (⇑
       (reify
        (eval
         (subₖ (liftsₖ (⇑ ∘ extendₖNF idSubst l))
          (⇑ (reify (reflect (` Z)))))
         (lifte idEnv))))
      ≡t ⇑ τ 
lem₁ {κ₂ = κ} l τ = eq-trans
                      (soundness-under-subₖ (extendₖNF idSubst τ)
                        (subₖ (liftsₖ (⇑ ∘ extendₖNF idSubst l))
                          (⇑ (reify (reflect (` Z))))))
                    (η-norm-under-subₖ-liftsₖ (extendₖNF idSubst l) (extendₖNF idSubst τ) Z)

--------------------------------------------------------------------------------
-- Lemma 2

lem₂ :  ∀ (l₁ : NormalType ∅ κ₁) (l₂ : NormalType ∅ κ₂) (τ : NormalType ∅ κ) → 
        subₖ (⇑ ∘ extendₖNF idSubst l₁)
        (⇑
        (reify
        (eval
         (subₖ (liftsₖ (⇑ ∘ extendₖNF idSubst l₂))
          (⇑ (reify (eval (weakenₖ (weakenₖ (⇑ τ))) (lifte (lifte idEnv))))))
         (lifte idEnv)))) ≡t ⇑ τ

lem₂ {κ = κ} l₁ l₂ τ = 
  eq-trans 
    (soundness-under-subₖ (extendₖNF idSubst l₁) 
      (subₖ (liftsₖ (⇑ ∘ extendₖNF idSubst l₂))
      (⇑ (reify (eval (weakenₖ (weakenₖ (⇑ τ))) (lifte (lifte idEnv))))))) 
  (eq-trans 
    (inst (sym (subₖ-comp (⇑ (reify (eval (weakenₖ (weakenₖ (⇑ τ))) (lifte (lifte idEnv)))))))) 
  (eq-trans 
    ((subₖ-≡t (eq-sym (reify-⟦⟧≋ (fundS (weakenₖ (weakenₖ (⇑ τ))) (weaken-⟦⟧≋ (weaken-⟦⟧≋ idSR))))))) 
  (eq-trans 
    ((inst ∘ sym) (subₖ-comp (weakenₖ (weakenₖ (⇑ τ))))) 
  (eq-trans 
    (inst (sym ((↻-subₖ-renₖ (weakenₖ (⇑ τ)))))) 
  (eq-trans 
    (inst (sym (↻-subₖ-renₖ (⇑ τ)))) 
  (inst (emptySub _ _)))))))

--------------------------------------------------------------------------------
-- Lemma 3

lem₃ : ∀ (φ : NormalType ∅ (κ `→ ★)) (τ : NormalType ∅ κ) (l : NormalType _ L) → 
       eval {κ = ★}
      (subₖ (λ x₁ → ⇑ (extendₖNF idSubst τ x₁))
       (⇑
        (eval {κ = ★}
         (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst l x₁)))
          (⇑
           (eval {κ = κ `→ ★} (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
            (lifte (lifte idEnv) Z))))
         (lifte idEnv))))
      idEnv
      ≡ 
      φ ·' τ 
lem₃ φ τ l = 
  trans (completeness
           {τ₁ =
            subₖ (λ x₁ → ⇑ (extendₖNF idSubst τ x₁))
            (⇑
             (eval
              (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst l x₁)))
               (⇑
                (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
                 (lifte (lifte idEnv) Z))))
              (lifte idEnv)))}
  (eq-trans (subₖ-≡t⇑
                 {σ = (extendₖNF idSubst τ)}
                 {τ₁ =
                         ⇑
                         (eval
                          (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst l x₁)))
                           (⇑
                            (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
                             (lifte (lifte idEnv) Z))))
                          (lifte idEnv))}
  (eq-trans (eq-sym (soundness-liftsₖ (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst l x₁)))
        (⇑
         (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
          (lifte (lifte idEnv) Z)))))) 
  (eq-trans (inst (sym (subₖ-comp (⇑
        (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
         (lifte (lifte idEnv) Z)))))) (subₖ-≡t
                                         {σ = subₖ (liftsₖ `) ∘ liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst l x₁))}
                                         {τ₁ =
                                          ⇑
                                          (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
                                           (lifte (lifte idEnv) Z))}
                                         ((eq-sym ((reify-⟦⟧≋ {V = (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
       (lifte (lifte idEnv) Z))} (fundS (weakenₖ (weakenₖ (⇑ φ)) · ` Z) (weaken-⟦⟧≋ (weaken-⟦⟧≋ idSR))))))))))) 
  (eq-· 
    (eq-trans 
      (inst (sym ((subₖ-comp (subₖ
        (λ {κ = κ₁} z →
           liftsₖ (λ {κ = κ₂} z₁ → liftsₖ (λ {κ = κ₃} z₂ → ` z₂) z₁) z)
        (weakenₖ (weakenₖ (⇑ φ))))))) ) 
    (eq-trans 
      ((inst ∘ sym) (subₖ-comp (weakenₖ (weakenₖ (⇑ φ))))) 
    (eq-trans 
      (eq-sym (inst (↻-subₖ-renₖ (weakenₖ (⇑ φ))))) 
    (eq-trans 
      (eq-sym (inst (↻-subₖ-renₖ (⇑ φ)))) 
    (inst (emptySub (⇑ φ) _)))))) eq-refl))) 
  (sym (stability-·' φ τ))

--------------------------------------------------------------------------------
-- lemma 4

lem₄ : ∀ (xs : SimpleRow NormalType ∅ R[ κ ]) (υ₁ : NormalType ∅ κ) (υ₂ : NormalType ∅ L) → xs ≡ reifyRow
          (evalRow
           (subRowₖ (λ x₁ → ⇑ (extendₖNF idSubst υ₁ x₁))
            (⇑Row
             (reifyRow
              (evalRow
               (subRowₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst υ₂ x₁)))
                (⇑Row
                 (reifyRow'
                  (evalRow (renRowₖ (S {κ₂ = κ}) (renRowₖ (S {κ₂ = L}) (⇑Row xs)))
                   (extende
                    (λ x₁ →
                       renSem S
                       (extende (λ x₂ → renSem S (reflect (` x₂))) (ne (` Z)) x₁))
                    (reflect (` Z)))
                   .fst)
                  (evalRow (renRowₖ S (renRowₖ S (⇑Row xs)))
                   (extende
                    (λ x₁ →
                       renSem S
                       (extende (λ x₂ → renSem S (reflect (` x₂))) (ne (` Z)) x₁))
                    (reflect (` Z)))
                   .snd))))
               (lifte idEnv)))))
               idEnv)   
lem₄ [] υ₁ υ₂ = refl
lem₄ ((l' , τ) ∷ xs) υ₁ υ₂ = cong₂ _∷_ (cong₂ _,_ refl (trans (sym (stability τ)) (sym (completeness (lem₂ υ₁ υ₂ τ))) )) (lem₄ xs υ₁ υ₂)



--------------------------------------------------------------------------------
-- cutSyn takes a syn body M, which synthesizes a term at type Π {ℓ ▹ τ , ρ},
-- and builds a body M' that synthesizes a term at type Π ρ. This is necessary
-- for us to recursively synthesize records.

cutSyn :  ∀ (φ : NormalType ∅ (κ `→ ★)) (z : Label × NormalType ∅ κ) (zs : SimpleRow NormalType ∅ R[ κ ]) →
            {ozs : True (normalOrdered? (z ∷ zs))} {ozs' : True (normalOrdered? zs)} → 
            NormalTerm ∅ (SynT' (⦅ z ∷ zs ⦆ ozs) φ) → NormalTerm ∅ (SynT' (⦅ zs ⦆ ozs') φ)
cutSyn {κ = κ} φ (l , τ) zs {ozs' = ozs'} M = (Λ (Λ (`ƛ (`λ 
           (conv (lem₅ t) 
           (weakenTermByType (weakenTermByPred (weakenTermByKind (weakenTermByKind {κ = L} M))) 
           ·[ ℓℓ ] 
           ·[ u ] 
           ·⟨ (n-var 
                (convPVar 
                  (cong₂ _≲_ (cong₂ _▹ₙ_ refl (sym #2)) 
                  (cong-⦅⦆ (#3 zs))) (T Z))) n-⨾ 
                  n-incl {oxs = fromWitness (subst NormalOrdered (#3 zs) 
                                            (reifyRowOrdered _ 
                                              (evalRowOrdered (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv)) 
                                                (orderedRenRowₖ S (renRowₖ S (⇑Row zs)) 
                                                  (orderedRenRowₖ S (⇑Row zs) (Ordered⇑ _ (toWitness ozs')))))))} 
                         (λ x i → there i) ⟩ 
           · ⌊ℓ⌋) )))))
       where
         ℓℓ = ne (` (S Z))
         u = η-norm (` Z)
         ⌊ℓ⌋ = ` Z

         t = (eval (weakenₖ (weakenₖ (⇑ φ))) (lifte (lifte idEnv)) id
                      (idEnv Z))

         σ : SubstitutionₖNF ((∅ ,, _) ,, _) ((∅ ,, _) ,, _)
         σ Z     = u
         σ (S Z) = ℓℓ

         lem₅ : ∀ {κ} (t : NormalType _ κ) → 
              reify (eval {κ = κ}
              (subₖ (λ x₁ → ⇑ (extendₖNF idSubst u x₁))
               (⇑
                (reify (eval {κ = κ}
                 (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                  (⇑
                   (renₖNF (liftₖ (liftₖ S))
                    (renₖNF (liftₖ (liftₖ S))
                     t))))
                 (lifte idEnv)))))
              idEnv)
              ≡
              t
         lem₅ t = trans 
                (completeness
                  (eq-trans 
                    (subₖ-≡t (eq-sym (soundness-liftsₖ (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                       (⇑ (renₖNF (liftₖ (liftₖ S)) (renₖNF (liftₖ (liftₖ S)) t))))))) 
                  (eq-trans (inst (sym (subₖ-comp (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                      (⇑ (renₖNF (liftₖ (liftₖ S)) (renₖNF (liftₖ (liftₖ S)) t))))) )) 
                  (eq-trans 
                      (inst (sym (subₖ-comp (⇑ (renₖNF (liftₖ (liftₖ S)) (renₖNF (liftₖ (liftₖ S)) t)))))) 
                  (eq-trans 
                    (subₖ-≡t
                       {τ₁ = ⇑ (renₖNF (liftₖ (liftₖ S)) (renₖNF (liftₖ (liftₖ S)) t))} 
                       (eq-trans 
                         ((inst (↻-ren-⇑ (liftₖ (liftₖ S)) (renₖNF (liftₖ (liftₖ S)) t)))) 
                         (inst (cong (renₖ (liftₖ (liftₖ S))) (↻-ren-⇑ (liftₖ (liftₖ S)) t))))) 
                  (eq-trans 
                    (inst (sym (↻-subₖ-renₖ (renₖ (liftₖ (liftₖ S)) (⇑ t))))) 
                  (eq-trans 
                    (inst (sym (↻-subₖ-renₖ (⇑ t)))) 
                  (eq-trans
                     (subₖ-cong-≡t
                      {σ₁ =
                       ((subₖ (subₖ (λ x₁ → ⇑ (extendₖNF idSubst u x₁)) ∘ liftsₖ `) ∘
                         liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                        ∘ liftₖ (liftₖ S))
                       ∘ liftₖ (liftₖ S)}
                      {σ₂ = ⇑ ∘ σ} (λ { Z → eq-refl 
                                      ; (S Z) → eq-trans
                                                   (subₖ-cong-≡t
                                                    {σ₁ =
                                                     λ x₁ → subₖ (λ x₂ → ⇑ (extendₖNF idSubst u x₂)) (liftsₖ ` x₁)}
                                                    {σ₂ = extendₖ ` (⇑ u)} (λ { Z → eq-refl ; (S y₁) → η-norm-≡t (` y₁) }) (weakenₖ (⇑ ℓℓ)))
                                                   (inst (subₖ-weaken (⇑ ℓℓ) (⇑ u))) }) (⇑ t))
                     (eq-trans 
                         (subₖ-cong-≡t 
                           {σ₁ = ⇑ ∘ σ} 
                           {σ₂ = `} 
                           (λ { Z → η-norm-≡t (` Z) ; (S Z) → eq-refl }) (⇑ t)) (inst (subₖ-id (⇑ t)))))))))))) 
                     (stability t)              

         #2 : reify
               (eval
                (subₖ (λ x₁ → ⇑ (extendₖNF idSubst u x₁))
                 (⇑
                  (reify
                   (eval
                    (subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                     (⇑
                      (renₖNF (liftₖ (liftₖ S))
                       (renₖNF (liftₖ (liftₖ S)) (reify (idEnv Z))))))
                    (extende (λ x₁ → weakenSem (reflect (` x₁))) (idEnv Z))))))
                (λ x₁ → reflect (` x₁)))
               ≡ reify (reflect (` Z))
         #2 = trans 
                (completeness
                     (subₖ-≡t⇑ {σ = extendₖNF idSubst u}
                      (eq-trans 
                        (eq-sym (soundness-liftsₖ ((subₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                                                  (⇑ (renₖNF (liftₖ (liftₖ S))
                                                  (renₖNF (liftₖ (liftₖ S)) (reify (idEnv Z)))))))) ) 
                      (eq-trans (inst (sym (subₖ-comp (⇑
                                (renₖNF (liftₖ (liftₖ S))
                                (renₖNF (liftₖ (liftₖ S)) (reify (idEnv Z)))))))) 
                      (subₖ-≡t                                   
                      (eq-trans 
                        (inst (cong ⇑ (sym (renₖNF-comp (liftₖ (liftₖ S)) (liftₖ (liftₖ S)) (reify (idEnv Z)))))) 
                        (η-norm-≡t'ren (` Z) {liftₖ (liftₖ S) ∘ (liftₖ (liftₖ S))}))))))) 
                (stability (η-norm (` Z)))

         #3 : ∀ (zs : SimpleRow NormalType ∅ R[ κ ]) → reifyRow
                (evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv)))
                ≡
                reifyRow'
                (evalRow
                (subRowₖ (λ x₁ → ⇑ (extendₖNF idSubst u x₁))
                 (⇑Row
                  (reifyRow'
                   (evalRow
                    (subRowₖ (liftsₖ (λ x₁ → ⇑ (extendₖNF idSubst ℓℓ x₁)))
                     (⇑Row
                      (renRowₖNF (liftₖ (liftₖ S))
                       (renRowₖNF (liftₖ (liftₖ S))
                        (reifyRow'
                         (evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                          .fst)
                         (λ x₁ →
                              evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                             .snd x₁))))))
                    (lifte idEnv) .fst)
                   (λ x₁ →
                        evalRow
                       (subRowₖ (liftsₖ (λ x₂ → ⇑ (extendₖNF idSubst ℓℓ x₂)))
                       (⇑Row
                        (renRowₖNF (liftₖ (liftₖ S))
                         (renRowₖNF (liftₖ (liftₖ S))
                          (reifyRow'
                           (evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                            .fst)
                           (λ x₂ →
                                evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                               .snd x₂))))))
                      (lifte idEnv) .snd x₁))))
                idEnv .fst)
               (λ x₁ →
                    evalRow
                   (subRowₖ (λ x₂ → ⇑ (extendₖNF idSubst u x₂))
                   (⇑Row
                    (reifyRow'
                     (evalRow
                      (subRowₖ (liftsₖ (λ x₂ → ⇑ (extendₖNF idSubst ℓℓ x₂)))
                       (⇑Row
                        (renRowₖNF (liftₖ (liftₖ S))
                         (renRowₖNF (liftₖ (liftₖ S))
                          (reifyRow'
                           (evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                            .fst)
                           (λ x₂ →
                                evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                               .snd x₂))))))
                      (lifte idEnv) .fst)
                     (λ x₂ →
                          evalRow
                         (subRowₖ (liftsₖ (λ x₃ → ⇑ (extendₖNF idSubst ℓℓ x₃)))
                         (⇑Row
                          (renRowₖNF (liftₖ (liftₖ S))
                           (renRowₖNF (liftₖ (liftₖ S))
                            (reifyRow'
                             (evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                              .fst)
                             (λ x₃ →
                                  evalRow (renRowₖ S (renRowₖ S (⇑Row zs))) (lifte (lifte idEnv))
                                 .snd x₃))))))
                        (lifte idEnv) .snd x₂))))
             idEnv .snd x₁)     
         #3 [] = refl
         #3 ((l , υ) ∷ zs) = cong₂ _∷_ (cong₂ _,_ refl (sym (lem₅ _)  )) (#3 zs)


--------------------------------------------------------------------------------
-- Synthesizing records

synRecord : ∀ (φ : NormalType ∅ (κ `→ ★)) 
              (zs : SimpleRow NormalType ∅ R[ κ ])
              (ozs : True (normalOrdered? zs)) → 
              NormalTerm ∅ (SynT' (⦅ zs ⦆ ozs) φ) → Record ∅ (map (overᵣ (φ ·'_)) zs)
synRecord φ [] ozs M = ∅
synRecord φ ((l , τ) ∷ zs) ozs M = 
  l ▹ conv (lem₃ φ τ (lab l)) 
           (M ·[ lab l ] 
              ·[ τ ] 
              ·⟨ n-incl (λ { (l' , τ') 
                 (here refl) → 
                   here (cong₂ _,_ refl 
                     (completeness 
                       (eq-trans (lem₁ (lab l) τ) 
                       (eq-sym (lem₂ τ (lab l) τ)) ))) }) ⟩ 
             · # (lab l))  ⨾ 
       (synRecord φ zs (fromWitness (normalOrdered-tail (l , τ) zs (toWitness ozs))) 
         (cutSyn φ (l , τ) zs {ozs} {ozs' = (fromWitness (normalOrdered-tail (l , τ) zs (toWitness ozs)))} M))

--------------------------------------------------------------------------------
-- Analyzing variants


getApplicand : ∀ {l : Label} {φ : NormalType Δ (κ₁ `→ κ₂)} {φτ : NormalType Δ κ₂} 
                 {xs : SimpleRow NormalType Δ R[ κ₁ ]} → 
               (l , φτ) ∈ (map (overᵣ (φ ·'_)) xs) → 
               ∃[ τ ] ((l , τ) ∈ xs × φτ ≡ φ ·' τ)
getApplicand {xs = []} ()
getApplicand {xs = ((l , τ) ∷ xs)} (here refl) = τ , ((here refl) , refl)
getApplicand {l = l} {φ} {φτ} {xs = (_ ∷ xs)} (there i) with getApplicand {l = l} {φ} {φτ} {xs} i
... | τ , i' , eq = τ , ((there i') , eq)

anaVariant : ∀ (φ : NormalType ∅ (κ `→ ★)) 
              (zs : SimpleRow NormalType ∅ R[ κ ])
              (τ : NormalType ∅ ★)
              (ozs : True (normalOrdered? zs))
              (ozs' : True (normalOrdered? (map (overᵣ (φ ·'_)) zs)))
              (M : NormalTerm ∅ (AnaT' (⦅ zs ⦆ ozs) φ τ))
              (v : NormalTerm ∅ (Σ (⦅ map (overᵣ (φ ·'_)) zs ⦆ ozs'))) →
              Value v → 
              NormalTerm ∅ τ
anaVariant φ zs τ ozs ozs' M v (V-Σ l {M'} V i) with getApplicand {φ = φ} i 
... | υ , i' , refl = (conv 
  (trans (completeness (lem₂ υ (lab l) τ)) (stability τ)) 
        (M ·[ lab l ] 
           ·[ υ ] 
           ·⟨ n-incl (λ { (.l , τ') (here refl) → 
                     subst (λ X → (l , τ') ∈ X) (lem₄ zs υ (lab l)) (subst (λ X → (l , X) ∈ _) (trans (sym (stability υ)) (sym (completeness (lem₁ (lab l) υ)))) i') }) ⟩ 
           · # (lab l) 
           · conv (sym (lem₃ φ υ (lab l))) M'))
