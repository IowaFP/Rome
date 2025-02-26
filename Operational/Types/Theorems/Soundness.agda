{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Soundness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Properties
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming
  using (↻-ren-⇑NE ; ↻-ren-⇑)

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Theorems.Soundness.Relation 

open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Soundness for Π 
       
sound-Π : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Π π-Kripke
sound-Π {κ₁ = ★} ρ {v} {left x} q = eq-· eq-refl q
sound-Π {κ₁ = L} ρ {v} {left x} q = eq-· eq-refl q
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {f} {left g} q = λ ρ {v} {V} eq → 
  subst-≋⟦⟧ 
  (eq-sym (eq-Π-assoc {ρ = ren ρ f} {τ = v})) 
  (subst-≋⟦⟧ 
    (eq-sym 
      (eq-trans 
        (eq-· eq-refl 
          (eq-trans 
            (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = ren ρ f}) eq-refl) 
            eq-β)) 
          eq-refl)) 
        (sound-Π ρ
           {v = `λ (` Z · ren S v) <$> sub (extend ` v) (ren S (ren ρ f))} 
           (eq-<$> 
             (eq-λ (reify-≋⟦⟧ (reflect-≋⟦⟧ (eq-· eq-refl (reify-≋⟦⟧ (ren-≋⟦⟧ S eq))) ))) 
             (eq-trans 
               (eq-trans 
                 (inst (sub-weaken (ren ρ f) v)) 
                 (cong-ren-≡t ρ q)) 
               (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {left x} q = 
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Π 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-≋⟦⟧ (sound-Π id eq-refl)))) 
                eq-refl))
sound-Π {κ₁ = ★} ρ {v} {right (l , τ)} q = eq-· eq-refl (fst q)
sound-Π {κ₁ = L} ρ {v} {right (l , τ)} q = eq-· eq-refl (fst q)
sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {v₁} {right (l , f)} (q , sound-f)  ρ₂ {v₂} {V₂} rel-v = 
  (subst-≋⟦⟧ 
    (eq-sym eq-Π-assoc) 
    (sound-Π ρ₂ 
      (eq-trans 
        (eq-· 
          (eq-· eq-refl (cong-ren-≡t  ρ₂ q)) 
          eq-refl) 
        (eq-trans 
          (eq-· eq-β eq-refl) 
          (eq-trans 
            eq-β 
            ((eq-trans 
              eq-▹$ 
              (eq-▹
                ((eq-trans (inst (sub-weaken (ren ρ₂ (⇑ l)) v₂)) (eq-sym (inst (↻-ren-⇑ ρ₂ l))))) 
                (eq-trans 
              eq-β 
              (eq-trans 
                eq-β 
                (eq-trans 
                  (inst (sym (sub-comp (ren (lift S) (ren (lift ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) ) 
                  (eq-trans 
                    (eq-sym (inst (↻-sub-ren (ren (lift ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) 
                    (eq-trans 
                      (inst (sym (↻-sub-ren (⇑ (reify (f S (reflect (` Z)))))))) 
                      ((reify-≋⟦⟧ (subst-≋⟦⟧ 
                        (inst (sub-cong 
                          {σ₁ = (extend (` ∘ ρ₂) v₂)} 
                          (λ { Z → sym (sub-weaken v₂ _) ; (S x) → refl }) 
                          (⇑ (reify (f S (reflect (` Z))))))) 
                             (subst-≋⟦⟧ 
                              (eq-trans 
                                eq-β 
                                (eq-trans 
                                  (inst (sym (↻-sub-ren (⇑ (reify (f S (reflect (` Z)))))))) 
                                  (inst (sub-cong  (λ { Z → refl
                                                      ; (S x) → refl }) (⇑ (reify (f S (reflect (` Z))))))))) 
                              (sound-f ρ₂ rel-v))))))))))))))) , 
      refl-≋⟦⟧ (sound-f ρ₂ rel-v) )))
sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {right (l , τ)} (q , rel) =
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Π▹ 
            (eq-▹ eq-refl (reify-≋⟦⟧ (sound-Π id rel)))) , 
    refl-≋⟦⟧ (sound-Π id rel)

--------------------------------------------------------------------------------
-- Soundness for Σ (identical logic as Π but woefully duplicated)
       
sound-Σ : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Σ σ-Kripke
sound-Σ {κ₁ = ★} ρ {v} {left x} q = eq-· eq-refl q
sound-Σ {κ₁ = L} ρ {v} {left x} q = eq-· eq-refl q
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {f} {left g} q = λ ρ {v} {V} eq → 
  subst-≋⟦⟧ 
  (eq-sym (eq-Σ-assoc {ρ = ren ρ f} {τ = v})) 
  (subst-≋⟦⟧ 
    (eq-sym 
      (eq-trans 
        (eq-· eq-refl 
          (eq-trans 
            (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = ren ρ f}) eq-refl) 
            eq-β)) 
          eq-refl)) 
        (sound-Σ ρ
           {v = `λ (` Z · ren S v) <$> sub (extend ` v) (ren S (ren ρ f))} 
           (eq-<$> 
             (eq-λ (reify-≋⟦⟧ (reflect-≋⟦⟧ (eq-· eq-refl (reify-≋⟦⟧ (ren-≋⟦⟧ S eq))) ))) 
             (eq-trans 
               (eq-trans 
                 (inst (sub-weaken (ren ρ f) v)) 
                 (cong-ren-≡t ρ q)) 
               (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Σ {κ₁ = R[ κ₁ ]} ρ {v} {left x} q = 
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Σ 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-≋⟦⟧ (sound-Σ id eq-refl)))) 
                eq-refl))
sound-Σ {κ₁ = ★} ρ {v} {right (l , τ)} q = eq-· eq-refl (fst q)
sound-Σ {κ₁ = L} ρ {v} {right (l , τ)} q = eq-· eq-refl (fst q)
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {v₁} {right (l , f)} (q , sound-f)  ρ₂ {v₂} {V₂} rel-v = 
  (subst-≋⟦⟧ 
    (eq-sym eq-Σ-assoc) 
    (sound-Σ ρ₂ 
      (eq-trans 
        (eq-· 
          (eq-· eq-refl (cong-ren-≡t  ρ₂ q)) 
          eq-refl) 
        (eq-trans 
          (eq-· eq-β eq-refl) 
          (eq-trans 
            eq-β 
            ((eq-trans 
              eq-▹$ 
              (eq-▹
                ((eq-trans (inst (sub-weaken (ren ρ₂ (⇑ l)) v₂)) (eq-sym (inst (↻-ren-⇑ ρ₂ l))))) 
                (eq-trans 
              eq-β 
              (eq-trans 
                eq-β 
                (eq-trans 
                  (inst (sym (sub-comp (ren (lift S) (ren (lift ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) ) 
                  (eq-trans 
                    (eq-sym (inst (↻-sub-ren (ren (lift ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) 
                    (eq-trans 
                      (inst (sym (↻-sub-ren (⇑ (reify (f S (reflect (` Z)))))))) 
                      ((reify-≋⟦⟧ (subst-≋⟦⟧ 
                        (inst (sub-cong 
                          {σ₁ = (extend (` ∘ ρ₂) v₂)} 
                          (λ { Z → sym (sub-weaken v₂ _) ; (S x) → refl }) 
                          (⇑ (reify (f S (reflect (` Z))))))) 
                             (subst-≋⟦⟧ 
                              (eq-trans 
                                eq-β 
                                (eq-trans 
                                  (inst (sym (↻-sub-ren (⇑ (reify (f S (reflect (` Z)))))))) 
                                  (inst (sub-cong  (λ { Z → refl
                                                      ; (S x) → refl }) (⇑ (reify (f S (reflect (` Z))))))))) 
                              (sound-f ρ₂ rel-v))))))))))))))) , 
      refl-≋⟦⟧ (sound-f ρ₂ rel-v) )))
sound-Σ {κ₁ = R[ κ₁ ]} ρ {v} {right (l , τ)} (q , rel) =
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Σ▹ 
            (eq-▹ eq-refl (reify-≋⟦⟧ (sound-Σ id rel)))) , 
    refl-≋⟦⟧ (sound-Σ id rel)

--------------------------------------------------------------------------------
-- Fundamental lemma  

fund : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitution Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          σ ≋e η → (sub σ τ) ≋⟦ (eval τ η) ⟧
          
fundPred : ∀ {Δ₁ Δ₂ κ}(π : Pred Δ₁ R[ κ ]){σ : Substitution Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          σ ≋e η → (subPred σ π) ≡p ⇑Pred (evalPred π η)           
fundPred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-≋⟦⟧ (fund ρ₁ e)) eq-· (reify-≋⟦⟧ (fund ρ₂ e)) ~ (reify-≋⟦⟧ (fund ρ₃ e))
fundPred (ρ₁ ≲ ρ₂) e = (reify-≋⟦⟧ (fund ρ₁ e)) eq-≲ (reify-≋⟦⟧ (fund ρ₂ e))

fund Unit {σ} {η} e = eq-refl
fund (` α) {σ} {η} e = e α
fund (`λ τ) {σ} {η} e = {! fund τ (weaken-≋ e)   !}
fund (τ₁ · τ₂) {σ} {η} e  = 
  subst-≋⟦⟧ 
    (eq-· (inst (ren-id (sub σ τ₁))) eq-refl) 
    (fund τ₁ e id (fund τ₂ e))
fund (τ₁ `→ τ₂) {σ} {η} e = eq-→ (fund τ₁ e) (fund τ₂ e)
fund (`∀ κ τ) {σ} {η} e = eq-∀ (fund τ {lifts σ} {↑e η} (weaken-≋ e))
fund (μ τ) {σ} {η} e = eq-μ
    (eq-trans 
        (eq-η {f = sub σ τ}) 
        (eq-λ (fund τ e S eq-refl)))
fund (π ⇒ τ) {σ} {η} e = eq-⇒ (fundPred π e) (fund τ e)
fund (lab l) {σ} {η} e = eq-refl
fund (l ▹ τ) {σ} {η} e = 
  (eq-▹ 
    (fund l e) 
    (reify-≋⟦⟧ (fund τ e))) , 
    (refl-≋⟦⟧ (fund τ e))
fund ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (fund τ e)
fund Π {σ} {η} e = sound-Π
fund Σ {σ} {η} e =  sound-Σ  
fund (τ₁ <$> τ₂) {σ} {η} e with eval τ₂ η | inspect (λ x → eval x η) τ₂ | fund τ₂ e 
... | left x | [ eq ] | _ = 
  eq-<$> 
    (eq-trans 
      eq-η 
      (eq-λ 
        (reify-≋⟦⟧ (fund τ₁ e S {` Z} {reflect (` Z)} (reflect-≋⟦⟧ eq-refl))))) 
    (eq-trans 
      (reify-≋⟦⟧ (fund τ₂ e)) 
      (eq-trans (inst (cong (⇑ ∘ reify) eq)) eq-refl))
... | right (l , V) | [ eq ] | (eq₂ , rel-v) = 
  eq-trans 
    (eq-<$> (reify-≋⟦⟧ (λ {Δ} → fund τ₁ e {Δ})) eq₂) 
    (eq-trans 
      eq-▹$ 
      (eq-▹ 
        eq-refl 
        (eq-trans 
          (eq-· 
            (eq-trans 
              (eq-λ 
                (eq-sym (reify-≋⟦⟧ (fund τ₁ e S {` Z} {reflect (` Z)} (reflect-≋⟦⟧ eq-refl))))) 
                (eq-trans 
                  (eq-sym eq-η) 
                  (eq-trans 
                    (inst (sub-cong (λ {κ} x → refl) τ₁)) 
                    (eq-trans 
                      eq-refl 
                      (inst (sym (ren-id (sub σ τ₁)))))))) 
              (reify-≋⟦⟧ (rel-v))) 
          (reify-≋⟦⟧ (fund τ₁ e id rel-v))))) , 
  refl-≋⟦⟧ (fund τ₁ e id rel-v)

idSR : ∀ {Δ₁} →  ` ≋e (idEnv {Δ₁})
idSR α = reflect-≋⟦⟧ eq-refl

--------------------------------------------------------------------------------
-- Soundness claim  

soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ)   
soundness τ = subst (_≡t ⇑ (⇓ τ)) (sub-id τ) ((reify-≋⟦⟧ (fund τ idSR)))   
  
