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

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Theorems.Soundness.Relation 

open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Fundamental lemma

evalSR : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitution Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          SREnv σ η → (sub σ τ) ≋ (eval τ η) 

β-≋ : ∀ (ρ : Renaming Δ₁ Δ₂) (f : KripkeFunction Δ₁ κ₁ κ₂) 
         (v : Type Δ₂ κ₁) (V : SemType Δ₂ κ₁) → v ≋ V → 
         sub (extend (` ∘ ρ) v) (⇑ (reify (f S (reflect (` Z))))) ≋ f ρ V
β-≋ ρ f v V rel-v = {!   !}          
       
sound-Π : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Π π-Kripke
sound-Π {κ₁ = ★} ρ {v} {left x} q = eq-· eq-refl q
sound-Π {κ₁ = L} ρ {v} {left x} q = eq-· eq-refl q
-- Need more tooling to build _≋_ 
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {f} {left g} q = λ ρ {v} {V} eq → 
  subst-≋ 
  (eq-sym (eq-assoc-Π {ρ = ren ρ f} {τ = v})) 
  (subst-≋ 
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
             (eq-λ (reify-≋ (reflect-≋ (eq-· eq-refl (reify-≋ (ren-≋ S eq))) ))) 
             (eq-trans 
               (eq-trans 
                 (inst (sub-weaken (ren ρ f) v)) 
                 (cong-ren-≡t ρ q)) 
               (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {left x} q = 
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-app-lift-Π 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-≋ (sound-Π id eq-refl)))) 
                eq-refl))
sound-Π {κ₁ = ★} ρ {v} {right (l , τ)} q = eq-· eq-refl (fst q)
sound-Π {κ₁ = L} ρ {v} {right (l , τ)} q = eq-· eq-refl (fst q)
sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {v₁} {right (l , f)} q  ρ₂ {v₂} {V₂} rel-v = {!   !} 
  -- subst-≋ (eq-sym (eq-· (eq-· eq-refl (cong-ren-≡t ρ₂ q)) eq-refl)) 
  -- (subst-≋ 
  --   (eq-sym eq-assoc-Π) 
  --   (subst-≋ 
  --     (eq-sym 
  --     (eq-trans 
  --       (eq-· eq-refl 
  --         (eq-trans 
  --           (eq-· eq-β eq-refl) 
  --           eq-β)) 
  --         eq-refl)) 
  --     (sound-Π ρ₂ 
  --       (eq-trans 
  --         eq-▹$ 
  --         (eq-▹ 
  --           (eq-trans 
  --             (inst (sub-weaken (ren ρ₂ (⇑ l)) v₂)) 
  --             (inst (sym (↻-ren-⇑  ρ₂ l)))) 
  --           (eq-trans 
  --             eq-β 
  --             (eq-trans 
  --               eq-β 
  --               (eq-trans 
  --                 (inst (sym (sub-comp (ren (lift S) (ren (lift ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) ) 
  --                 (eq-trans 
  --                   (eq-sym (inst (↻-sub-ren (ren (lift ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) 
  --                   (eq-trans 
  --                     (inst (sym (↻-sub-ren (⇑ (reify (f S (reflect (` Z)))))))) 
  --                     (reify-≋ (subst-≋ 
  --                       (inst (sub-cong 
  --                         {σ₁ = (extend (` ∘ ρ₂) v₂)} 
  --                         (λ { Z → sym (sub-weaken v₂ _) ; (S x) → refl }) 
  --                         (⇑ (reify (f S (reflect (` Z))))))) 
  --                       {!  !}))))))))))))
sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {right (l , τ)} (q , rel) =
    eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Π 
            (eq-▹ eq-refl (reify-≋ (sound-Π id rel)))) , 
    {!   !}


evalSR Unit {σ} {η} e = eq-refl
evalSR (` α) {σ} {η} e = e α
evalSR (`λ τ) {σ} {η} e = {! evalSR (` Z)   !}
evalSR (τ₁ · τ₂) {σ} {η} e = {! eq-·  !}
evalSR (τ₁ `→ τ₂) {σ} {η} e = eq-→ (evalSR τ₁ e) (evalSR τ₂ e)
evalSR (`∀ κ τ) {σ} {η} e = {!   !}
evalSR (μ τ) {σ} {η} e = eq-μ 
    (eq-trans 
        (eq-η {f = sub σ τ}) 
        (eq-λ (evalSR τ e S eq-refl)))
evalSR (π ⇒ τ) {σ} {η} e = {!   !}
evalSR (lab l) {σ} {η} e = eq-refl
evalSR (l ▹ τ) {σ} {η} e = (eq-▹ (evalSR l e) (reify-≋ (evalSR τ e))) , (subst-≋ (reify-≋ (evalSR τ e)) (evalSR τ e)) -- eq-▹ (evalSR l e) (reify-≋ (evalSR τ e)) 
evalSR ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (evalSR τ e)
evalSR Π {σ} {η} e = sound-Π
evalSR Σ {σ} {η} e = {!   !}
evalSR (τ₁ <$> τ₂) {σ} {η} e = {!   !}        

idSR : ∀ {Δ₁} → SREnv ` (idEnv {Δ₁})
idSR α = reflect-≋ eq-refl

--------------------------------------------------------------------------------
-- Soundness claim  

soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ)   
soundness τ = subst (_≡t ⇑ (⇓ τ)) (sub-id τ) ((reify-≋ (evalSR τ idSR)))   
