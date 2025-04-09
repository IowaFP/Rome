{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Soundness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming 
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Properties.Equivalence
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming
  using (↻-ren-⇑NE ; ↻-ren-⇑)

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness.Relation public

--------------------------------------------------------------------------------
-- Soundness for Π 
       
sound-Πε : ∀ {κ} {Δ} → ⟦_⟧≋_ {Δ = Δ} {κ = κ} (Π · (ε {κ = κ})) (ΠV (right εV))
sound-Πε {★} = eq-refl
sound-Πε {L} = eq-refl
sound-Πε {κ `→ κ₁} ρ {v} {V} rel-f = 
  subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc) 
  (subst-⟦⟧≋ 
    (eq-sym (eq-· eq-refl (eq-· eq-β eq-refl) ))
  (subst-⟦⟧≋ 
    (eq-sym (eq-· eq-refl eq-β)) 
  (subst-⟦⟧≋ 
    (eq-sym (eq-· eq-refl eq-map)) 
  sound-Πε)))
sound-Πε {R[ κ ]} = (eq-trans eq-Π eq-map) , (λ ())

sound-Π : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Π Π-Kripke
sound-Π {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = L} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = κ `→ κ₁} ρ {v} {left f} q φ {v₂} {V₂} rel-v₂ = 
  subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc) 
  (subst-⟦⟧≋ 
    (eq-sym (eq-trans 
      (eq-· 
        eq-refl 
        (eq-trans 
          {!(eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ ?}) eq-refl)!} 
          {!!})) 
        {!!})) 
  {!!}) 
-- subst-⟦⟧≋ 
  -- (eq-sym (eq-Π-assoc {ρ = renₖ ρ f} {τ = v})) 
  -- (subst-⟦⟧≋ 
  --   (eq-sym 
  --     (eq-trans 
  --       (eq-· eq-refl 
  --         (eq-trans 
  --           (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
  --           eq-β)) 
  --         eq-refl)) 
  --       (sound-Π ρ
  --          {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
  --          (eq-<$> 
  --            (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq)))))) 
  --            (eq-trans 
  --              (eq-trans 
  --                (inst (subₖ-weaken (renₖ ρ f) v)) 
  --                (renₖ-≡t ρ q)) 
  --              (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Π {κ₁ = R[ κ ]} ρ {v} {left x} q = {!!}
sound-Π {κ₁ = κ} ρ {v} {right y} q = {!!}
-- sound-Π  ρ {v} {nothing} q  = 
--   subst-⟦⟧≋ 
--     (eq-· eq-refl (eq-sym q)) 
--     sound-Πε
-- sound-Π {κ₁ = κ₁ `→ κ₂} ρ {f} {just (left g)} q = λ ρ {v} {V} eq → 
--   subst-⟦⟧≋ 
--   (eq-sym (eq-Π-assoc {ρ = renₖ ρ f} {τ = v})) 
--   (subst-⟦⟧≋ 
--     (eq-sym 
--       (eq-trans 
--         (eq-· eq-refl 
--           (eq-trans 
--             (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
--             eq-β)) 
--           eq-refl)) 
--         (sound-Π ρ
--            {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
--            (eq-<$> 
--              (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq)))))) 
--              (eq-trans 
--                (eq-trans 
--                  (inst (subₖ-weaken (renₖ ρ f) v)) 
--                  (renₖ-≡t ρ q)) 
--                (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
-- sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {just (left x)} q = 
--     eq-trans 
--         (eq-· eq-refl q) 
--         (eq-trans 
--             eq-Π 
--             (eq-<$> 
--                 (eq-trans 
--                     eq-η 
--                     (eq-λ (reify-⟦⟧≋ (sound-Π id eq-refl)))) 
--                 eq-refl))
-- sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {v₁} {just (right (l , f))} (q , sound-f)  ρ₂ {v₂} {V₂} rel-v = ?
--   -- rewrite renSem-id V₂ = 
--   -- (subst-⟦⟧≋ 
--   --   (eq-sym eq-Π-assoc) 
--   --   (sound-Π ρ₂ 
--   --     (eq-trans 
--   --       (eq-· 
--   --         (eq-· eq-refl (renₖ-≡t  ρ₂ q)) 
--   --         eq-refl) 
--   --       (eq-trans 
--   --         (eq-· eq-β eq-refl) 
--   --         (eq-trans 
--   --           eq-β 
--   --           ((eq-trans 
--   --             eq-▹$ 
--   --             (eq-▹
--   --               ((eq-trans (inst (subₖ-weaken (renₖ ρ₂ (⇑ l)) v₂)) (eq-sym (inst (↻-ren-⇑ ρ₂ l))))) 
--   --               (eq-trans 
--   --             eq-β 
--   --             (eq-trans 
--   --               eq-β 
--   --               (eq-trans 
--   --                 (inst (sym (subₖ-comp (renₖ (liftₖ S) (renₖ (liftₖ ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) ) 
--   --                 (eq-trans 
--   --                   (eq-sym (inst (↻-subₖ-renₖ (renₖ (liftₖ ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) 
--   --                   (eq-trans 
--   --                     (inst (sym (↻-subₖ-renₖ (⇑ (reify (f S (reflect (` Z)))))))) 
--   --                     ((reify-⟦⟧≋ (subst-⟦⟧≋ 
--   --                       (inst (subₖ-cong 
--   --                         {σ₁ = (extendₖ (` ∘ ρ₂) v₂)} 
--   --                         (λ { Z → sym (subₖ-weaken v₂ _) ; (S x) → refl }) 
--   --                         (⇑ (reify (f S (reflect (` Z))))))) 
--   --                            (subst-⟦⟧≋ 
--   --                             (eq-trans 
--   --                               eq-β 
--   --                               (eq-trans 
--   --                                 (inst (sym (↻-subₖ-renₖ (⇑ (reify (f S (reflect (` Z)))))))) 
--   --                                 (inst (subₖ-cong  (λ { Z → refl
--   --                                                     ; (S x) → refl }) (⇑ (reify (f S (reflect (` Z))))))))) 
--   --                             (sound-f ρ₂ rel-v))))))))))))))) , 
--   --     refl-⟦⟧≋ (sound-f ρ₂ rel-v) )))
-- sound-Π {κ₁ = R[ κ₁ ]} ρ {v} {just (right (l , τ))} (q , rel) =
--     eq-trans 
--         (eq-· eq-refl q) 
--         (eq-trans 
--             eq-Π▹ 
--             (eq-▹ eq-refl (reify-⟦⟧≋ (sound-Π id rel)))) , 
--     refl-⟦⟧≋ (sound-Π id rel)

--------------------------------------------------------------------------------
-- Soundness for Σ (identical logic as Π but woefully duplicated)

sound-Σε : ∀ {κ} {Δ} → ⟦_⟧≋_ {Δ = Δ} {κ = κ} (Σ · (ε {κ = κ})) {!!}
sound-Σε {★} = eq-refl
sound-Σε {L} = eq-refl
-- sound-Σε {κ `→ κ₁} ρ {v} {V} rel-f = 
--   subst-⟦⟧≋ 
--     (eq-sym eq-Σ-assoc) 
--   (subst-⟦⟧≋ 
--     (eq-sym (eq-· eq-refl (eq-· eq-β eq-refl)))
--   (subst-⟦⟧≋ 
--     (eq-sym (eq-· eq-refl eq-β)) 
--   (subst-⟦⟧≋ 
--     (eq-sym (eq-· eq-refl ?)) 
--   sound-Σε)))
-- sound-Σε {R[ κ ]} = eq-trans eq-Σ ?

sound-Σ : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Σ Σ-Kripke
-- sound-Σ  ρ {v} {nothing} q  = 
--   subst-⟦⟧≋ 
--     (eq-· eq-refl (eq-sym q)) 
--     sound-Σε       
-- sound-Σ {κ₁ = ★} ρ {v} {just (left x)} q = eq-· eq-refl q
-- sound-Σ {κ₁ = L} ρ {v} {just (left x)} q = eq-· eq-refl q
-- sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {f} {just (left g)} q = λ ρ {v} {V} eq → 
--   subst-⟦⟧≋ 
--   (eq-sym (eq-Σ-assoc {ρ = renₖ ρ f} {τ = v})) 
--   (subst-⟦⟧≋ 
--     (eq-sym 
--       (eq-trans 
--         (eq-· eq-refl 
--           (eq-trans 
--             (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
--             eq-β)) 
--           eq-refl)) 
--         (sound-Σ ρ
--            {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
--            (eq-<$> 
--              (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq))) ))) 
--              (eq-trans 
--                (eq-trans 
--                  (inst (subₖ-weaken (renₖ ρ f) v)) 
--                  (renₖ-≡t ρ q)) 
--                (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
-- sound-Σ {κ₁ = R[ κ₁ ]} ρ {v} {just (left x)} q = 
--     eq-trans 
--         (eq-· eq-refl q) 
--         (eq-trans 
--             eq-Σ 
--             (eq-<$> 
--                 (eq-trans 
--                     eq-η 
--                     (eq-λ (reify-⟦⟧≋ (sound-Σ id eq-refl)))) 
--                 eq-refl))
-- sound-Σ {κ₁ = ★} ρ {v} {just (right (l , τ))} q = eq-· eq-refl (fst q)
-- sound-Σ {κ₁ = L} ρ {v} {just (right (l , τ))} q = eq-· eq-refl (fst q)
-- sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {v₁} {just (right (l , f))} (q , sound-f)  ρ₂ {v₂} {V₂} rel-v = ?
--   -- rewrite renSem-id V₂ = 
--   -- (subst-⟦⟧≋ 
--   --   (eq-sym eq-Σ-assoc) 
--   --   (sound-Σ ρ₂ 
--   --     (eq-trans 
--   --       (eq-· 
--   --         (eq-· eq-refl (renₖ-≡t  ρ₂ q)) 
--   --         eq-refl) 
--   --       (eq-trans 
--   --         (eq-· eq-β eq-refl) 
--   --         (eq-trans 
--   --           eq-β 
--   --           ((eq-trans 
--   --             eq-▹$ 
--   --             (eq-▹
--   --               ((eq-trans (inst (subₖ-weaken (renₖ ρ₂ (⇑ l)) v₂)) (eq-sym (inst (↻-ren-⇑ ρ₂ l))))) 
--   --               (eq-trans 
--   --             eq-β 
--   --             (eq-trans 
--   --               eq-β 
--   --               (eq-trans 
--   --                 (inst (sym (subₖ-comp (renₖ (liftₖ S) (renₖ (liftₖ ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) ) 
--   --                 (eq-trans 
--   --                   (eq-sym (inst (↻-subₖ-renₖ (renₖ (liftₖ ρ₂) (⇑ (reify (f S (reflect (` Z))))))))) 
--   --                   (eq-trans 
--   --                     (inst (sym (↻-subₖ-renₖ (⇑ (reify (f S (reflect (` Z)))))))) 
--   --                     ((reify-⟦⟧≋ (subst-⟦⟧≋ 
--   --                       (inst (subₖ-cong 
--   --                         {σ₁ = (extendₖ (` ∘ ρ₂) v₂)} 
--   --                         (λ { Z → sym (subₖ-weaken v₂ _) ; (S x) → refl }) 
--   --                         (⇑ (reify (f S (reflect (` Z))))))) 
--   --                            (subst-⟦⟧≋ 
--   --                             (eq-trans 
--   --                               eq-β 
--   --                               (eq-trans 
--   --                                 (inst (sym (↻-subₖ-renₖ (⇑ (reify (f S (reflect (` Z)))))))) 
--   --                                 (inst (subₖ-cong  (λ { Z → refl
--   --                                                     ; (S x) → refl }) (⇑ (reify (f S (reflect (` Z))))))))) 
--   --                             (sound-f ρ₂ rel-v))))))))))))))) , 
--   --     refl-⟦⟧≋ (sound-f ρ₂ rel-v) )))
-- sound-Σ {κ₁ = R[ κ₁ ]} ρ {v} {just (right (l , τ))} (q , rel) =
--     eq-trans 
--         (eq-· eq-refl q) 
--         (eq-trans 
--             eq-Σ▹ 
--             (eq-▹ eq-refl (reify-⟦⟧≋ (sound-Σ id rel)))) , 
--     refl-⟦⟧≋ (sound-Σ id rel)

--------------------------------------------------------------------------------
-- Fundamental lemma  

fundS : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)

-- fundSRow : ∀ {Δ₁ Δ₂ κ}(τ : SimpleRow Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
--           ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)
          
fundSPred : ∀ {Δ₁ Δ₂ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η)           
fundSPred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-⟦⟧≋ (fundS ρ₁ e)) eq-· (reify-⟦⟧≋ (fundS ρ₂ e)) ~ (reify-⟦⟧≋ (fundS ρ₃ e))
fundSPred (ρ₁ ≲ ρ₂) e = (reify-⟦⟧≋ (fundS ρ₁ e)) eq-≲ (reify-⟦⟧≋ (fundS ρ₂ e))

fundS (` α) {σ} {η} e = e α
fundS (`λ τ) {σ} {η} e ρ {v} {V} q = 
  subst-⟦⟧≋ 
    (eq-sym eq-β) 
    (subst-⟦⟧≋ 
      (eq-trans 
        (eq-trans 
          (inst (subₖ-cong (λ { Z → refl ; (S x) → trans (renₖ-subₖ-id σ ρ (σ x)) (↻-subₖ-renₖ (σ x)) }) τ)) 
          (inst (subₖ-comp τ))) 
        (inst (↻-subₖ-renₖ (subₖ (liftsₖ σ) τ)))) 
      (fundS τ (extend-⟦⟧≋ (ren-⟦⟧≋ ρ ∘ e) q)))
fundS (τ₁ · τ₂) {σ} {η} e  = 
  subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) 
    (fundS τ₁ e id (fundS τ₂ e))
fundS (τ₁ `→ τ₂) {σ} {η} e = eq-→ (fundS τ₁ e) (fundS τ₂ e)
fundS (`∀ τ) {σ} {η} e = eq-∀ (fundS τ {liftsₖ σ} {lifte η} (weaken-⟦⟧≋ e))
fundS (μ τ) {σ} {η} e = eq-μ
    (eq-trans 
        (eq-η {f = subₖ σ τ}) 
        (eq-λ (fundS τ e S eq-refl)))
fundS (π ⇒ τ) {σ} {η} e = eq-⇒ (fundSPred π e) (fundS τ e)
fundS (lab l) {σ} {η} e = eq-refl
fundS (l ▹ τ) {σ} {η} e = eq-labTy (reify-⟦⟧≋ (fundS τ e)) , λ { fzero → fundC (λ { x → {!reify-⟦⟧≋ (e x)!} }) eq-refl } -- {!fundS τ e!} , (λ { fzero → {!fundC !} })
  -- (eq-▹ 
  --   (fundS l e) 
  --   (reify-⟦⟧≋ (fundS τ e))) , 
  --   (refl-⟦⟧≋ (fundS τ e))
fundS ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (fundS τ e)
fundS Π {σ} {η} e = sound-Π
fundS Σ {σ} {η} e =  sound-Σ  
fundS (τ₁ <$> τ₂) {σ} {η} e with eval τ₂ η | inspect (λ x → eval x η) τ₂ | fundS τ₂ e 
... | c  | [[ eq ]] | w = {!!}
-- ... | nothing | [ eq ] | w = eq-trans (eq-<$> eq-refl w) eq-<$>ε
-- ... | just (left x) | [ eq ] | _ = 
--   eq-<$> 
--     (eq-trans 
--       eq-η 
--       (eq-λ 
--         (reify-⟦⟧≋ (fundS τ₁ e S {` Z} {reflect (` Z)} (reflect-⟦⟧≋ eq-refl))))) 
--     (eq-trans 
--       (reify-⟦⟧≋ (fundS τ₂ e)) 
--       (eq-trans (inst (cong (⇑ ∘ reify) eq)) eq-refl))
-- ... | just (right (l , V)) | [ eq ] | (eq₂ , rel-v) = 
--   eq-trans 
--     (eq-<$> (reify-⟦⟧≋ (λ {Δ} → fundS τ₁ e {Δ})) eq₂) 
--     (eq-trans 
--       eq-▹$ 
--       (eq-▹ 
--         eq-refl 
--         (eq-trans 
--           (eq-· 
--             (eq-trans 
--               (eq-λ 
--                 (eq-sym (reify-⟦⟧≋ (fundS τ₁ e S {` Z} {reflect (` Z)} (reflect-⟦⟧≋ eq-refl))))) 
--                 (eq-trans 
--                   (eq-sym eq-η) 
--                   (eq-trans 
--                     (inst (subₖ-cong (λ {κ} x → refl) τ₁)) 
--                     (eq-trans 
--                       eq-refl 
--                       (inst (sym (renₖ-id (subₖ σ τ₁)))))))) 
--               (reify-⟦⟧≋ (rel-v))) 
--           (reify-⟦⟧≋ (fundS τ₁ e id rel-v))))) , 
--   refl-⟦⟧≋ (fundS τ₁ e id rel-v)
fundS ⦅ [] ⦆ {σ} {η} e = eq-refl , (λ { () })
fundS ⦅ x ∷ ρ ⦆ {σ} {η} e = eq-row (eq-cons (reify-⟦⟧≋ (fundS x e)) {!!}) , {!!}

idSR : ∀ {Δ₁} →  ⟦ ` ⟧≋e (idEnv {Δ₁})
idSR α = reflect-⟦⟧≋ eq-refl

--------------------------------------------------------------------------------
-- Soundness claim  

soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 
soundness τ = subst (_≡t ⇑ (⇓ τ)) (subₖ-id τ) ((reify-⟦⟧≋ (fundS τ idSR)))   
  
 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

-- embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
-- embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (soundness τ₂) 
