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
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming
  using (↻-ren-⇑NE ; ↻-ren-⇑)

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness.Relation public


--------------------------------------------------------------------------------
-- Soundness for Π and other operations

sound-Π : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Π Π-Kripke

-- Mapping Π over a row relates to pre-composition by semantic Π
map-Π : ∀ (n : ℕ) (P : Fin n → SemType Δ L × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
        ⟦ map (overᵣ (_·_ Π)) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΠV (P i .snd))

-- Mapping _apply_ over a row is semantic application
map-apply : ∀ (n : ℕ) (P : Fin n → SemType Δ₁ L × KripkeFunction Δ₁ κ₁ κ₂) → 
               (φ : Renamingₖ Δ₁ Δ₂) → 
               (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
               (v : Type Δ₂ κ₁) (V : SemType Δ₂ κ₁) → 
               (rel-v : ⟦ v ⟧≋ V) → 
             ⟦ map (overᵣ (_·_ (`λ (` Z · weakenₖ v))))
               (subRowₖ (extendₖ ` v)
                 (renRowₖ S (renRowₖ φ (⇑Row (reifyRow (n , P))))))
             ⟧r≋ (n , λ x → renₖNF φ (P x . fst) , apply V id (renKripke φ (P x .snd)))
map-apply zero P φ rel v V rel-v = tt
map-apply (suc n) P φ = {!!} -- (rel-fzero , rel-fsuc) v V rel-v = 
  -- subst-⟦⟧≋ 
  --   (eq-sym eq-β) 
  -- (subst-⟦⟧≋ 
  --   (eq-sym eq-β) 
  -- (subst-⟦⟧≋ 
  --   (inst (subₖ-comp (renₖ (liftₖ S)
  --           (renₖ (liftₖ φ) (⇑ (reify (P fzero S (reflect (` Z))))))))) 
  -- (subst-⟦⟧≋ 
  --   (inst (↻-subₖ-renₖ (renₖ (liftₖ φ) (⇑ (reify (P fzero S (reflect (` Z)))))))) 
  -- (subst-⟦⟧≋ 
  --   (inst (↻-subₖ-renₖ (⇑ (reify (P fzero S (reflect (` Z))))) )) 
  -- (subst-⟦⟧≋ 
  --   (inst (subₖ-cong {σ₁ = extendₖ (` ∘ φ) v} (λ { Z → sym (subₖ-weaken v _) ; (S x) → refl })  (⇑ (reify (P fzero S (reflect (` Z))))))) 
  -- (subst-⟦⟧≋ 
  --   (eq-trans 
  --     eq-β 
  --   (eq-trans 
  --     (inst (sym (↻-subₖ-renₖ {r = liftₖ φ} {σ = extendₖ ` (renₖ id v)} (⇑ (reify (P fzero S (reflect (` Z)))))))) 
  --   (inst (subₖ-cong (λ { Z → renₖ-id v ; (S x) → refl }) (⇑ (reify (P fzero S (reflect (` Z))))))))) 
  -- (rel-fzero φ (ren-⟦⟧≋ id rel-v)))))))) , 
  -- (map-apply n (P ∘ fsuc) φ rel-fsuc v V rel-v)

sound-Π {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = L} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {f} {left g} q = λ ρ {v} {V} eq → 
  subst-⟦⟧≋ 
  (eq-sym (eq-Π-assoc {ρ = renₖ ρ f} {τ = v})) 
  (subst-⟦⟧≋ 
    (eq-sym 
      (eq-trans 
        (eq-· eq-refl 
          (eq-trans 
            (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
            eq-β)) 
          eq-refl)) 
        (sound-Π ρ
           {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
           (eq-<$> 
             (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq)))))) 
             (eq-trans 
               (eq-trans 
                 (inst (subₖ-weaken (renₖ ρ f) v)) 
                 (renₖ-≡t ρ q)) 
               (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Π {κ₁ = R[ κ ]} ρ {v} {left x} q =
 eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Π 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-⟦⟧≋ (sound-Π id eq-refl)))) 
                eq-refl))
sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {right ((n , P) , _)} = {!!} -- (eq , rel) ρ₂ {v} {V} rel-v = 
  -- subst-⟦⟧≋ (eq-sym (eq-Π-assoc)) (sound-Π ρ₂ {renₖ ρ₂ f ?? v} 
  -- ((eq-trans 
  --   (eq-· 
  --     (eq-· 
  --       eq-refl 
  --       (renₖ-≡t ρ₂ eq)) 
  --     eq-refl) 
  -- (eq-trans 
  --   (eq-· eq-β eq-refl) 
  -- (eq-trans 
  --   eq-β 
  -- (eq-trans 
  --   eq-map 
  -- (eq-row 
  --   (reify-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v))))))) , refl-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v)))
sound-Π {κ₁ = R[ κ ]} ρ {v} {right (n , P)} = {!!} -- (eq , rel) = 
  -- eq-trans 
  --   (eq-· eq-refl eq) 
  -- (eq-trans 
  --   eq-Π 
  -- (eq-trans 
  --   eq-map 
  --   (eq-row (reify-⟦⟧r≋ (map-Π n P rel))))) , 
  -- refl-⟦⟧r≋ (map-Π n P rel)

map-Π zero P rel = tt
map-Π (suc n) P = {!!} -- (rel-fzero , rel-fsuc) = (sound-Π id rel-fzero) , (map-Π n (P ∘ fsuc) rel-fsuc)

--------------------------------------------------------------------------------
-- Soundness for Σ (identical logic as Π but woefully duplicated)

sound-Σ : SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} Σ Σ-Kripke
map-Σ : ∀ (n : ℕ) (P : Fin n → SemType Δ L × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
        ⟦ map (overᵣ (_·_ Σ)) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΣV (P i .snd))

sound-Σ {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Σ {κ₁ = L} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {f} {left g} q = λ ρ {v} {V} eq → 
  subst-⟦⟧≋ 
  (eq-sym (eq-Σ-assoc {ρ = renₖ ρ f} {τ = v})) 
  (subst-⟦⟧≋ 
    (eq-sym 
      (eq-trans 
        (eq-· eq-refl 
          (eq-trans 
            (eq-· (eq-β {τ₁ = (`λ (`λ (` Z · ` (S Z)) <$> ` (S Z)))}  {τ₂ = renₖ ρ f}) eq-refl) 
            eq-β)) 
          eq-refl)) 
        (sound-Σ ρ
           {v = `λ (` Z · renₖ S v) <$> subₖ (extendₖ ` v) (renₖ S (renₖ ρ f))} 
           (eq-<$> 
             (eq-λ (reify-⟦⟧≋ (reflect-⟦⟧≋ (eq-· eq-refl (reify-⟦⟧≋ (ren-⟦⟧≋ S eq)))))) 
             (eq-trans 
               (eq-trans 
                 (inst (subₖ-weaken (renₖ ρ f) v)) 
                 (renₖ-≡t ρ q)) 
               (eq-sym (inst (↻-ren-⇑NE ρ g)) )))))
sound-Σ {κ₁ = R[ κ ]} ρ {v} {left x} q =
 eq-trans 
        (eq-· eq-refl q) 
        (eq-trans 
            eq-Σ 
            (eq-<$> 
                (eq-trans 
                    eq-η 
                    (eq-λ (reify-⟦⟧≋ (sound-Σ id eq-refl)))) 
                eq-refl))
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {right (n , P)} = {!!} -- (eq , rel) ρ₂ {v} {V} rel-v = 
  -- subst-⟦⟧≋ (eq-sym (eq-Σ-assoc)) (sound-Σ ρ₂ {renₖ ρ₂ f ?? v} 
  -- ((eq-trans 
  --   (eq-· 
  --     (eq-· 
  --       eq-refl 
  --       (renₖ-≡t ρ₂ eq)) 
  --     eq-refl) 
  -- (eq-trans 
  --   (eq-· eq-β eq-refl) 
  -- (eq-trans 
  --   eq-β 
  -- (eq-trans 
  --   eq-map 
  -- (eq-row 
  --   (reify-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v))))))) , refl-⟦⟧r≋ (map-apply n P ρ₂ rel v V rel-v)))
sound-Σ {κ₁ = R[ κ ]} ρ {v} {right (n , P)} = {!!} -- (eq , rel) = 
  -- eq-trans 
  --   (eq-· eq-refl eq) 
  -- (eq-trans 
  --   eq-Σ 
  -- (eq-trans 
  --   eq-map 
  --   (eq-row (reify-⟦⟧r≋ (map-Σ n P rel))))) , 
  -- refl-⟦⟧r≋ (map-Σ n P rel)

map-Σ zero P rel = tt
map-Σ (suc n) P = {!!} -- (rel-fzero , rel-fsuc) = (sound-Σ id rel-fzero) , (map-Σ n (P ∘ fsuc) rel-fsuc)

--------------------------------------------------------------------------------
-- Fundamental lemma  


fundS : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)
fundSRow : ∀ {Δ₁ Δ₂ κ}(xs : SimpleRow Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subRowₖ σ xs ⟧r≋ (evalRow xs η)

-- mapping an application over a row is application of the semantic row.
fundS-map-app : ∀ (n : ℕ) (P : Fin n → SemType Δ₂ L × SemType Δ₂ κ₁) →  
                (τ₁ : Type Δ₁ (κ₁ `→ κ₂)) → 
                (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
                {σ : Substitutionₖ Δ₁ Δ₂} → {η : Env Δ₁ Δ₂} → 
                ⟦ σ ⟧≋e η → 
                ⟦ map (overᵣ (_·_ (subₖ σ τ₁))) (⇑Row (reifyRow' n P)) ⟧r≋ (n , (λ x → {!!} , eval τ₁ η id (P x .snd)))


fundS-map-app zero P _ _ _ = tt
fundS-map-app (suc n) P τ₁ = {!!} -- (rel-fzero , rel-fsuc) {σ} e =
        -- subst-⟦⟧≋ (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) (fundS τ₁ e id rel-fzero) , 
        -- fundS-map-app n (P ∘ fsuc) τ₁ rel-fsuc e
          
fundSPred : ∀ {Δ₁ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : Env Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η)           
fundSPred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-⟦⟧≋ (fundS ρ₁ e)) eq-· (reify-⟦⟧≋ (fundS ρ₂ e)) ~ (reify-⟦⟧≋ (fundS ρ₃ e))
fundSPred (ρ₁ ≲ ρ₂) e = (reify-⟦⟧≋ (fundS ρ₁ e)) eq-≲ (reify-⟦⟧≋ (fundS ρ₂ e))

fundSRow [] e = tt
fundSRow (x ∷ xs) e = {!!} -- (fundS x e) , (fundSRow xs e)

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
fundS (lab l) {σ} {η} e = {!!}
-- fundS (l ▹ τ) {σ} {η} e = eq-trans (eq-▹ eq-refl ((reify-⟦⟧≋ (fundS τ e)))) eq-labTy , (refl-⟦⟧≋ (fundS τ e)) , tt
fundS ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (fundS τ e)
fundS Π {σ} {η} e = sound-Π
fundS Σ {σ} {η} e =  sound-Σ  
fundS (τ₁ <$> τ₂) {σ} {η} e with eval τ₂ η | inspect (λ x → eval x η) τ₂ | fundS τ₂ e 
... | left x | [[ eq ]] | w =
  eq-<$> 
    (eq-trans 
      eq-η 
      (eq-λ 
        (reify-⟦⟧≋ (fundS τ₁ e S {` Z} {reflect (` Z)} (reflect-⟦⟧≋ eq-refl))))) 
    (eq-trans 
      (reify-⟦⟧≋ (fundS τ₂ e)) 
      (eq-trans (inst (cong (⇑ ∘ reify) eq)) eq-refl))
... | right (n , P) | [[ eq ]] | x = {!!} -- eqₜ , rel = 
    -- (eq-trans 
    --   (eq-<$> 
    --     eq-refl
    --     eqₜ) 
    -- (eq-trans 
    --   eq-map 
    --   (eq-row (reify-⟦⟧r≋ (fundS-map-app n P τ₁ rel e) )))) , 
    -- refl-⟦⟧r≋ (fundS-map-app n P τ₁ rel e)  
fundS (⦅ xs ⦆ oxs) {σ} {η} e with fundSRow xs e
fundS (⦅ [] ⦆ tt) {σ} {η} e | tt = {!!} -- eq-refl , tt
fundS (⦅ x ∷ xs ⦆ oxs) {σ} {η} e | _ = {!!}
fundS (ρ₂ ─ ρ₁) e = {!!}
--   eq-row (eq-cons (reify-⟦⟧≋ (fundS x e)) (reify-⟦⟧r≋ rel-xs)) , 
--   (refl-⟦⟧≋ (fundS x e)) , 
--   refl-⟦⟧r≋ rel-xs

--------------------------------------------------------------------------------
-- Soundness claim  

soundness : ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 
soundness τ = subst (_≡t ⇑ (⇓ τ)) (subₖ-id τ) ((reify-⟦⟧≋ (fundS τ idSR)))   
  
 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (soundness τ₂) 

