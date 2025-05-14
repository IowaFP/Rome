{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Equivalence.Relation.Admissable where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence .Relation

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution

-------------------------------------------------------------------------------
-- Admissable rules

eq-Π▹ : ∀ {l} {τ : Type Δ R[ κ ]}{nl : True (notLabel? κ)} → 

        ----------------------------
        (Π {notLabel = nl} · (l ▹ τ)) ≡t (l ▹ (Π {notLabel = nl} · τ))
eq-Π▹ = eq-trans eq-Π eq-▹$

eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) κ₂} {nl : True (notLabel? κ₂)} → 

        Π {notLabel = nl} · (l ▹ `λ τ) ≡t `λ (Π {notLabel = nl} · (weakenₖ l ▹ τ))
eq-Πλ {l = l} {τ = τ} = 
  eq-trans 
    eq-η 
    (eq-λ 
      (eq-trans 
        eq-Π-assoc 
        (eq-· 
          eq-refl 
          (eq-trans 
            (eq-· 
              eq-β 
              eq-refl) 
            (eq-trans 
              eq-β 
              (eq-trans 
                eq-▹$ 
                (eq-▹ 
                  (inst (trans (sym (↻-subₖ-renₖ (renₖ S l))) (subₖ-id (renₖ S l)))) 
                  (eq-trans 
                    eq-β 
                    (eq-trans 
                      eq-β 
                      (inst (trans 
                        (sym (subₖ-comp (renₖ (liftₖ S) (renₖ (liftₖ S) τ)))) 
                        (trans 
                          (sym (↻-subₖ-renₖ (renₖ (liftₖ S) τ))) 
                          (trans 
                            (sym (↻-subₖ-renₖ τ)) 
                            (trans (subₖ-cong (λ { Z → refl ; (S x) → refl }) τ) (subₖ-id τ)))))))))))))))

