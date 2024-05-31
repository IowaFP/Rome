{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Terms.Admissible where

open import Preludes.Level

open import Rome.Kinds
open import Rome.Types
import Rome.Types.Syntax as Types
open import Rome.Terms.Syntax
open import Rome.Types.Substitution
open import Rome.Equivalence.Syntax
open import Rome.Entailment.Syntax
open import Rome.GVars.Kinds

--------------------------------------------------------------------------------
-- projection and injection of labeled types.
--
-- (The distinction is that  
--   prj : (ℓ ▹ τ) ≲ ρ ⇒  Π ρ → Π (ℓ R▹ τ)
-- but
--   prj▹ :   (ℓ ▹ τ) ≲ ρ ⇒ Π ρ → (ℓ ▹ τ)
--
-- (And the dual holds for inj and inj▹).

prj▹ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {Ł : Type Δ (L ℓ)} 
       {τ : Type Δ (★ ℓκ)} {ρ : Type Δ R[ ★ ℓκ ]} →          
        Term Δ Φ Γ (Π ρ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
        ------------------------------------------
        Term Δ Φ Γ (Ł ▹ τ)
prj▹ r e = Π⁻¹ (prj r e)          

inj▹ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {Ł : Type Δ (L ℓ)} 
       {τ : Type Δ (★ ℓκ)} {ρ : Type Δ R[ ★ ℓκ ]} →
        Term Δ Φ Γ (Ł ▹ τ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
        ---------------------------------------------
        Term Δ Φ Γ (Σ ρ)
inj▹ s e = inj (Σ s) e

--------------------------------------------------------------------------------
-- The unit term.

u : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}  → 
    Term Δ Φ Γ (U {ℓ = ℓ})
u = lab (lab "unit")

--------------------------------------------------------------------------------
-- Defining 

Functor : Type Δ (((★ ℓ) `→ (★ ℓ)) `→ ★ (lsuc ℓ))
Functor {ℓ = ℓ} = `λ ((★ ℓ) `→ (★ ℓ)) -- F
                  (`∀ (★ ℓ)            -- t
                  (`∀ (★ ℓ)            -- s
                      ((t `→ s) `→ (F ·[ t ]) `→  F ·[ s ])))
      where
        F = tvar (S (S Z))
        t = tvar (S Z)
        s = tvar Z

fmapΣ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → 
        Term Δ Φ Γ (`∀ (R[ ★ ℓ `→ ★ ℓ ]) 
          (Π (⌈ K Functor ⌉· tvar Z) `→ (K Functor) ·[ (Σ (tvar Z)) ]))
fmapΣ {ℓ = ℓ} = `Λ ((R[ ★ ℓ `→ ★ ℓ ])) 
                (`λ (Π (⌈ K Functor ⌉· tvar Z)) 
                (t-≡ 
                  (`Λ (★ ℓ) 
                  (`Λ (★ ℓ) 
                  (`λ {!!} 
                  (`λ {!!} {!!})))) (teq-sym teq-β)))

  

--------------------------------------------------------------------------------
-- Recursive injection.

injμ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →
       Term Δ Φ Γ 
         (`∀ R[ (★ ℓ) `→ (★ ℓ) ] -- y
           (`∀ R[ (★ ℓ) `→ (★ ℓ) ] -- z
             ((tvar (S Z) ≲ tvar Z) ⇒ 
               (Π (⌈ Functor ⌉· tvar (S Z))) `→ 
                 μΣ (tvar (S Z)) `→ μΣ (tvar Z))))
injμ {ℓ = ℓ} = 
  `Λ R[ (★ ℓ) `→ (★ ℓ) ]                           -- y (TVar)
 (`Λ R[ (★ ℓ) `→ (★ ℓ) ]                           -- z (TVar)
 (`ƛ ((tvar (S Z) ≲ tvar Z)) 
 (`λ ((Π (⌈ Functor ⌉· tvar (S Z))))                 -- d (Var)
   (recΣ 
   (`Λ R[ ★ ℓ `→ ★ ℓ ]                             -- w  (TVar)
   (`Λ R[ ★ ℓ `→ ★ ℓ ]                             -- y' (TVar)
   (`ƛ (tvar (Types.S³ Z) · (tvar Z) ~ (tvar (S Z))) 
   (`λ ((Σ (K² (tvar (S Z))) ·[ μΣ (tvar (S Z)) ])) -- v (Var)
   (`λ ((μΣ (tvar (S Z)) `→ K² (μΣ (tvar Z))))     -- r (Var)
       (In (t-≡ 
         (inj {! !} {!!}) 
         (teq-sym teq-lift₃))))))))))))
