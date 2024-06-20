{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Terms.Admissible where

open import Preludes.Level

open import Rome.Kinds
open import Rome.Types
import Rome.Types.Syntax as Types
open import Rome.Terms.Syntax
open import Rome.Terms.Semantics
open import Rome.Terms.Reasoning
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
-- tie.

tie : ∀ {ℓ₁ ℓΔ ℓΓ ℓΦ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → 
      Term Δ Φ Γ (`∀ (R[ (★ ℓ₁ `→ ★ ℓ₁) ])
                 (`∀ (★ ℓ₁) 
                 ((tvar (S Z) ↪ tvar Z) `→ 
                 (Functor ·[ Σ (tvar (S Z)) ]) `→ 
                 (μ (Σ (tvar (S Z)))) `→ (tvar Z))))
tie {ℓ₁} {Δ = Δ} {Φ = Φ} = 
  `Λ R[ (★ ℓ₁ `→ ★ ℓ₁) ]      -- ρ 
  (`Λ (★ _)                    -- τ
    (fix · 
      `λ (_ `→ _) 
      (`λ ((tvar (S Z) ↪ tvar Z)) 
      (`λ (Functor ·[ Σ (tvar (S Z)) ]) 
      (`λ ((μ (Σ (tvar (S Z))))) 
        ((((((φ ·[ ρ ]) ·[ ε ]) ·⟨ n-ε-R ⟩) · (Out v fmap)) · ((ti · φ) · fmap))))))))
  where
    ρ = tvar (S Z)
    ti = var (S³  Z)
    φ = var (S² Z)
    fmap = var (S Z)
    v = var Z

--------------------------------------------------------------------------------
-- Branching.

_▿μ_   : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →
         ---------------------------
         Term Δ Φ Γ (`∀ R[ ★ ℓ `→ ★ ℓ ] -- ρ₁ (S³ Z)
                    (`∀ R[ ★ ℓ `→ ★ ℓ ] -- ρ₂ (S² Z)
                    (`∀ R[ ★ ℓ `→ ★ ℓ ] -- ρ₃ (S  Z)
                    (`∀ (★ ℓ)            -- τ      Z
                    ((tvar (Types.S³ Z)  ↪₂ tvar Z) `→ 
                    (tvar (Types.S² Z) ↪₂ tvar Z) `→ 
                    (tvar (Types.S³ Z)  · tvar (Types.S² Z) ~ tvar ((Types.S Z))) ⇒ 
                    (tvar (S Z) ↪₂ tvar Z)))))) 

_▿μ_ {ℓ = ℓ} = 
  `Λ R[ ★ ℓ `→ ★ ℓ ] 
  (`Λ R[ ★ ℓ `→ ★ ℓ ] 
  (`Λ R[ ★ ℓ `→ ★ ℓ ] 
  (`Λ ((★ ℓ)) 
  (`λ (tvar (Types.S³ Z) ↪₂ tvar Z) 
  (`λ (tvar (Types.S² Z) ↪₂ tvar Z)
  (`ƛ (tvar (Types.S³ Z)  · tvar (Types.S² Z) ~ tvar ((Types.S Z))) 
  (`Λ R[ ★ ℓ `→ ★ ℓ ]   
  (`ƛ ((ρ₃ ≲ w)) 
  (`λ ((Σ ρ₃) ·[ μΣ w ])
  (`λ (μΣ w `→ τ) 
  (((body · v') · r))))))))))))
  where
    ρ₁ = tvar (Types.S⁴ Z)
    ρ₂ = tvar (Types.S³ Z)
    ρ₃ = tvar (Types.S² Z)
    τ = tvar (S Z)
    w = tvar Z
    v = var (S Z)
    v' = t-≡ teq-lift₃ v
    r = var Z
    f' : Term _ _ _ (Σ (ρ₁ ·⌈ (μΣ w) ⌉) `→ (μΣ w `→ τ) `→ τ)
    f' = `λ (Σ (ρ₁ ·⌈ (μΣ w) ⌉)) 
         (`λ ((μΣ w `→ τ)) ((((var (S⁵ Z) ·[ w ]) ·⟨ n-trans (n-·≲L (n-var (S Z))) (n-var Z) ⟩) · t-≡ (teq-sym teq-lift₃) (var (S Z))) · var Z)) 
    g' : Term _ _ _ (Σ (ρ₂ ·⌈ (μΣ w) ⌉) `→ (μΣ w `→ τ) `→ τ)
    g' = `λ (Σ (ρ₂ ·⌈ (μΣ w) ⌉)) 
         (`λ ((μΣ w `→ τ)) ((((var (S⁴ Z) ·[ w ]) ·⟨ n-trans (n-·≲R (n-var (S Z))) (n-var Z) ⟩) · t-≡ (teq-sym teq-lift₃) (var (S Z))) · var Z)) 
    body : Term _ _ _ (Σ (ρ₃ ·⌈ (μΣ w) ⌉) `→ (μΣ w `→ τ) `→ τ)
    body = (f' ▿ g') (n-·lift₁ (n-var (S Z)))
  
--------------------------------------------------------------------------------
-- FmapΣ.

-- fmapΣ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → 
--         Term Δ Φ Γ (`∀ (R[ ★ ℓ `→ ★ ℓ ]) 
--           (Π (⌈ K Functor ⌉· tvar Z) `→ (K Functor) ·[ (Σ (tvar Z)) ]))
-- fmapΣ {ℓ = ℓ} = `Λ ((R[ ★ ℓ `→ ★ ℓ ])) 
--                 (`λ (Π (⌈ K Functor ⌉· tvar Z)) 
--                 (t-≡ 
--                   (`Λ (★ ℓ) 
--                   (`Λ (★ ℓ) 
--                   (`λ {!!} 
--                   (`λ {!!} {!!})))) (teq-sym teq-β)))

  

--------------------------------------------------------------------------------
-- Recursive injection.

-- injμ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →
--        Term Δ Φ Γ 
--          (`∀ R[ (★ ℓ) `→ (★ ℓ) ] -- y
--            (`∀ R[ (★ ℓ) `→ (★ ℓ) ] -- z
--              ((tvar (S Z) ≲ tvar Z) ⇒ 
--                (Π (⌈ Functor ⌉· tvar (S Z))) `→ 
--                  μΣ (tvar (S Z)) `→ μΣ (tvar Z))))
-- injμ {ℓ = ℓ} = {!!}
-- --   `Λ R[ (★ ℓ) `→ (★ ℓ) ]                           -- y (TVar)
-- --  (`Λ R[ (★ ℓ) `→ (★ ℓ) ]                           -- z (TVar)
-- --  (`ƛ ((tvar (S Z) ≲ tvar Z)) 
-- --  (`λ ((Π (⌈ Functor ⌉· tvar (S Z))))                 -- d (Var)
-- --    (recΣ 
-- --    (`Λ R[ ★ ℓ `→ ★ ℓ ]                             -- w  (TVar)
-- --    (`Λ R[ ★ ℓ `→ ★ ℓ ]                             -- y (TVar)
-- --    (`ƛ (tvar (Types.S³ Z) · (tvar Z) ~ (tvar (S Z))) 
-- --    (`λ ((Σ (K² (tvar (S Z))) ·[ μΣ (tvar (S Z)) ])) -- v (Var)
-- --    (`λ ((μΣ (tvar (S Z)) `→ K² (μΣ (tvar Z))))     -- r (Var)
-- --        (In (t-≡ 
-- --          (inj {! !} {!!}) 
-- --          (teq-sym teq-lift₃))))))))))))

--------------------------------------------------------------------------------
-- Helpers? Not sure I need these anymore.

step : ∀ {ℓ ℓκ ℓΔ ℓΓ ℓΦ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ} → 
         {M : Type (Δ ، κ) (★ (ℓ ⊔ ℓκ))} → {N : Type Δ κ} →
      Term Δ Φ Γ ((`λ κ M) ·[ N ]) → Term Δ Φ Γ (M β[ N ])
step m = t-≡ teq-β m

step² : ∀ {ℓΔ ℓΓ ℓΦ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {κ₁ : Kind ℓκ₁} {κ₂ : Kind ℓκ₂} → 
         {M : Type (Δ ، κ₁ ، κ₂) (★ (ℓ ⊔ ℓκ₁ ⊔ ℓκ₂))} → {N₁ : Type Δ κ₁} → { N₂ : Type Δ  κ₂} →
      Term Δ Φ Γ (((`λ κ₁ (`λ κ₂ M)) ·[ N₁ ]) ·[ N₂ ]) → Term Δ Φ Γ ((subst (exts (Z↦ N₁)) M) β[ N₂ ])
step² {_} {κ₁ = κ₁} {κ₂} {M} {N₁} {N₂} m = 
  ((((`λ κ₁ (`λ κ₂ M)) ·[ N₁ ]) ·[ N₂ ])
 ⊩⟨ t-≡ (teq-· teq-β teq-refl) ⟩ 
    ((`λ κ₂ (subst (exts (Z↦ N₁)) M)) ·[ N₂ ]) 
 ⊩⟨ t-≡ teq-β ⟩ 
   (((subst (exts (Z↦ N₁)) M) β[ N₂ ]) 
 ⊩⟨ t-≡ teq-refl ⟩ 
    (λ x → x))) m

