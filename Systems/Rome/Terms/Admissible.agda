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
-- 

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

--------------------------------------------------------------------------------
-- tie.


-- THis is clusterfuck.
tie : ∀ {ℓ₁ ℓΔ ℓΓ ℓΦ} {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → 
      Term Δ Φ Γ (`∀ (R[ (★ ℓ₁ `→ ★ ℓ₁) ])
                 (`∀ (★ ℓ₁) ((tvar (S Z) ↪ tvar Z) `→ (μΣ (tvar (S Z))) `→ (tvar Z))))
tie {ℓ₁} {Δ = Δ} {Φ = Φ} = 
  `Λ R[ (★ ℓ₁ `→ ★ ℓ₁) ] 
  (`Λ (★ _) 
  (`λ ((tvar (S Z) ↪ tvar Z)) 
  ({!(((var (S Z) ·[ ? ]) ·[ ? ]) ·⟨ ? ⟩) · ? !})))

--------------------------------------------------------------------------------
-- Branching.

_▿μ_   : ∀ {ℓl} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
         {ρ₁ ρ₂ ρ₃ : Type Δ R[ ★ ℓl `→ ★ ℓl ]} {τ : Type Δ (★ ℓl)} →         
         Term Δ Φ Γ (_↪_ {ℓl} ρ₁ τ)  → 
         Term Δ Φ Γ (ρ₂ ↪ τ)  →
         Ent Δ Φ    (ρ₁ · ρ₂ ~ ρ₃) →
         ---------------------------
         Term Δ Φ Γ (ρ₃ ↪ τ)

_▿μ_ {ℓl} M N e = `Λ {!R[ ★ ℓl `→ ★ ℓl ]!} (`Λ {!!} {!!})

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
