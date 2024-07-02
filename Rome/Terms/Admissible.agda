{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Terms.Admissible where

open import Preludes.Level

open import Rome.Kinds
open import Rome.Types
import Rome.Types.Syntax as Ty
open import Rome.Terms.Syntax
open import Rome.Terms.Semantics
open import Rome.Terms.Reasoning
open import Rome.Types.Substitution
open import Rome.Equivalence.Syntax
open import Rome.Entailment.Syntax
open import Rome.Entailment.Reasoning
open import Rome.GVars.Kinds

--------------------------------------------------------------------------------
-- projection and injection of labeled types.
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
    Term Δ Φ Γ (Unit {ℓ = ℓ})
u = lab (lab "unit")

--------------------------------------------------------------------------------
-- Record selection (sel).
selT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ (lsuc ℓ))
selT {ℓ} =
  `∀ (L ℓ) (`∀ (★ ℓ) (`∀ R[ ★ ℓ ]
    ((Ł R▹ T) ≲ ζ ⇒ Π ζ `→ ⌊ Ł ⌋ `→ T)))
    where
      ζ = tvar Z
      T = tvar (S Z)
      Ł = tvar (S (S Z))


sel : ∀ {ℓ ℓΔ ℓφ ℓΓ} {Δ : KEnv ℓΔ} {φ : PEnv Δ ℓφ}  {Γ : Env Δ ℓΓ} → Term Δ φ Γ (selT {ℓ} {ℓΔ} {Δ})
sel {ℓ} =
  `Λ (L ℓ) (`Λ (★ ℓ) (`Λ R[ (★ ℓ) ]
  (`ƛ ((Ł R▹ T) ≲ ζ) (`λ (Π ζ) (`λ ⌊ Ł ⌋ body)))))
  where
    ζ = tvar Z
    T = tvar (S Z)
    Ł = tvar (S (S Z))

    body = (prj▹ (var (S Z)) (n-var Z)) / (var Z)

--------------------------------------------------------------------------------
-- Variant construct (con).

conT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ (lsuc ℓ))
conT {ℓ} =
  `∀ (L lzero) (`∀ (★ ℓ) (`∀ R[ (★ ℓ) ]
    ((l R▹ t) ≲ z ⇒ ⌊ l ⌋ `→ t `→ Σ z)))
    where
      z = tvar Z
      t = tvar (S Z)
      l = tvar (S (S Z))

con : ∀ {ℓ ℓΔ ℓφ ℓΓ} {Δ : KEnv ℓΔ} {φ : PEnv Δ ℓφ}  {Γ : Env Δ ℓΓ} → Term Δ φ Γ (conT {ℓ})
con {ℓ} {ℓΔ = ℓΔ} = `Λ (L _) (`Λ (★ ℓ) (`Λ R[ (★ ℓ) ]
        (`ƛ ((l R▹ t) ≲ z) ((`λ (⌊ l ⌋) (`λ t Σz))))))
  where
    z = tvar Z
    t = tvar (S Z)
    l = tvar (S (S Z))

    x = var Z
    l'  = var (S Z)
    Σz = inj▹ (l' ▹ x) (n-var Z)

--------------------------------------------------------------------------------
-- Case (case).

caseT : ∀ {ℓ ι ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ((lsuc ℓ) ⊔ (lsuc ι)))
caseT {ℓ} {ι} =
  `∀ (L lzero) (`∀ (★ ℓ) (`∀ (★ ι)
    (⌊ l ⌋ `→ (t `→ s) `→ Σ (l R▹ t) `→ s)))
    where
      l = tvar (S (S Z))
      t = tvar (S Z)
      s = tvar Z

case : ∀ {ℓ ℓΔ ℓΦ ℓΓ} {Δ : KEnv ℓΔ} {Φ : PEnv Δ ℓΦ}  {Γ : Env Δ ℓΓ} →
       Term Δ Φ Γ (caseT {ℓ})
case {ℓ} = `Λ (L lzero) (`Λ (★ ℓ) (`Λ (★ ℓ)
       (`λ ⌊ Ł ⌋ (`λ (T `→ O) (`λ (Σ (Ł R▹ T)) (f · ((Σ⁻¹ x) / l)))))))
  where
    Ł = tvar (S (S Z))
    T = tvar (S Z)
    O = tvar Z

    l = var (S (S Z))
    f = var (S Z)
    x = var Z

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
        (((((φ ·[ ρ ]) ·⟨ n-refl ⟩) · (Out v fmap)) · ((ti · φ) · fmap))))))))
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
                    ((tvar (Ty.S³ Z)  ↪ tvar Z) `→
                    (tvar (Ty.S² Z) ↪ tvar Z) `→
                    (tvar (Ty.S³ Z)  · tvar (Ty.S² Z) ~ tvar ((Ty.S Z))) ⇒
                    (tvar (S Z) ↪ tvar Z))))))

_▿μ_ {ℓ = ℓ} =
  `Λ R[ ★ ℓ `→ ★ ℓ ]
  (`Λ R[ ★ ℓ `→ ★ ℓ ]
  (`Λ R[ ★ ℓ `→ ★ ℓ ]
  (`Λ ((★ ℓ))
  (`λ (tvar (Ty.S³ Z) ↪ tvar Z)
  (`λ (tvar (Ty.S² Z) ↪ tvar Z)
  (`ƛ (tvar (Ty.S³ Z)  · tvar (Ty.S² Z) ~ tvar ((Ty.S Z)))
  (`Λ R[ ★ ℓ `→ ★ ℓ ]
  (`ƛ ((ρ₃ ≲ w))
  (`λ ((Σ ρ₃) ·[ μΣ w ])
  (`λ (μΣ w `→ τ)
  (((body · v') · r))))))))))))
  where
    ρ₁ = tvar (Ty.S⁴ Z)
    ρ₂ = tvar (Ty.S³ Z)
    ρ₃ = tvar (Ty.S² Z)
    τ = tvar (S Z)
    w = tvar Z
    v = var (S Z)
    v' = t-≡ teq-lift-Σ v
    r = var Z
    f' : Term _ _ _ (Σ (↑ ρ₁ ·[ (μΣ w) ]) `→ (μΣ w `→ τ) `→ τ)
    f' = `λ (Σ (↑ ρ₁ ·[ (μΣ w) ]))
         (`λ ((μΣ w `→ τ)) ((((var (S⁵ Z) ·[ w ]) ·⟨ n-trans (n-·≲L (n-var (S Z))) (n-var Z) ⟩) · t-≡ (teq-sym teq-lift-Σ) (var (S Z))) · var Z))
    g' : Term _ _ _ (Σ (↑ ρ₂ ·[ (μΣ w) ]) `→ (μΣ w `→ τ) `→ τ)
    g' = `λ (Σ (↑ ρ₂ ·[ (μΣ w) ]))
         (`λ ((μΣ w `→ τ)) ((((var (S⁴ Z) ·[ w ]) ·⟨ n-trans (n-·≲R (n-var (S Z))) (n-var Z) ⟩) · t-≡ (teq-sym teq-lift-Σ) (var (S Z))) · var Z))
    body : Term _ _ _ (Σ (↑ ρ₃ ·[ (μΣ w) ]) `→ (μΣ w `→ τ) `→ τ)
    body = (f' ▿ g') (n-·lift₁ (n-var (S Z)))

--------------------------------------------------------------------------------
-- Encoding the boolean type.

true : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → Term Δ Φ Γ (Bool {ℓ})
true = `Λ _ (`ƛ _ (inj (Σ ((lab Tru) ▹ (lab _))) (n-·≲L (n-var Z))))

false : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → Term Δ Φ Γ (Bool {ℓ})
false = `Λ _ (`ƛ _ (inj (Σ ((lab Fls) ▹ (lab _))) (n-·≲R (n-var Z))))

--------------------------------------------------------------------------------
-- idω : ★ → ★ at all levels.

idω : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ ((★ ℓ) `→ (★ ℓ))
idω {ℓ} = `λ (★ ℓ) (tvar Z)

--------------------------------------------------------------------------------
-- EqΣ.
-- ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →

Eq : Type Δ (★ ℓ `→ ★ (lsuc ℓ))
Eq = `λ _ ((tvar Z) `→ ((tvar Z) `→ K Bool))

eqΣT : Type Δ (★ (lsuc ℓ))
eqΣT {ℓ = ℓ} = `∀ R[ ★ ℓ ] (Π (((Eq ↑) ·[ tvar Z ])) `→ (Σ (tvar Z) `→ Σ (tvar Z) `→ Bool {ℓ}))

eqΣ : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → Term Δ Φ Γ (eqΣT {ℓ})
eqΣ {ℓ} = 
  `Λ R[ ★ ℓ ]                    -- z (TVar)
  (`λ (Π (((Eq ↑) ·[ tvar Z ]))) -- d (Var)
  (`λ (Σ (tvar Z))               -- v (Var)
  (`λ (Σ (tvar Z))               -- w (Var)
    ((ana (tvar Z) idω (Bool {ℓ}) 
      (`Λ (L lzero)              -- ℓ (TVar)
      (`Λ (★ ℓ)                  -- u (TVar)
      (`ƛ ((Ł₀ R▹ u₀) ≲ z₀) 
      (`λ ⌊ (tvar (S Z)) ⌋       --   l : ⌊ ℓ ⌋ (Var)
      (`λ ((K² idω ·[ (tvar Z) ])) -- y : u    (Var)
        (rowCompl 
          (n-var Z) body)))))) 
      · t-≡ (teq-Σ (teq-sym teq-id-↑)) (var Z)))))) 
      where
        z₀ = tvar (Ty.S² Z)
        Ł₀ = tvar (S Z)
        u₀ = tvar Z

        body : Term _ _ _ 
               (`∀ R[ ★ ℓ ]
                 ((tvar (Ty.S² Z) R▹ tvar (S Z)) · tvar Z ~ (tvar (Ty.S³ Z)) ⇒
                 Bool))
        body = `Λ (R[ ★ ℓ ]) -- Y (TVar)
               (`ƛ _         -- π 
               ((( lhs ▿ `λ _ false) π) · v))
          where
            υ = tvar (S Z)
            Ł = tvar (Ty.S² Z)
            v = var (S³ Z)
            π = n-var Z
            lhs : Term (_ ، R[ ★ ℓ ] ، L zero ، ★ ℓ ، R[ ★ ℓ ]) _ _ (Σ (Ł R▹ υ) `→ Bool {ℓ})
            lhs = `λ _      -- x (Var)
              ((((prj▹ d) pf) / l) · (Σ⁻¹ x / l) · y)
              where
--                Y = tvar Z
                z = tvar (Ty.S³ Z)
                x = var Z
                y = var (S Z) 
                l = var (S² Z)
                d = var (S⁵ Z)
                pf :  Ent _ _ ((Ł R▹ (υ `→ idω ·[ υ ] `→ Bool)) ≲ (Eq ↑) ·[ z ])
                pf = n-≡ 
                  (peq-≲ 
                    (teq-trans teq-lift₂ 
                    (teq-sing teq-refl 
                    (teq-trans teq-β 
                    (teq-→ teq-refl (teq-→ (teq-sym teq-β) teq-refl) )))) teq-refl) 
                    (n-≲lift₂ {ϕ = Eq} (n-var (S Z))) -- n-≡ (peq-≲ {!teq-lift₂!} {!!}) (n-var (S Z))

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
--              ((ρ₁ ≲ tvar Z) ⇒
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
-- --    (`ƛ (tvar (Ty.S³ Z) · (tvar Z) ~ (tvar (S Z)))
-- --    (`λ ((Σ (K² (tvar (S Z))) ·[ μΣ (tvar (S Z)) ])) -- v (Var)
-- --    (`λ ((μΣ (tvar (S Z)) `→ K² (μΣ (tvar Z))))     -- r (Var)
-- --        (In (t-≡
-- --          (inj {! !} {!!})
-- --          (teq-sym teq-lift-Σ))))))))))))

