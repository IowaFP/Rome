module Rome.Operational.Terms.Theorems.Progress where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna

open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Syntax

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Substitution
open import Rome.Operational.Terms.Normal.Reduction

open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Entailment.Properties

open import Effect.Monad.Identity

--------------------------------------------------------------------------------
-- Proof of progress

data Progress {τ} (M : NormalTerm Γ τ) : Set where
  Done : 
         Value M → 
         ----------
         Progress M

  Steps : 
          (M' : NormalTerm Γ τ) → (M —→ M') → 
          --------------------------------------
          Progress M



progress : ∀ {τ} (M : NormalTerm ∅ τ) → Progress M

-- progress (`λ M) = Done (V-λ M)
-- progress (M · N) = {!!}
-- progress (Λ M) = Done (V-Λ M)
-- progress (M ·[ τ ]) = {!!}
-- progress (In F M) = {!!}

-- progress (Out F M) with progress M 
-- progress (Out F M) | Done (V-In .F {N} VM) = Steps N β-In
-- progress (Out F M) | Done (V-fix N) = Steps (Out F (N · (fix N))) (ξ-Out (β-fix N)) 
-- progress (Out F M) | Steps M' step = Steps (Out F M') (ξ-Out step)

-- progress (fix M) = Steps (M · fix M) (β-fix M)

-- progress (`ƛ M) = Done (V-ƛ M)

-- progress (M ·⟨ n ⟩) = {!!}

-- progress (# ℓ) = Done V-#
-- progress (M Π▹ N) with progress N
-- progress (M Π▹ N) | Done VN = Done (V-Π M N VN)
-- progress (M Π▹ N) | Steps N' steps = Steps {!!} (ξ-Π▹ N N' M steps)
-- progress (M Π/ N) = {!!}

-- progress (prj M n) with progress M 
-- progress (prj M n) | Done (V-Π {υ = υ} ℓ M' VM') with norm₁ n 
-- ... | xs , _ , refl , refl = Done {!≲-inv n !}
-- progress (prj M n) | Done (V-⊹ M₁ N x x₁) = {!!}
-- progress (prj M n) | Done (V-Unit .M) = {!!}
-- progress (prj M n) | Done (V-fix M₁) = {!!}
-- progress (prj M n) | Done (V-syn ρ φ M₁) = {!!}
-- progress (prj M n) | Steps M' x = {!!}

-- progress ((M ⊹ N) n) = {!!}
-- progress (syn ρ φ M) = Done (V-syn ρ φ M)
-- progress (ana ρ φ τ M) = Done (V-ana ρ φ τ M)
-- progress (M Σ▹ N) = {!!}
-- progress (M Σ/ N) = {!!}
-- progress (inj M n) = {!!}
-- progress ((M ▿ N) n) = {!!}
-- progress (comp M n) = {!!}


-------------------------------------------------------------------------------
-- Tinkering

-- {-# TERMINATING #-}
-- eval : ∀ {τ} → NormalTerm ∅ τ → NormalTerm ∅ τ 
-- eval M with progress M 
-- ... | Done x = M
-- ... | Steps M' x = eval M'
   
-- _ : eval uu ≡ uu 
-- _ = refl
    
-- _ : eval ((♯l Π▹ # (lab "r")) Π/ ♯l) ≡ (# (lab "r"))
-- _ = refl

-- _ : eval (prj (♯l Π▹ ♯l) n-refl) ≡ ((♯l Π▹ ♯l))
-- _ = refl

-- _ : eval (`ƛ (prj (((♯l Π▹ uu) ⊹ (♯l Π▹ uu)) (n-var Z)) (n-·≲L (n-var Z)))) ≡ {! eval (`ƛ (prj (((♯l Π▹ uu) ⊹ (♯l Π▹ uu)) (n-var Z)) (n-·≲L (n-var Z))))  !}
-- _ = {!   !} 
   
-- _ : eval (((((Λ (Λ (`ƛ (`λ (prj {ρ₂ = ne ((` Z))} {ne (` (S Z))}  (` Z) (n-var (T Z))))))) ·[ lab "l" ▹ UnitNF ]) ·[ lab "l" ▹ UnitNF ]) ·⟨ n-refl ⟩) · (♯l Π▹ uu))   ≡ ((♯l Π▹ uu)) 
-- _ = refl
