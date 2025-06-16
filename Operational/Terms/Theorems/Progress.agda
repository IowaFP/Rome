{-# OPTIONS --safe #-}
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

  StepsTo_via_ : 
          (M' : NormalTerm Γ τ) → (M —→ M') → 
          --------------------------------------
          Progress M



progress : ∀ {τ} (M : NormalTerm ∅ τ) → Progress M
progress (`λ M) = Done (V-λ M)
progress (M₁ · M₂) with progress M₁ 
... | Done (V-λ M) = StepsTo (M β[ M₂ ]) via β-λ
... | StepsTo M₃ via M₁→M₃ = StepsTo (M₃ · M₂) via (ξ-·1 M₁→M₃)
progress (Λ M) = Done (V-Λ M)
progress (M ·[ τ ]) with progress M 
... | Done (V-Λ M₁) = StepsTo (M₁ β·[ τ ]) via β-Λ
... | StepsTo M' via M→M' = StepsTo (M' ·[ τ ]) via (ξ-·[] M→M')
progress (In F M) with progress M 
... | Done V = Done (V-In F V)
... | StepsTo M' via M→M' = StepsTo (In F M') via (ξ-In M→M')
progress (Out F M) with progress M 
... | Done (V-In .F {M'} V) = StepsTo M' via β-In
... | StepsTo M' via M→M' = StepsTo (Out F M') via (ξ-Out M→M')
progress (fix M) = StepsTo M · (fix M) via (β-fix M)
progress (`ƛ M) = Done (V-ƛ M)
progress (M ·⟨ n ⟩) with progress M
... | Done (V-ƛ M') = StepsTo (M' βπ[ n ]) via β-ƛ
... | StepsTo M' via M→M' = StepsTo M' ·⟨ n ⟩ via ξ-·⟨⟩ M→M'
progress (# ℓ) = Done V-#
progress (_Π▹ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Π▹ N) with progress M 
... | Done (V-# {l = lab l}) = StepsTo ⟨ l ▹ N ⨾ ∅ ⟩ via β-Π▹ N
... | StepsTo M' via M→M' = StepsTo (M' Π▹ N) via ξ-Π▹₁ N M M' M→M'
progress (_Π/ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Π/ ℓ) with progress M 
... | Done (V-Π (_ ▹ M' ⨾ ∅) (_ ▹ V ⨾ ∅)) = StepsTo M' via {!!} 
... | StepsTo M' via M→M' = {!!}
progress (prj M x₁) = {!!}
progress ((M₁ ⊹ M₂) x₁) = {!!} -- with norm-· x₁ 
-- ... | xs , _ , ys , _ , zs , _ , refl , refl , refl with progress M₁ | progress M₂ 
-- ... | Done (V-Π r x₂) | Done (V-Π r₁ x₃) with ·-inv x₁ 
-- ... | c = {!c .snd .snd!}
progress (syn ρ φ M) = {!!}
progress (ana ρ φ τ M) = {!!}
progress (_Σ▹ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Σ▹ N) with progress M 
... | Done (V-# {l = lab l}) = StepsTo (⟨ l ▹ N ⟩via (here refl)) via β-Σ▹ N
... | StepsTo M' via M→M' = StepsTo (M' Σ▹ N) via ξ-Σ▹₁ N M M' M→M'
progress (_Σ/ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Σ/ ℓ) = {!!}
progress (inj M x₁) = {!!}
progress ((M ▿ M₁) x₁) = {!!}
progress ⟨ x₁ ⟩ = {!!}
progress (⟨ l ▹ M ⟩via i) with progress M 
... | Done V = Done (V-Σ l V i)
... | StepsTo M' via M→M' = {!!}
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
