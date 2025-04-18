module Rome.Operational.Terms.Theorems.Progress where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Substitution
open import Rome.Operational.Terms.Normal.Reduction

open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Entailment.Properties

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

progress (`λ M) = Done (V-λ M)

progress (M · N) with progress M | progress N 
... | Done (V-λ _)         | _  = Steps _ β-λ
... | Steps M' s           | n = Steps (M' · N) (ξ-·1 s)
... | Done (V-▿ m n x x₁)  | Steps M' x₂ = {!   !}
progress (M · N) | Done (V-▿ {e = e} m n VM VN) | Done (V-Σ ℓ o VO) with singleton-sum e 
... | left refl = Steps (m · (ℓ Σ▹ o)) {!   !}
... | right eq = {!   !}

progress (Λ M) = Done (V-Λ M)

progress (c ·[ τ₁ ]) = {!   !}
progress (In F c) = {!   !}
progress (Out F c) = {!   !}
progress (`ƛ c) = {!   !}
progress (c ·⟨ x ⟩) = {!   !}
progress (# l) = Done V-#
progress (c Π▹ c₁) = {!   !}
progress (c Π/ c₁) = {!   !}
progress (prj c x) = {!   !}
progress ((c ⊹ c₁) x) = {!   !}
progress (c Σ▹ c₁) = {!   !}
progress (c Σ/ c₁) = {!   !}
progress (inj c x) = {!   !}
progress ((c ▿ c₁) x) = {!   !} 


--------------------------------------------------------------------------------
-- (Old) Proof of progress

-- progress (`λ M) = Done (V-λ M)
-- progress (Λ M) = Done (V-Λ M)
-- progress (M · N) with progress M
-- progress (.(`λ M) · N) | Done (V-λ M)   = Steps (M β[ N ]) β-λ
-- progress (M · N)       | Steps M' steps = Steps (M' · N) (ξ-·1 steps)

-- progress (M ·[ τ ]) with progress M
-- ... | c = ?
-- progress (.(Λ _) ·[ τ ]) | Done (V-Λ M) = Steps _ β-Λ
-- progress (M ·[ τ ])      | Steps M' steps = Steps _ (ξ-·[] steps)

-- progress (In τ M) with progress M 
-- ... | Done V         = Done (V-In τ V) 
-- ... | Steps M' steps = Steps (In τ M') (ξ-In steps) 

-- progress (Out τ M) with progress M
-- progress (Out τ .(In τ _)) | Done (V-In F M) = Steps _ β-In
-- progress (Out τ M)           | Steps M' steps = Steps _ (ξ-Out steps)

-- progress (`ƛ M) = Done (V-ƛ M)

-- progress (M ·⟨ e ⟩) with progress M 
-- ... | Done (V-ƛ M₁) = Steps (M₁ βπ[ e ]) β-ƛ
-- ... | Steps M' x = Steps (M' ·⟨ e ⟩) (ξ-·⟨⟩ x)

-- progress (# l) = Done V-#
-- progress (ℓ Π▹ M) with progress M 
-- ... | Done VM = Done (V-Π ℓ M VM)
-- ... | Steps M' M—→M' = Steps (ℓ Π▹ M') (ξ-Π▹ M M' ℓ M—→M')

-- progress (_Π/_ {l} M ℓ) with progress M
-- ... | Done (V-Π ℓ₁ N VN)  = Steps N (β-Π/ N ℓ₁ ℓ VN)
-- ... | Steps M' M—→M' = Steps (M' Π/ ℓ) (ξ-Π/ M M' ℓ M—→M')
-- ... | Done (V-⊹ {e = e} N₁ N₂ v₁ v₂) with no-meaningful-combinations e
-- progress (_Π/_ {l} M ℓ) | Done (V-⊹ {e = e} E N vE v) | left refl with ε-left-identity e 
-- ... | refl = Steps (N Π/ ℓ) (ξ-Π/ M N ℓ (β-Πε-left E N e v))
-- progress (_Π/_ {l} M ℓ) | Done (V-⊹ {e = e} N E v vE) | right refl with ε-right-identity e
-- ... | refl  = Steps (N Π/ ℓ) (ξ-Π/ M N ℓ (β-Πε-right N E e v))

-- progress (prj {ρ₁ = ne x} M e₁) = ⊥-elim (noNeutrals x)
-- progress (prj {ρ₁ = ε} M e) = Done (V-Unit (prj M e))
-- progress (prj {ρ₁ = l₂ ▹ τ} M e₁) with progress M
-- progress (prj {ne x} {.(_ ▹ _)} _ e) | Done v = ⊥-elim (noNeutrals x)
-- progress (prj {ε} {.(_ ▹ _)} _ e) | Done v with ε-minimum e 
-- ... | ()
-- progress (prj {ρ₂ ▹ ρ₃} {.(_ ▹ _)} _ e) | Done v with ≲-refl e 
-- progress (prj {ρ₂ ▹ ρ₃} {.(_ ▹ _)} M e) | Done v | refl = Steps M (β-prj M e v)
-- progress (prj M e) | Steps M' x = Steps _ (ξ-prj M M' e  x)

-- progress ((M ⊹ N) e) with progress M | progress N 
-- ... | Steps M' m | d = Steps ((M' ⊹ N) e) (ξ-⊹₁ M M' N e m)
-- ... | _ | Steps N' n = Steps ((M ⊹ N') e) (ξ-⊹₂ M N N' e n)
-- ... | Done v₁ | Done v₂ = Done (V-⊹ M N v₁ v₂)

-- progress (ℓ Σ▹ M) with progress M 
-- ... | Done VM = Done (V-Σ ℓ M VM)
-- ... | Steps M' M—→M' = Steps (ℓ Σ▹ M') (ξ-Σ▹ M M' ℓ M—→M')

-- progress (_Σ/_ {l} M ℓ) with progress M
-- ... | Done (V-Σ ℓ₁ N VN)  = Steps N (β-Σ/ N ℓ₁ ℓ VN)
-- ... | Steps M' M—→M' = Steps (M' Σ/ ℓ) (ξ-Σ/ M M' ℓ M—→M')

-- progress (inj M e) with progress M 
-- progress (inj {ρ₂ = ne x₁} M e) | Done (V-Σ ℓ M₁ x) = ⊥-elim (noNeutrals x₁)
-- progress (inj {ρ₂ = ε} M e) | Done (V-Σ ℓ M₁ x) with ε-minimum e
-- progress (inj {ρ₂ = ε} M e) | Done (V-Σ ℓ M₁ x) | () 
-- progress (inj {ρ₂ = ρ₂ ▹ ρ₃} M e) | Done v@(V-Σ ℓ M₁ x) with ≲-refl e 
-- ... | refl = Steps M (β-inj M e v)
-- progress (inj {ρ₂ = ρ₂} M e) | Steps M' x = Steps (inj M' e) (ξ-inj M M' e x)

-- progress ((f ▿ g) e) with progress f | progress g 
-- ... | Steps f' s | _ = Steps ((f' ▿ g) e) (ξ-▿₁ f f' g e s)
-- ... | _ | Steps g' s = Steps ((f ▿ g') e) (ξ-▿₂ f g g' e s)
-- ... | Done v₁ | Done v₂ = Done (V-▿ f g v₁ v₂)

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
