
{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Theorems.Progress where

open import Rome.Operational.Prelude
open import Rome.Operational.Containment

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna

open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Syntax

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Substitution
open import Rome.Operational.Terms.Normal.Reduction

open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Entailment.Properties

open import Effect.Monad.Identity

--------------------------------------------------------------------------------
-- Proof of progress (Entailments)

data EntProgress {π : NormalPred Δ R[ κ ]} (M : NormalEnt Γ π) : Set where
  Done : 
         EntValue Γ π M → 
         ----------
         EntProgress M

  StepsTo_via_ : 
          (M' : NormalEnt Γ π) → (M =⇒ M') → 
          --------------------------------------
          EntProgress M

entProgress : ∀ {π : NormalPred ∅ R[ κ ]} (N : NormalEnt ∅ π) → EntProgress N
entProgress (n-incl i₁) = Done (n-incl i₁)
entProgress (n-plus i₁ i₂ i₃) = Done (n-plus i₁ i₂ i₃)
entProgress n@n-refl with norm-≲ n 
... | xs , oxs , ys , oys , refl , refl = StepsTo n-incl (λ x i → i) via δ-refl xs oxs
entProgress (_n-⨾_ M N) with entProgress M | entProgress N
... | Done (n-incl i₁) | Done (n-incl i₂) = StepsTo n-incl (⊆-trans i₁ i₂) via δ-trans i₁ i₂
... | Done V | StepsTo N' via N=⇒N' = StepsTo (_n-⨾_ M N') via ξ-trans₂ N=⇒N' 
... | StepsTo M' via M=⇒M' | Done _ = StepsTo (_n-⨾_ M' N) via ξ-trans₁ M=⇒M'
... | StepsTo M' via M=⇒M' | StepsTo _ via _ = StepsTo (_n-⨾_ M' N) via ξ-trans₁ M=⇒M'
entProgress (n-plusL≲ N) with entProgress N 
... | Done (n-plus i₁ i₂ i₃) = StepsTo n-incl i₁ via δ-·≲L i₁ i₂ i₃
... | StepsTo N' via N=⇒N' = StepsTo n-plusL≲ N' via ξ-·≲L N=⇒N'
entProgress (n-plusR≲ N) with entProgress N 
... | Done (n-plus i₁ i₂ i₃) = StepsTo n-incl i₂ via δ-·≲R i₁ i₂ i₃
... | StepsTo N' via N=⇒N' = StepsTo n-plusR≲ N' via ξ-·≲R N=⇒N'
entProgress n@n-empty≲ with norm-≲ n
... | xs , _ , ys , _ , refl , refl = StepsTo n-incl (λ { x () }) via {!!}
entProgress n@n-emptyR with norm-· n
... | xs , _ , ys , _ , zs , _ , refl , refl , refl = 
  StepsTo (n-plus(λ x i → i) (λ { x () }) λ x i → left i) via {!!} 
entProgress n@n-emptyL with norm-· n 
... | .[] , .tt , xs , _ , xs , _ , refl , refl , refl = StepsTo n-plus(λ { x () }) (λ x i → i) (λ x i → (right i)) via {!!}
entProgress n@(n-map≲ {F = F} N {x = ρ₁} {y = ρ₂} eq₁ eq₂) with entProgress N
... | StepsTo N' via N=⇒N' = StepsTo n-map≲ {F = F} N' eq₁ eq₂ via ξ-≲lift N N' eq₁ eq₂ N=⇒N'
entProgress (n-map≲ {F = F} N {_} {_} refl refl) | Done (n-incl {xs = xs} {ys = ys} i) = StepsTo n-incl (⊆-cong _ _ (sym ∘ stability-map F) i) via {!!}
entProgress (n-map· N eq₁ eq₂ eq₃) with entProgress N
... | StepsTo N' via N=⇒N' = StepsTo n-map· N' eq₁ eq₂ eq₃ via {!via ξ-·lift N N' !}
entProgress (n-complR-inert N) with norm-≲ N 
entProgress (n-complR-inert {nsr = ()} N) | xs , _ , ys , _ , refl , refl
entProgress (n-complR N) with entProgress N 
... | Done (n-incl i) = StepsTo n-plus i {!!} {!!} via {!!}
... | StepsTo N' via N=⇒N' = {!!}
entProgress (n-complL-inert N) with norm-≲ N 
entProgress (n-complL-inert {nsr = ()} N) | xs , _ , ys , _ , refl , refl
entProgress (n-complL N) = {!!}

--------------------------------------------------------------------------------
-- Proof of progress (Terms)

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
... | Done (V-In .F {M'} V) = StepsTo M' via δ-In
... | StepsTo M' via M→M' = StepsTo (Out F M') via (ξ-Out M→M')
progress (fix M) = StepsTo M · (fix M) via (δ-fix M)
progress (`ƛ M) = Done (V-ƛ M)
progress (M ·⟨ n ⟩) with progress M
... | Done (V-ƛ M') = StepsTo (M' βπ[ n ]) via β-ƛ
... | StepsTo M' via M→M' = StepsTo M' ·⟨ n ⟩ via ξ-·⟨⟩ M→M'
progress (# ℓ) = Done V-#
progress (_Π▹ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Π▹ N) with progress M 
... | Done (V-# {l = lab l}) = StepsTo ⟨ l ▹ N ⨾ ∅ ⟩ via δ-Π▹ N
... | StepsTo M' via M→M' = StepsTo (M' Π▹ N) via ξ-Π▹₁ N M M' M→M'
progress (_Π/ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Π/ ℓ) with progress M 
... | Done (V-Π (_ ▹ M' ⨾ ∅) (_ ▹ V ⨾ ∅)) = StepsTo M' via δ-Π/ M' ℓ 
... | StepsTo M' via M→M' = StepsTo M' Π/ ℓ via ξ-Π/₁ M M' ℓ M→M'
progress (prj M n) with progress M | entProgress n | norm-≲ n
... | StepsTo M' via M→M' | _ | _ = StepsTo prj M' n via ξ-prj M M' n M→M'
... | _ | StepsTo n' via n=⇒n' | _ = StepsTo (prj M n') via {!!}
progress (prj M n) | Done (V-Π r rV) | Done (n-incl {xs = xs} {oxs = oxs} {oys} i) | _ = StepsTo ⟨ project {oxs = oxs} {oys = oys} r i ⟩ via (δ-prj r i)

--  xs , oxs , ys , oys , refl , refl with ≲-inv n 
-- ... | i = StepsTo ⟨ project r i ⟩ via {!δ-prj r i!}

progress ((M₁ ⊹ M₂) x₁) = {!!} -- with norm-· x₁ 
-- ... | xs , _ , ys , _ , zs , _ , refl , refl , refl with progress M₁ | progress M₂ 
-- ... | Done (V-Π r x₂) | Done (V-Π r₁ x₃) with ·-inv x₁ 
-- ... | c = {!c .snd .snd!}
progress (syn ρ φ M) = {!!}
progress (ana ρ φ τ M) = {!!}
progress (_Σ▹ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Σ▹ N) with progress M 
... | Done (V-# {l = lab l}) = StepsTo (⟨ l ▹ N ⟩via (here refl)) via δ-Σ▹ N
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
-- progress (Out F M) | Done (V-In .F {N} VM) = Steps N δ-In
-- progress (Out F M) | Done (V-fix N) = Steps (Out F (N · (fix N))) (ξ-Out (δ-fix N)) 
-- progress (Out F M) | Steps M' step = Steps (Out F M') (ξ-Out step)

-- progress (fix M) = Steps (M · fix M) (δ-fix M)

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

-- _ : eval (`ƛ (prj (((♯l Π▹ uu) ⊹ (♯l Π▹ uu)) (n-var Z)) (n-plusL≲ (n-var Z)))) ≡ {! eval (`ƛ (prj (((♯l Π▹ uu) ⊹ (♯l Π▹ uu)) (n-var Z)) (n-plusL≲ (n-var Z))))  !}
-- _ = {!   !} 
   
-- _ : eval (((((Λ (Λ (`ƛ (`λ (prj {ρ₂ = ne ((` Z))} {ne (` (S Z))}  (` Z) (n-var (T Z))))))) ·[ lab "l" ▹ UnitNF ]) ·[ lab "l" ▹ UnitNF ]) ·⟨ n-refl ⟩) · (♯l Π▹ uu))   ≡ ((♯l Π▹ uu)) 
-- _ = refl
