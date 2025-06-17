
{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Theorems.Progress where

open import Rome.Operational.Prelude
open import Rome.Operational.Containment

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.SynAna

open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
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
... | Done (n-incl i₁) | Done (n-incl i₂) = StepsTo n-incl (⊆-trans i₁ i₂) via δ-⨾ i₁ i₂
... | Done V | StepsTo N' via N=⇒N' = StepsTo (_n-⨾_ M N') via ξ-⨾₂ N=⇒N' 
... | StepsTo M' via M=⇒M' | Done _ = StepsTo (_n-⨾_ M' N) via ξ-⨾₁ M=⇒M'
... | StepsTo M' via M=⇒M' | StepsTo _ via _ = StepsTo (_n-⨾_ M' N) via ξ-⨾₁ M=⇒M'
entProgress (n-plusL≲ N) with entProgress N 
... | Done (n-plus i₁ i₂ i₃) = StepsTo n-incl i₁ via δ-plusL≲ i₁ i₂ i₃
... | StepsTo N' via N=⇒N' = StepsTo n-plusL≲ N' via ξ-plusL≲ N=⇒N'
entProgress (n-plusR≲ N) with entProgress N 
... | Done (n-plus i₁ i₂ i₃) = StepsTo n-incl i₂ via δ-plusR≲ i₁ i₂ i₃
... | StepsTo N' via N=⇒N' = StepsTo n-plusR≲ N' via ξ-plusR≲ N=⇒N'
entProgress n@n-empty≲ with norm-≲ n
... | xs , _ , ys , _ , refl , refl = StepsTo _ via δ-empty≲
entProgress n@n-emptyR with norm-· n
... | xs , _ , ys , _ , zs , _ , refl , refl , refl = 
  StepsTo _ via δ-emptyR 
entProgress n@n-emptyL with norm-· n 
... | .[] , .tt , xs , _ , xs , _ , refl , refl , refl = 
  StepsTo _ via δ-emptyL
entProgress n@(n-map≲ {F = F} N {x = ρ₁} {y = ρ₂} eq₁ eq₂) with entProgress N
... | StepsTo N' via N=⇒N' = StepsTo n-map≲ {F = F} N' eq₁ eq₂ via ξ-map≲ N N' eq₁ eq₂ N=⇒N'
entProgress (n-map≲ {F = F} N {_} {_} refl refl) | Done (n-incl {xs = xs} {ys = ys} i) = 
  StepsTo n-incl (⊆-cong _ _ (sym ∘ stability-map F) i) via δ-map≲ i 
entProgress (n-map· N eq₁ eq₂ eq₃) with entProgress N
entProgress (n-map· {F = F} N refl refl refl) | Done (n-plus i₁ i₂ i₃) = StepsTo 
  n-plus (⊆-cong _ _ (sym ∘ stability-map F) i₁) 
         (⊆-cong _ _ (sym ∘ stability-map F) i₂) 
         (⊆-cong-or _ _ (sym ∘ stability-map F) i₃) 
  via δ-map· i₁ i₂ i₃
entProgress (n-map· {F = F} N eq₁ eq₂ eq₃) |
  StepsTo N' via N=⇒N' = StepsTo n-map· {F = F} N' eq₁ eq₂ eq₃ via ξ-map· N N' eq₁ eq₂ eq₃ N=⇒N' 
entProgress (n-complR-inert N) with norm-≲ N 
entProgress (n-complR-inert {nsr = ()} N) | xs , _ , ys , _ , refl , refl
entProgress (n-complR N) with entProgress N 
... | Done (n-incl {xs = xs} {ys = ys} {oxs = oxs} {oys} i) = 
  StepsTo n-plus i (⇓Row-⇑Row-─s-mono xs ys) (⇓Row-⇑Row-─s-mono-orᵣ xs ys {toWitness oys} i) 
  via δ-complR i
... | StepsTo N' via N=⇒N' = StepsTo (n-complR N') via ξ-complR N N' N=⇒N'
entProgress (n-complL-inert N) with norm-≲ N 
entProgress (n-complL-inert {nsr = ()} N) | xs , _ , ys , _ , refl , refl
entProgress (n-complL N) with entProgress N 
... | Done (n-incl {xs = xs} {ys = ys} {oxs = oxs} {oys} i) = 
  StepsTo (n-plus (⇓Row-⇑Row-─s-mono xs ys) i (⇓Row-⇑Row-─s-mono-orₗ xs ys {toWitness oys} i)) via δ-complL i
... | StepsTo N' via N=⇒N' = StepsTo (n-complL N') via ξ-complL N N' N=⇒N'

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
progress (M₁ · M₂) with progress M₁ | progress M₂  
... | StepsTo M₃ via M₁→M₃ | _ = StepsTo (M₃ · M₂) via (ξ-·1 M₁→M₃)
... | Done (V-λ M) | _ = StepsTo (M β[ M₂ ]) via β-λ
... | Done (V-ana ρ φ τ eq₁ eq₂ M vM) | StepsTo M₂' via M₂—→M₂' = StepsTo ana ρ φ τ eq₁ eq₂ M · M₂' via ξ-·2 M₂—→M₂' 
progress (M₁ · M₂) | Done (V-ana (ne x₁) φ τ {τ₁} {τ₂} refl eq₂ M vM) | Done (V-Σ {τ₃} l {M₃} V₂ i) = ⊥-elim (noNeutrals x₁)
-- N.b. we only need to show stability-<$>' for ⦅⦆ case.
-- No matter what, we need to show that xs = map (overᵣ blah) ρ and that if l ∈ xs then l ∈ map .
-- We can use (subst (λ x → (l , τ₃) ∈ x) eq i) to grab an index of (map (overᵣ (φ ·'_)) ρ) which should
-- (in theory) give us an index in ρ, which will give us a type with kind κ. May need to write write an inversion
-- that takes (l , τ₃) ∈ (map f ρ) and yields an (l , τ₃') ∈ ρ s.t. τ₃ = f τ₃'.
progress (M₁ · M₂) | Done (V-ana (⦅ ρ ⦆ oρ) φ τ {τ₁} {τ₂} refl eq₂@refl M vM) | Done (V-Σ {τ₃} l {M₃} V₂ i) with  inj-⦅⦆ (inj-Σ (trans (sym eq₂) (cong Σ (cong-⦅⦆ (sym (stability-map φ ρ))))))
... | eq =  StepsTo (conv {!eq!} (M ·[ lab l ] ·[ {!subst (λ x → (l , τ₃) ∈ x) eq i!} ] ·⟨ {!!} ⟩ · # (lab l) · {!M₃!})) via {!!}
progress (M₁ · M₂) | Done (V-ana ((ρ ─ ρ₁) {nsr}) φ τ {τ₁} {τ₂} refl eq₂ M vM) | Done (V-Σ {τ₃} l {M₃} V₂ i) = ⊥-elim (noComplements nsr refl)
progress (M₁ · M₂) | Done (V-ana (l₁ ▹ₙ ρ) φ τ {τ₁} {τ₂} refl eq₂ M vM) | Done (V-Σ {τ₃} l {M₃} V₂ i) = ⊥-elim (noNeutrals l₁)
-- 

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
progress (prj M n) | Done (V-Π r rV) | Done (n-incl {xs = xs} {oxs = oxs} {oys} i) | _ = 
  StepsTo ⟨ project {oxs = oxs} {oys = oys} r i ⟩ via (δ-prj r i)

--  xs , oxs , ys , oys , refl , refl with ≲-inv n 
-- ... | i = StepsTo ⟨ project r i ⟩ via {!δ-prj r i!}

progress ((M₁ ⊹ M₂) x₁) = {!!} -- with norm-· x₁ 
-- ... | xs , _ , ys , _ , zs , _ , refl , refl , refl with progress M₁ | progress M₂ 
-- ... | Done (V-Π r x₂) | Done (V-Π r₁ x₃) with ·-inv x₁ 
-- ... | c = {!c .snd .snd!}
progress (syn ρ φ M) = {!!}
progress (ana ρ φ τ eq₁ eq₂ M) = {!!}
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
