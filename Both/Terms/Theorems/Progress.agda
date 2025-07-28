{-# OPTIONS --safe #-}
module Rome.Both.Terms.Theorems.Progress where

open import Rome.Both.Prelude
open import Rome.Both.Containment

open import Rome.Both.Kinds.Syntax

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.SynAna
open import Rome.Both.Types.Properties.Substitution

open import Rome.Both.Types.Semantic.NBE
open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Properties.Renaming
open import Rome.Both.Types.Normal.Properties.Substitution

open import Rome.Both.Types.Equivalence.Relation
open import Rome.Both.Types.Equivalence.Properties

open import Rome.Both.Types.Theorems.Completeness
open import Rome.Both.Types.Theorems.Stability
open import Rome.Both.Types.Theorems.Soundness


open import Rome.Both.Terms.Normal.Syntax
open import Rome.Both.Terms.Normal.Substitution
open import Rome.Both.Terms.Normal.Reduction

open import Rome.Both.Kinds.GVars

open import Rome.Both.Terms.Normal.GVars
open import Rome.Both.Terms.Normal.Renaming
open import Rome.Both.Terms.Normal.Entailment.Properties
open import Rome.Both.Terms.Normal.SynAna

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
... | xs , oxs , ys , oys , refl , refl = StepsTo (n-incl (λ x i → i)) via δ-refl xs oxs
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
entProgress n@n-emptyR with norm-· n
... | xs , _ , ys , _ , zs , _ , refl , refl , refl = 
  StepsTo _ via δ-emptyR 
entProgress n@n-emptyL with norm-· n 
... | .[] , .tt , xs , _ , xs , _ , refl , refl , refl = 
  StepsTo _ via δ-emptyL
entProgress n@(n-map≲ {F = F} N {x = ρ₁} {y = ρ₂} eq₁ eq₂) with entProgress N
... | StepsTo N' via N=⇒N' = StepsTo n-map≲ {F = F} N' eq₁ eq₂ via ξ-map≲ N N' eq₁ eq₂ N=⇒N'
entProgress (n-map≲ {F = F} N {_} {_} refl refl) | Done (n-incl {xs = xs} {ys = ys} i) = 
  StepsTo n-incl ((⊆-cong _ _ (sym ∘ stability-map F) i)) via δ-map≲ i 
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

data RecordProgress {xs} (r : Record Γ xs) : Set where
  Done : 
         RecordValue Γ xs r → 
         ----------
         RecordProgress r

  StepsTo_via_ : ∀ 
                   (r' : Record Γ xs) → (r —→ᵣ r') → 
                 --------------------------------------
                 RecordProgress r

--------------------------------------------------------------------------------
-- Statement of progress for terms and records
       
progress : ∀ {τ} (M : NormalTerm ∅ τ) → Progress M
recordProgress : ∀ {xs} → 
                   (M : Record ∅ xs) → RecordProgress M 

--------------------------------------------------------------------------------
-- Proof of record progress

recordProgress ∅ = Done ∅
recordProgress (_▹_⨾_ {xs = xs} l M r) with progress M | recordProgress r 
... | Done V | Done rV = Done (l ▹ V ⨾ rV)
... | StepsTo M' via M—→M' | Done x₂ = StepsTo (l ▹ M' ⨾ r) via ξ-record₂ M—→M'
... | Done V | StepsTo r' via r—→r' = StepsTo l ▹ M ⨾ r' via ξ-record₁ r—→r'
... | StepsTo M' via x₁ | StepsTo r' via x₂ = StepsTo l ▹ M ⨾ r' via ξ-record₁ x₂

--------------------------------------------------------------------------------
-- Proof of term progress 

progress (`λ M) = Done (V-λ M)
progress (M₁ · M₂) with progress M₁ | progress M₂  
progress (M₁ · M₂) | StepsTo M₃ via M₁→M₃ | _ = StepsTo (M₃ · M₂) via (ξ-·1 M₁→M₃)
progress (M₁ · M₂) | Done (V-λ M) | _ = StepsTo (M β[ M₂ ]) via β-λ
progress (M₁ · M₂) | Done (V-▿ F G vF vG) | StepsTo M₂' via M₂—→M₂' = StepsTo (F ▿ G) _ · M₂' via ξ-·2 M₂—→M₂'
progress (M₁ · M₂) | Done (V-▿ {e = e} F G vF vG) | Done (V-Σ {τ = τ} l {M} vM i) with entProgress e 
... | StepsTo e' via e=⇒e' = StepsTo (F ▿ G) e' · (⟨ l ▹ M ⟩via i) via
                               ξ-·1 (ξ-▿₃ F G e e' e=⇒e')
... | Done (n-plus {xs = xs} {ys} {zs} i₁ i₂ i₃) with i₃ (l , τ) i 
... | left inxs = StepsTo (F · (⟨ l ▹ M ⟩via inxs)) via δ-▿₁ F G e M i inxs
... | right inys = StepsTo (G · (⟨ l ▹ M ⟩via inys)) via δ-▿₂ F G e M i inys 
progress (M₁ · M₂) | Done (V-ana ρ φ τ eq₁ eq₂ M vM) | StepsTo M₂' via M₂—→M₂' = StepsTo ana ρ φ τ eq₁ eq₂ M · M₂' via ξ-·2 M₂—→M₂' 
progress (M₁ · M₂) | Done (V-ana ρ φ t {τ₁} {τ₂} eq₁@refl eq₂ M VM) | Done V@(V-Σ {φυ} {oxs = oxs'} l {N} V' i) with 
      row-canonicity-∅ ρ
... | xs , oxs , refl with inj-⦅⦆ 
                           {wf₂ = fromWitness (normal-map-map₂ xs (φ ·'_) (toWitness oxs))} 
                           (inj-Σ (trans (sym eq₂) (cong Σ (cong-⦅⦆ (sym (stability-map φ xs))))))
... |  refl =
  StepsTo 
    anaVariant φ xs t oxs oxs'  M _ V  via 
    δ-ana {xs = xs} φ t φυ eq₂ M l N V' i     

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
... | _ | StepsTo n' via n=⇒n' | _ = StepsTo (prj M n') via ξ-prj⇒ M n n' n=⇒n'
progress (prj M n) | Done (V-Π r rV) | Done (n-incl {xs = xs} {oxs = oxs} {oys} i) | _ = 
  StepsTo ⟨ project {oxs = oxs} {oys = oys} r i ⟩ via (δ-prj r i)
progress ((M₁ ⊹ M₂) n) with progress M₁ | progress M₂ | entProgress n 
... | StepsTo M₁' via M₁—→M₁' | _ | _ = StepsTo (M₁' ⊹ M₂) n via ξ-⊹₁ M₁ M₁' M₂ n M₁—→M₁'
... | _ | StepsTo M₂' via M₂—→M₂' | _ = StepsTo (M₁ ⊹ M₂') n via ξ-⊹₂ M₁ M₂ M₂' n M₂—→M₂' 
... | _ | _ | StepsTo n' via n=⇒n' = StepsTo (M₁ ⊹ M₂) n' via ξ-⊹₃ M₁ M₂ n n' n=⇒n'
... | Done (V-Π {xs} r₁ Vr₁) | Done (V-Π {ys} r₂ Vr₂) | Done (n-plus i₁ i₂ i₃) = StepsTo ⟨ concatRec r₁ r₂ i₃ ⟩ via δ-⊹ r₁ r₂ i₁ i₂ i₃
progress (syn ρ φ M) with progress M | row-canonicity-∅ ρ
... | Done V | xs , oxs , refl = 
  let eq-mapOver = (cong Π (cong-⦅⦆ 
                   {wf₁ = fromWitness (normal-map-map₂ xs (φ ·'_) (toWitness oxs))} 
                   (stability-map φ xs))) in
  StepsTo 
    (conv eq-mapOver ⟨ synRecord φ xs oxs M ⟩) via δ-syn φ eq-mapOver M
... | StepsTo M' via M—→M' | _ = StepsTo syn ρ φ M' via ξ-Syn ρ φ M M' M—→M'
progress (ana ρ φ τ eq₁ eq₂ M) with progress M 
... | Done V = Done (V-ana ρ φ τ eq₁ eq₂ M V)
... | StepsTo M' via M—→M' = StepsTo ana ρ φ τ eq₁ eq₂ M' via ξ-Ana ρ φ τ eq₁ eq₂ M M' M—→M'
progress (_Σ▹ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Σ▹ N) with progress M 
... | Done (V-# {l = lab l}) = StepsTo (⟨ l ▹ N ⟩via (here refl)) via δ-Σ▹ N
... | StepsTo M' via M→M' = StepsTo (M' Σ▹ N) via ξ-Σ▹₁ N M M' M→M'
progress (_Σ/ne_ {l} M M₁) = ⊥-elim (noNeutrals l)
progress (M Σ/ ℓ) with progress M 
... | Done (V-Σ l {M'} V (here refl)) = StepsTo M' via (δ-Σ/ M' ℓ)
... | StepsTo M' via M→M' = StepsTo M' Σ/ ℓ via ξ-Σ/₁ M M' ℓ M→M'
progress (inj M n) with progress M | entProgress n 
... | StepsTo M' via M—→M' | _  = StepsTo (inj M' n) via (ξ-inj M M' n M—→M')
... | Done V  | StepsTo n' via n—→n'  = StepsTo inj M n' via ξ-inj⇒ M n n' n—→n'
... | Done (V-Σ l {M'} V i) | Done (n-incl i₁) = StepsTo (⟨ l ▹ M' ⟩via i₁ (l , _) i) via δ-inj l M' i₁ i
progress ((M₁ ▿ M₂) n) with progress M₁ | progress M₂ | entProgress n 
... | StepsTo M₁' via M₁—→M₁' | _ | _ = StepsTo (M₁' ▿ M₂) n via ξ-▿₁ M₁ M₁' M₂ n M₁—→M₁'
... | _ | StepsTo M₂' via M₂—→M₂' | _ = StepsTo (M₁ ▿ M₂') n via ξ-▿₂ M₁ M₂ M₂' n M₂—→M₂'
... | _ | _ | StepsTo n' via n=⇒n' = StepsTo (M₁ ▿ M₂) n' via ξ-▿₃ M₁ M₂ n n' n=⇒n'
... | Done V₁ | Done V₂ | Done Vn = Done (V-▿ M₁ M₂ V₁ V₂)
progress ⟨ r ⟩ with recordProgress r 
... | Done V = Done (V-Π r V)
... | StepsTo r' via r—→r' = StepsTo ⟨ r' ⟩ via ξ-⟨⟩ r—→r'
progress (⟨_▹_⟩via_ {xs = xs} {oxs} l M i) with progress M 
... | Done V = Done (V-Σ l V i)
... | StepsTo M' via M→M' = StepsTo (⟨ l ▹ M' ⟩via i) via ξ-Σ M M' i M→M'
