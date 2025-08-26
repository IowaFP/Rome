module Rome.Both.Terms.Denotation where 

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars
open import Rome.Both.Kinds.Denotation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Denotation
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Substitution

open import Rome.Both.Terms.Syntax

open import Rome.Both.IndexCalculus.Records renaming (Π to Pi)
open import Rome.Both.IndexCalculus.Variants renaming (Σ to Sigma)
open import Rome.Both.IndexCalculus.Rows


--------------------------------------------------------------------------------
-- Denoting environments 

⟦_⟧e : ∀ {Δ : KEnv ιΔ} → Env Δ ιΓ → ⟦ Δ ⟧ke → Set ιΓ
⟦ ∅ ⟧e H = ⊤'
⟦ Γ ,   τ ⟧e H = (⟦ Γ ⟧e H) × (⟦ τ ⟧nf H)
⟦ Γ ,,  κ ⟧e (H , ⟦κ⟧) = ⟦ Γ ⟧e H × ⟦ κ ⟧k
⟦ Γ ,,, π ⟧e H = ⟦ Γ ⟧e H × ⟦ π ⟧p H 

weaken⟦⟧ : ∀ {τ : NormalType Δ (★ {ι})} {H : ⟦ Δ ⟧ke} {κ : Kind ικ} {k : ⟦ κ ⟧k} → 
             ⟦ τ ⟧nf H → ⟦ weakenₖNF τ  ⟧nf (H , k)
weaken⟦⟧ {τ = ne x} {H} {κ} {k} ⟦τ⟧ = {!   !}
weaken⟦⟧ {τ = τ `→ τ₁} {H} {κ} {k} ⟦τ⟧ = {!   !}
weaken⟦⟧ {τ = `∀ τ} {H} {κ} {k} ⟦τ⟧ = {!   !}
weaken⟦⟧ {τ = π ⇒ τ} {H} {κ} {k} ⟦τ⟧ = {!   !}
weaken⟦⟧ {τ = ⌊ τ ⌋} {H} {κ} {k} ⟦τ⟧ = {!   !}
weaken⟦⟧ {τ = Π τ} {H} {κ} {k} ⟦τ⟧ = {!   !}
weaken⟦⟧ {τ = Σ τ} {H} {κ} {k} ⟦τ⟧ = {!   !}

⟦_⟧v : ∀ {Δ : KEnv ιΔ} {Γ : Env Δ ιΓ} {τ : NormalType Δ (★ {ι})} → 
         Var Γ τ → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → ⟦ τ ⟧nf H
⟦ Z ⟧v H (_ , ⟦τ⟧) = ⟦τ⟧
⟦ S v ⟧v H (η , _) = ⟦ v ⟧v H η
⟦_⟧v {Δ = Δ} (K {τ = τ} v) (H , _) (η , k) = {!   !} -- weaken⟦⟧ {Δ = Δ} {H = H , _} {k = k} (⟦ v ⟧v H η)
⟦ P v ⟧v H (η , _) = ⟦ v ⟧v H η


--------------------------------------------------------------------------------
-- Denoting entailments 

⟦_⟧n : ∀ {π : NormalPred Δ R[ κ ]} {Γ : Env Δ ιΓ} → Ent Γ π → 
        (H : ⟦ Δ ⟧ke) → (η : ⟦ Γ ⟧e H) → 
        ⟦ π ⟧p H 
⟦ n-var x ⟧n H η = {!   !}
⟦ n-incl x ⟧n H η = {!   !}
⟦ n-plus x x₁ x₂ ⟧n H η = {!   !}
⟦ n-refl ⟧n H η = {!   !}
⟦ e n-⨾ e₁ ⟧n H η = {!   !}
⟦ n-plusL≲ e ⟧n H η = {!   !}
⟦ n-plusR≲ e ⟧n H η = {!   !}
⟦ n-emptyR ⟧n H η = {!   !}
⟦ n-emptyL ⟧n H η = {!   !}
⟦ n-map≲ e x x₁ ⟧n H η = {!   !}
⟦ n-map· e x x₁ x₂ ⟧n H η = {!   !}
⟦ n-complR-inert e ⟧n H η = {!   !}
⟦ n-complR e ⟧n H η = {!   !}
⟦ n-complL-inert e ⟧n H η = {!   !}
⟦ n-complL e ⟧n H η = {!   !} 

--------------------------------------------------------------------------------
-- Denoting terms

⟦_⟧ : ∀ {Δ : KEnv ιΔ} {τ : NormalType Δ (★ {ι})} {Γ : Env Δ ιΓ} → 
        Term Γ τ → 
        (H : ⟦ Δ ⟧ke) → (η : ⟦ Γ ⟧e H) → ⟦ τ ⟧nf H
⟦ ` x ⟧ H η = ⟦ x ⟧v H η
⟦ `λ M ⟧ H η = λ x → ⟦ M ⟧ H (η , x)
⟦ M · N ⟧ H η = (⟦ M ⟧ H η) (⟦ N ⟧ H η)
⟦ Λ M ⟧ H η = λ k → ⟦ M ⟧ (H , k) (η , k) 
-- needs substitution lemma
⟦ M ·[ τ ] ⟧ H η = {!(⟦ M ⟧ H η)   !}
⟦ `ƛ M ⟧ H η =  λ p → ⟦ M ⟧ H (η , p) 
⟦ M ·⟨ e ⟩ ⟧ H η = ⟦ M ⟧ H η (⟦ e ⟧n H η)
⟦ # ℓ ⟧ H η = tt'
⟦ l Π▹ne M ⟧ H η = λ { fzero → ⟦ M ⟧ H η }
⟦ l Π▹ M ⟧ H η = λ { fzero → ⟦ M ⟧ H η }
⟦ M Π/ne l ⟧ H η = {!!}
⟦ M Π/ l ⟧ H η =  ⟦ M ⟧ H η fzero
⟦ prj M e ⟧ H η = {!!}
⟦ (M ⊹ N) x ⟧ H η = {!!}
⟦ syn ρ φ M ⟧ H η = {!!}
⟦ ana ρ φ τ eq₁ eq₂ M ⟧ H η = {!!}
⟦ l Σ▹ne M ⟧ H η = fzero , (⟦ M ⟧ H η)
⟦ l Σ▹ M ⟧ H η = fzero , (⟦ M ⟧ H η)
⟦ M Σ/ne l ⟧ H η with ⟦ M ⟧ H η  
... | fzero , m = m
⟦ M Σ/ l ⟧ H η with ⟦ M ⟧ H η  
... | fzero , m = m
⟦ inj M e ⟧ H η = {!!}
⟦ (M ▿ N) x ⟧ H η = {!!}
⟦ ⟨ r ⟩ ⟧ H η = {!!}
⟦ ⟨ l ▹ M ⟩via i ⟧ H η = {!!}
