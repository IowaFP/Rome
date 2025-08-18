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
-- Denoting terms

⟦_⟧e : ∀ {Δ : KEnv ιΔ} → Env Δ ιΓ → ⟦ Δ ⟧ke → Set ιΓ
⟦ ∅ ⟧e H = ⊤'
⟦ Γ ,   τ ⟧e H = (⟦ Γ ⟧e H) × (⟦ τ ⟧nf H)
⟦ Γ ,,  κ ⟧e (H , ⟦κ⟧) = ⟦ Γ ⟧e H × ⟦ κ ⟧k
⟦ Γ ,,, π ⟧e H = ⟦ Γ ⟧e H × ⟦ π ⟧p H 

weaken⟦⟧ : ∀ {τ : NormalType Δ (★ {ι})} {H : ⟦ Δ ⟧ke} {κ : Kind ικ} {k : ⟦ κ ⟧k} → 
             ⟦ τ ⟧nf H → ⟦ weakenₖNF τ  ⟧nf (H , k)
weaken⟦⟧ {τ = ne x} {H} {κ} {k} ⟦τ⟧ = {!!}
weaken⟦⟧ {τ = τ₁ `→ τ₂} {H} {κ} {k} ⟦τ⟧ = λ x → weaken⟦⟧ (⟦τ⟧ {!!})
weaken⟦⟧ {τ = `∀ τ} {H} {κ} {k} ⟦τ⟧ = {!!}
weaken⟦⟧ {τ = π ⇒ τ} {H} {κ} {k} ⟦τ⟧ = {!!}
weaken⟦⟧ {τ = ⌊ τ ⌋} {H} {κ} {k} ⟦τ⟧ = ⟦τ⟧
weaken⟦⟧ {τ = Π τ} {H} {κ} {k} ⟦τ⟧ = {!!}
weaken⟦⟧ {τ = Σ τ} {H} {κ} {k} ⟦τ⟧ = {!!}

⟦_⟧v : ∀ {Γ : Env Δ ιΓ} {τ : NormalType Δ (★ {ι})} → 
         Var Γ τ → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → ⟦ τ ⟧nf H
⟦ Z ⟧v H (_ , ⟦τ⟧) = ⟦τ⟧
⟦ S v ⟧v H (η , _) = ⟦ v ⟧v H η
⟦ K v ⟧v (H , _) (η , _) = {!⟦ v ⟧v H η !}
⟦ P v ⟧v H (η , _) = ⟦ v ⟧v H η

⟦_⟧ : ∀ {Δ : KEnv ιΔ} {τ : NormalType Δ (★ {ι})} {Γ : Env Δ ιΓ} → 
        NormalTerm Γ τ → 
        (H : ⟦ Δ ⟧ke) → (η : ⟦ Γ ⟧e H) → ⟦ τ ⟧nf H
⟦ ` x ⟧ H η = ⟦ x ⟧v H η
⟦ `λ M ⟧ H η = λ x → ⟦ M ⟧ H (η , x)
⟦ M · N ⟧ H η = (⟦ M ⟧ H η) (⟦ N ⟧ H η)
⟦ Λ M ⟧ H η = λ k → ⟦ M ⟧ (H , k) (η , k) 
⟦ M ·[ τ ] ⟧ H η = {!(⟦ M ⟧ H η) !}
⟦ `ƛ M ⟧ H η =  λ p → ⟦ M ⟧ H (η , p) 
⟦ M ·⟨ x ⟩ ⟧ H η = {!!}
⟦ # ℓ ⟧ H η = tt'
⟦ M Π▹ne M₁ ⟧ H η = {!!}
⟦ M Π▹ M₁ ⟧ H η = {!!}
⟦ M Π/ne M₁ ⟧ H η = {!!}
⟦ M Π/ M₁ ⟧ H η =  ⟦ M ⟧ H η fzero
⟦ prj M x ⟧ H η = {!!}
⟦ (M ⊹ M₁) x ⟧ H η = {!!}
⟦ syn ρ φ M ⟧ H η = {!!}
⟦ ana ρ φ τ eq₁ eq₂ M ⟧ H η = {!!}
⟦ M Σ▹ne M₁ ⟧ H η = {!!}
⟦ M Σ▹ M₁ ⟧ H η = {!!}
⟦ M Σ/ne M₁ ⟧ H η = {!!}
⟦ M Σ/ M₁ ⟧ H η = {!!}
⟦ inj M x ⟧ H η = {!!}
⟦ (M ▿ M₁) x ⟧ H η = {!!}
⟦ ⟨ x ⟩ ⟧ H η = {!!}
⟦ ⟨ l ▹ M ⟩via x ⟧ H η = {!!}
