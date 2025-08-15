module Rome.Both.Terms.Denotation where 

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars
open import Rome.Both.Kinds.Denotation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Denotation

open import Rome.Both.Terms.Normal.Syntax

--------------------------------------------------------------------------------
-- Denoting terms

⟦_⟧e : NormalContext Δ → ⟦ Δ ⟧ke → Set ι
⟦ ∅ ⟧e H = ⊤'
⟦ Γ , τ ⟧e H  = ⟦ Γ ⟧e H × (⟦ τ ⟧nf H)
⟦ Γ ,, κ ⟧e (H , ⟦κ⟧) = ⟦ Γ ⟧e H × {!⟦ κ ⟧k!}
⟦ Γ ,,, π ⟧e H = ⟦ Γ ⟧e H × ⟦ π ⟧p H 

⟦_⟧ : ∀ {Δ : KEnv ιΔ} {τ : NormalType Δ (★ {ι})} {Γ : NormalContext Δ} → 
        NormalTerm Γ τ → 
        (H : ⟦ Δ ⟧ke) → ⟦ τ ⟧nf H
        
