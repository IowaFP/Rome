module Rome.Types.Semantics where

import Mix.Mix as M

open import Rome.Kinds.Syntax
open import Rome.Types.Syntax
 
-- ⟦_⟧v : KEnv → M.KEnv

⟦_⟧κ : Kind → M.Kind
⟦ ★ ⟧κ = M.★
⟦ L ⟧κ = M.★
⟦ R[ κ ] ⟧κ = M.Nat M.`→ ⟦ κ ⟧κ
⟦ κ₁ `→ κ₂ ⟧κ = ⟦ κ₁ ⟧κ M.`→ ⟦ κ₂ ⟧κ

⟦_⟧Δ : KEnv → M.KEnv
⟦ ε ⟧Δ = M.ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ M., ⟦ κ ⟧κ
⟦_⟧τ : ∀ {Δ} {κ} → Type Δ κ → M.Type ⟦ Δ ⟧Δ ⟦ κ ⟧κ
⟦ Π ρ ⟧τ = M.`∀ M.Nat (M.Ix (M.tvar M.Z) M.`→ (M.weaken ⟦ ρ ⟧τ M.·[ M.tvar M.Z ]))
⟦ Σ ρ ⟧τ = M.`∃ M.Nat (M.weaken ⟦ ρ ⟧τ M.·[ M.tvar M.Z ])
⟦ ε ⟧τ = M.`λ M.Nat {!!}
⟦ l R▹ τ ⟧τ = {!!}
 
⟦ U ⟧τ = M.⊤
⟦ tvar x ⟧τ = M.tvar {!x!}
⟦ τ₁ `→ τ₂ ⟧τ = ⟦ τ₁ ⟧τ M.`→ ⟦ τ₂ ⟧τ
⟦ `∀ {Δ} κ τ ⟧τ = M.`∀ ⟦ κ ⟧κ (⟦_⟧τ {Δ , κ} τ)
⟦ `λ {Δ} κ τ ⟧τ = M.`λ ⟦ κ ⟧κ (⟦_⟧τ {Δ , κ} τ)
⟦ τ ·[ τ₁ ] ⟧τ = {!!}
⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}
⟦ π' ⇒ τ ⟧τ = {!!}
⟦ lab l ⟧τ = M.⊤
⟦ l ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ ⌊ τ ⌋ ⟧τ = M.⊤
⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
