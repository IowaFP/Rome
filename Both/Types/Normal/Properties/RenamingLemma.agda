module Rome.Both.Types.Normal.Properties.RenamingLemma where 

open import Rome.Both.Prelude
open import Rome.Both.Preludes.Level
open import Rome.Both.FunExt

open import Rome.Both.Kinds.Denotation
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Denotation 
open import Rome.Both.Types.Normal.Renaming

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Renaming

--------------------------------------------------------------------------------
-- Renaming lemma for denotation

--------------------------------------------------------------------------------
-- A renaming preservation is a renaming that does not interfere with the meaning 
-- of variables. We use this sort of point-wise equality to show that renaming 
-- and substitution respect the meaning of types.

renaming-preservation : ∀ {Δ₁ : KEnv ιΔ₁} {Δ₂ : KEnv ιΔ₂} 
                        (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke) →
                        (r : Renamingₖ Δ₁ Δ₂) →  Setω
renaming-preservation {Δ₁ = Δ₁} {Δ₂ = Δ₂} H₁ H₂ r = (∀ {ικ} {κ : Kind ικ} (α : TVar Δ₁ κ) → ⟦ α ⟧tv H₁ ≡ ⟦ r α ⟧tv H₂)               

id-preservation : ∀ (Δ : KEnv ιΔ) (H : ⟦ Δ ⟧ke) →
                    renaming-preservation H H id
id-preservation Δ H x = refl     

lift-preservation : (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
                    (κ : Kind ικ) (r : Renamingₖ Δ₁ Δ₂)
                    (pres : renaming-preservation H₁ H₂ r) → 
                    (∀ (x : ⟦ κ ⟧k) → renaming-preservation (H₁ , x) (H₂ , x) (liftₖ r))
lift-preservation H₁ H₂ κ r pres x Z = refl
lift-preservation H₁ H₂ κ r pres x (S v) = pres v 

ren-preservationNE : (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
                    (r : Renamingₖ Δ₁ Δ₂)
                    (pres : renaming-preservation H₁ H₂ r) → 
                    (∀ (τ : NeutralType Δ₁ κ) → (⟦ τ ⟧ne H₁) ≡ (⟦ renₖNE r τ ⟧ne H₂))
ren-preservation : (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
                    (r : Renamingₖ Δ₁ Δ₂)
                    (pres : renaming-preservation H₁ H₂ r) → 
                    (∀ (τ : NormalType Δ₁ κ) → (⟦ τ ⟧nf H₁) ≡ (⟦ renₖNF r τ ⟧nf H₂))
ren-preservationPred : (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
                       (r : Renamingₖ Δ₁ Δ₂)
                       (pres : renaming-preservation H₁ H₂ r) → 
                       (∀ (π : NormalPred Δ₁ R[ κ ]) → (⟦ π ⟧p H₁) ≡ (⟦ renPredₖNF r π ⟧p H₂))                   

ren-preservationNE H₁ H₂ r pres (` α) = pres α
ren-preservationNE H₁ H₂ r pres (n · τ) 
  rewrite ren-preservationNE H₁ H₂ r pres n 
  | ren-preservation H₁ H₂ r pres τ = refl

ren-preservationPred H₁ H₂ r pres (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-preservation H₁ H₂ r pres ρ₁ 
  | ren-preservation H₁ H₂ r pres ρ₂ 
  | ren-preservation H₁ H₂ r pres ρ₃ = refl
ren-preservationPred H₁ H₂ r pres (ρ₁ ≲ ρ₂) 
  rewrite ren-preservation H₁ H₂ r pres ρ₁ 
  | ren-preservation H₁ H₂ r pres ρ₂ = refl

ren-preservation H₁ H₂ r pres (ne x) = ren-preservationNE H₁ H₂ r pres x
ren-preservation H₁ H₂ r pres (τ <$> x) 
  rewrite ren-preservation H₁ H₂ r pres τ 
  | ren-preservationNE H₁ H₂ r pres x = refl
-- Need functional extensionality
ren-preservation H₁ H₂ r pres (`λ τ) = {!   !}
ren-preservation H₁ H₂ r pres (τ₁ `→ τ₂)
  rewrite ren-preservation H₁ H₂ r pres τ₁ 
  | ren-preservation H₁ H₂ r pres τ₂ = refl
ren-preservation H₁ H₂ r pres (`∀ τ) = {!   !}
ren-preservation H₁ H₂ r pres (π ⇒ τ) 
  rewrite ren-preservationPred H₁ H₂ r pres π 
  | ren-preservation H₁ H₂ r pres τ  = refl 
ren-preservation H₁ H₂ r pres (⦅ ρ ⦆ oρ) = {!   !}
ren-preservation H₁ H₂ r pres (lab l) = refl
ren-preservation H₁ H₂ r pres ⌊ τ ⌋ = refl
ren-preservation H₁ H₂ r pres (Π τ) 
  rewrite ren-preservation H₁ H₂ r pres τ = refl 
ren-preservation H₁ H₂ r pres (Σ τ) 
  rewrite ren-preservation H₁ H₂ r pres τ = refl 
ren-preservation H₁ H₂ r pres (τ₂ ∖ τ₁) 
  rewrite ren-preservation H₁ H₂ r pres τ₂
  | ren-preservation H₁ H₂ r pres τ₁ = refl 
ren-preservation H₁ H₂ r pres (l ▹ₙ τ) 
  rewrite ren-preservationNE H₁ H₂ r pres l
  | ren-preservation H₁ H₂ r pres τ = refl 

-- Meaning is preserved by weakening 
weaken-preservation : (H : ⟦ Δ ⟧ke) → 
                      {κ : Kind ικ} {k : ⟦ κ ⟧k} (τ : NormalType Δ κ) → (⟦ τ ⟧nf H) ≡ (⟦ weakenₖNF τ ⟧nf (H , k))
weaken-preservation H {κ = κ} {k = k} τ = ren-preservation H (H , k) S (λ x → refl) τ 