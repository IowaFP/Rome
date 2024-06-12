module IndexCalculus.Variants.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants
open import IndexCalculus.Records
open import IndexCalculus.Recursion


--------------------------------------------------------------------------------
-- μ ∘ Σ

μΣ : ∀ {ℓ} → Row (Functor ℓ) → Set ℓ
μΣ ρ = Mu (λ X → Σ ( ρ  ·⌈ X ⌉))

--------------------------------------------------------------------------------
-- 

unrec : ∀ {ℓ} {ρ y w : Row (Functor ℓ)} {τ : Set ℓ} →
        ρ · y ~ w → (μΣ ρ → τ) → (μΣ w → τ) → Σ (ρ ·⌈ (μΣ w) ⌉) → τ
unrec π f r v = {!!}

-- -- This term isn't populatable...
-- -- It needs to return 
-- --   (Σ ρ₁ (μΣ (ρ₁ ⊕ ρ₂))) or (Σ ρ₂ (μΣ (ρ₁ ⊕ ρ₂)))

-- injμ⁻¹ : ∀ {ℓ ι} {ρ₁ ρ₂ ρ₃ : Row (Functor ℓ)} {C : Set ι} → 
--              ρ₁ · ρ₂ ~ ρ₃ → μΣ ρ₃ → (μΣ ρ₁) or (μΣ ρ₂)
-- injμ⁻¹ ev (In v) = {!!}

-- -- The strategy here is to take
-- --   v : μ (Σ ρ₃)
-- -- turn it into
-- --   v : (Σ ρ₁ (μΣ (ρ₁ ⊕ ρ₂))) or (Σ ρ₂ (μΣ (ρ₁ ⊕ ρ₂)))
-- -- and then bi-fmap (on both sides)
-- --   f : μΣ (ρ₁ ⊕ ρ₂) → C
-- -- 
-- _▿μ_Using_ : ∀ {ℓ ι} {ρ₁ ρ₂ ρ₃ : Row (Functor ℓ)} {C : Set ι} → 
--              ρ₁ · ρ₂ ~ ρ₃ → (μΣ ρ₁ → C) → (μΣ ρ₂ → C) → μΣ ρ₃ → C
-- (f ▿μ g Using ev) (In v) = {!!}
