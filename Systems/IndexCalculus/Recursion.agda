{-# OPTIONS --allow-unsolved-metas  #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants
open import IndexCalculus.Records

--------------------------------------------------------------------------------
-- Functors.

Functor = λ ℓ → (Set ℓ → Set ℓ)
FmapT : ∀ {ℓ} → (F : Functor ℓ) → Set (lsuc ℓ)
FmapT {ℓ} F = ∀ {A B : Set ℓ} → (A → B) → F A → F B 

FmapT-ρ : ∀ {ℓ} → (ρ : Row (Functor ℓ)) → Set (lsuc ℓ)
FmapT-ρ ρ = Π (lift₂ FmapT ρ)

--------------------------------------------------------------------------------
-- Denoting recursive types.

{-# NO_POSITIVITY_CHECK #-}
data Mu {ℓ} (F : Functor ℓ) : Set ℓ where
  In : F (Mu F) → Mu F

out : ∀ {ℓ} {F : Functor ℓ} → Mu F → F (Mu F)
out (In x) = x

--------------------------------------------------------------------------------
-- μ ∘ Σ

μΣ : ∀ {ℓ} → Row (Functor ℓ) → Set ℓ
μΣ ρ = Mu (λ X → Σ ( ρ  ·⌈ X ⌉))

--------------------------------------------------------------------------------
-- Inclusion Algebras

Alg : ∀ {ℓ ι} → Row (Functor ℓ) → Set ι → Set (lsuc ℓ ⊔ ι)
Alg {ℓ} ρ τ = 
  (w : Row (Set ℓ → Set ℓ)) → 
    Maybe (
      (y : Row (Set ℓ → Set ℓ)) → Maybe (        
       w · y ~ w → Maybe (
         Maybe (Σ ((ρ ·⌈ (μΣ w) ⌉)) → Maybe (μΣ w → Maybe τ) → Maybe τ
       ))))

  --   w · y ~ w → 
  --   Σ (ρ ·⌈ (μΣ w) ⌉) → 
  --   (μΣ w → τ ) → τ

  -- ((w : Row (Set ℓ → Set ℓ)) →
  --      Maybe
  --      ((y : Row (Set ℓ → Set ℓ)) →
  --       Maybe
  --       (ρ IndexCalculus.· s₁ ~ s →
  --        Maybe
  --        (Maybe
  --         (IndexCalculus.Σ
  --          (fst (⟦ K² ρ ⟧t ((H , s) , s₁)) ,
  --           (λ i →
  --              snd (⟦ K² ρ ⟧t ((H , s) , s₁)) i
  --              (Mu (λ X → IndexCalculus.Σ (fst s , (λ i₁ → snd s i₁ X))))))) →
  --         Maybe
  --         (Maybe
  --          (Maybe (Mu (λ X → IndexCalculus.Σ (fst s , (λ i → snd s i X)))) →
  --           Maybe (⟦ K² τ ⟧t ((H , s) , s₁))) →
  --          Maybe (⟦ K² τ ⟧t ((H , s) , s₁)))))))

--------------------------------------------------------------------------------
-- Bifunctor combinators (for rows)

-- _⊕_ : ∀ {ℓ} → (ρ₁ ρ₂ : Row (Functor ℓ)) → Row (Functor ℓ)
-- (ρ₁ ⊕ ρ₂) = {!!}
