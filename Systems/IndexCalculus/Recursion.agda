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

Mu : ∀ {ℓ} → (Functor ℓ) → (n : ℕ) → Set ℓ
Mu F zero = ⊤
Mu F (suc n) = F (Mu F n)

In : ∀ {ℓ} {F : Functor ℓ} → 
           (fmap : FmapT {ℓ} F) → (n : ℕ) → F (Mu F n) → Mu F n
In fmap zero xs = tt
In {ℓ} {F} fmap (suc n) xs = fmap {F (Mu F n)} {Mu F n} (In {_} {F} fmap n) xs

fmap-Maybe : ∀ {ℓ} → Functor ℓ → Set (lsuc ℓ)
fmap-Maybe {ℓ} F = (A : Set ℓ) → Maybe
             ((B : Set ℓ) → Maybe
             (Maybe (Maybe A → Maybe B) →
              Maybe (Maybe (F A) → Maybe (F B))))

In-Maybe : ∀ {ℓ} {F : Functor ℓ} → 
           (fmap : fmap-Maybe F) → (n : ℕ) → Maybe (F (Mu F n)) → Maybe (Mu F n)
In-Maybe fmap ℕ.zero d = just tt
In-Maybe {ℓ} {F} fmap (ℕ.suc n) d = do
  f₁ ← fmap (F (Mu F n))
  f₂ ← f₁ (Mu F n)
  f₃ ← f₂ (just (In-Maybe {_} {F} fmap n))
  f₃ d

cata : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → 
       (fmap : FmapT F) → (n : ℕ) → (F (Maybe A) → Maybe A) → Mu F n → Maybe A
cata {ℓ} {F} fmap ℕ.zero φ d = nothing
cata {ℓ} {F} fmap (ℕ.suc n) φ d = (φ (fmap (cata fmap n φ) d)) -- φ (fmap (cata fmap n φ) d)

-- TODO: Change this to use maybe fmap type so that it can be piped in thru term semantics.
-- Also use
--   join→ : Maybe (Maybe A → Maybe B) → Maybe A → Maybe B
-- to make fmap-Maybe type less garbage.
Out : ∀ {ℓ} {F : Functor ℓ} → 
        (n : ℕ) (fmap : FmapT F) → 
        (return : ∀ {A} → A → F A) →
        Mu F n → Mu F (ℕ.suc n)
Out {_} {F} ℕ.zero fmap return xs = return xs
Out {_} {F} (ℕ.suc n) fmap return xs = fmap (Out n fmap return) xs

--------------------------------------------------------------------------------
-- μ ∘ Σ

-- μΣ : ∀ {ℓ} → Row (Functor ℓ) → Set ℓ
-- μΣ ρ = Mu (λ X → Σ ( ρ  ·⌈ X ⌉))

-- --------------------------------------------------------------------------------
-- -- Inclusion Algebras

-- Alg : ∀ {ℓ ι} → Row (Functor ℓ) → Set ι → Set (lsuc ℓ ⊔ ι)
-- Alg {ℓ} ρ τ = 
--   (w : Row (Set ℓ → Set ℓ)) → 
--     Maybe (
--       (y : Row (Set ℓ → Set ℓ)) → Maybe (        
--        w · y ~ w → Maybe (
--          Maybe (Σ ((ρ ·⌈ (μΣ w) ⌉)) → Maybe (μΣ w → Maybe τ) → Maybe τ
--        ))))

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
