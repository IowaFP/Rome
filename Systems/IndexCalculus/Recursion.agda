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

cata : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → 
       (fmap : FmapT F) → 
       (n : ℕ) → (F A → A) → A → Mu F n → A
cata {ℓ} {F} fmap ℕ.zero φ a d = a
cata {ℓ} {F} fmap (ℕ.suc n) φ a d = φ (fmap (cata fmap n φ a) d)

Out : ∀ {ℓ} {F : Functor ℓ} → 
        (n : ℕ) (fmap : FmapT F) → 
        (return : ∀ {A} → A → F A) → 
        Mu F n → Mu F (ℕ.suc n)
Out {_} {F} n fmap return d = cata fmap n (fmap (In fmap n)) (return d) d


--------------------------------------------------------------------------------
-- Maybe bullshit helpers.

join→ : ∀ {ℓ ι} {A : Set ℓ} {B : Set ι} → 
          Maybe (Maybe A → Maybe B) → Maybe A → Maybe B
join→ (just x) a = x a
join→ nothing a = nothing

join→k : ∀ {ℓ ι} {A : Set ℓ} {B : Set ι} → 
          Maybe (A → Maybe B) → A → Maybe B
join→k (just x) a = x a
join→k nothing a = nothing

--------------------------------------------------------------------------------
-- Maybe bullshit fmap.

Fmap-MaybeT-garbage : ∀ {ℓ} → Functor ℓ → Set (lsuc ℓ)
Fmap-MaybeT-garbage {ℓ} F = (A : Set ℓ) → Maybe
             ((B : Set ℓ) → Maybe
             (Maybe (Maybe A → Maybe B) →
              Maybe (Maybe (F A) → Maybe (F B))))

Fmap-MaybeT : ∀ {ℓ} → Functor ℓ → Set (lsuc ℓ)
Fmap-MaybeT {ℓ} F = 
  ∀ {A : Set ℓ}
    {B : Set ℓ} →
    (Maybe A → Maybe B) →
    Maybe (F A) → Maybe (F B)

ungarbage : ∀ {ℓ} → {F : Functor ℓ} → Fmap-MaybeT-garbage F → 
             Fmap-MaybeT F
ungarbage {F} fmap {A} {B} φ fa = fmap A >>= λ f → f B >>= λ f → f (just φ) >>= λ f → f fa

--------------------------------------------------------------------------------
-- Maybe bullshit In, Out, and catamorphism.

In-Maybe : ∀ {ℓ} {F : Functor ℓ} → 
           (fmap : Fmap-MaybeT F) → (n : ℕ) → Maybe (F (Mu F n)) → Maybe (Mu F n)
In-Maybe fmap ℕ.zero d = just tt
In-Maybe {ℓ} {F} fmap (ℕ.suc n) d = fmap (In-Maybe {_} {F} fmap n) d

cata-Maybe : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → 
       (fmap : Fmap-MaybeT F) → 
       (n : ℕ) → (Maybe (F A) → Maybe A) → Maybe A → Maybe (Mu F n) → Maybe A
cata-Maybe {ℓ} {F} fmap ℕ.zero φ a d = a
cata-Maybe {ℓ} {F} fmap (ℕ.suc n) φ a d =  φ (fmap (cata-Maybe fmap n φ a) d) -- φ (fmap (cata-Maybe fmap n φ a) d)

Out-Maybe : ∀ {ℓ} {F : Functor ℓ} → 
        (n : ℕ) (fmap : Fmap-MaybeT F) → 
        (return : ∀ {A} → Maybe A → Maybe (F A)) → 
        Maybe (Mu F n) → Maybe (F (Mu F n))
Out-Maybe {_} {F} n fmap return d = cata-Maybe fmap n (fmap (In-Maybe fmap n)) (return d) d

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
