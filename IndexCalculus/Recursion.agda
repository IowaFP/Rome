module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Relation
open import Preludes.Data
open import Data.Empty.Polymorphic using (⊥) public
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
Mu F zero = ⊥
Mu F (suc n) = F (Mu F n)

-- In : ∀ {ℓ} {F : Functor ℓ} → 
--            (n : ℕ) → (fmap : FmapT {ℓ} F) → F (Mu F n) → Mu F n
-- In zero fmap xs = tt
-- In {ℓ} {F} (suc n) fmap xs = fmap {F (Mu F n)} {Mu F n} (In {_} {F} n fmap) xs

-- cata : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → 
--        (fmap : FmapT F) → 
--        (n : ℕ) → (F A → A) → A → Mu F n → A
-- cata {ℓ} {F} fmap ℕ.zero φ a d = a
-- cata {ℓ} {F} fmap (ℕ.suc n) φ a d = φ (fmap (cata fmap n φ a) d)

-- Out : ∀ {ℓ} {F : Functor ℓ} → 
--         (n : ℕ) (fmap : FmapT F) → 
--         (return : ∀ {A} → A → F A) → 
--         Mu F n → Mu F (ℕ.suc n)
-- Out {_} {F} n fmap return d = cata fmap n (fmap (In n fmap)) (return d) d

--------------------------------------------------------------------------------
-- Cleaning up nested maybes.

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
-- Maybe-ized In, Out, and catamorphism.

In-Maybe : ∀ {ℓ} {F : Functor ℓ} → 
           (n : ℕ) (fmap : Fmap-MaybeT F) → Maybe (F (Mu F n)) → Maybe (Mu F n)
In-Maybe ℕ.zero fmap d = nothing
In-Maybe {ℓ} {F} (ℕ.suc n) fmap d = fmap (In-Maybe {_} {F} n fmap) d
-- In-Maybe ℕ.zero fmap d = just tt
-- In-Maybe {ℓ} {F} (ℕ.suc n) fmap d = fmap (In-Maybe {_} {F} n fmap) d

Out-Maybe : ∀ {ℓ} {F : Functor ℓ} → 
           (n : ℕ) (fmap : Fmap-MaybeT F) → Maybe (Mu F n) → Maybe (F (Mu F n))
Out-Maybe ℕ.zero fmap d = nothing
Out-Maybe {ℓ} {F} (ℕ.suc n) fmap d = fmap (Out-Maybe {_} {F} n fmap) d

-- cata-Maybe : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → 
--        (fmap : Fmap-MaybeT F) → 
--        (n : ℕ) → (Maybe (F A) → Maybe A) → Maybe A → Maybe (Mu F n) → Maybe A
-- cata-Maybe {ℓ} {F} fmap ℕ.zero φ a d = a
-- cata-Maybe {ℓ} {F} fmap (ℕ.suc n) φ a d =  φ (fmap (cata-Maybe fmap n φ a) d)

-- Out-Maybe : ∀ {ℓ} {F : Functor ℓ} → 
--         (n : ℕ) (fmap : Fmap-MaybeT F) → 
--         Maybe (Mu F n) → Maybe (F (Mu F n))
-- Out-Maybe {_} {F} n fmap = cata-Maybe fmap n (fmap (In-Maybe n fmap)) nothing

--------------------------------------------------------------------------------
-- Example

open import Data.Sum public

NatF :  Functor lzero
NatF X = ⊤ ⊎ X

NatF_fmap : Fmap-MaybeT NatF
NatF f fmap (just (left x)) = just (left x)
NatF f fmap (just (right y)) with f (just y)
... | just x = just (right x)
... | nothing = nothing
NatF f fmap nothing = nothing

Nat3 = Mu NatF 3

nat3_zero = In-Maybe 3 NatF_fmap (just (inj₁ tt))
nat3_one = In-Maybe 3 NatF_fmap (just (inj₂ (inj₁ tt)))

nat3_four = In-Maybe 3 NatF_fmap (just (inj₂ (inj₂ (inj₂ (inj₁ tt)))))

nat3_test1 : In-Maybe 3 NatF_fmap (Out-Maybe 3 NatF_fmap nat3_one) ≡ nat3_one
nat3_test1 = refl

-- Out moves up an approximation, so to typecheck this the operations have to happen at the lower approximation
nat3_test2 : Out-Maybe 2 NatF_fmap (In-Maybe 2 NatF_fmap nat3_one) ≡ nat3_one
nat3_test2 = refl

nat3_test3 : nat3_four ≡ nothing
nat3_test3 = refl

nat3_test4 : nat3_one ≡ just (inj₂ (inj₁ tt))
nat3_test4 = refl
