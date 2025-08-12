module Rome.IndexCalculus.Recursion where

open import Rome.Preludes.Level
open import Rome.Preludes.Relation
open import Rome.Preludes.Data
open import Data.Empty.Polymorphic using (⊥) public
open import Rome.IndexCalculus.Rows
open import Rome.IndexCalculus.Variants
open import Rome.IndexCalculus.Records

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
-- Partial in & out.

In : ∀ {ℓ} {F : Functor ℓ} → 
           (n : ℕ) (fmap : Fmap-MaybeT F) → Maybe (F (Mu F n)) → Maybe (Mu F n)
In ℕ.zero fmap d = nothing
In {ℓ} {F} (ℕ.suc n) fmap d = fmap (In {_} {F} n fmap) d

Out : ∀ {ℓ} {F : Functor ℓ} → 
           (n : ℕ) (fmap : Fmap-MaybeT F) → Maybe (Mu F n) → Maybe (F (Mu F n))
Out ℕ.zero fmap d = nothing
Out {ℓ} {F} (ℕ.suc n) fmap d = fmap (Out {_} {F} n fmap) d

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

nat3_zero = In 3 NatF_fmap (just (left tt))
nat3_one = In 3 NatF_fmap (just (right (left tt)))

nat3_four = In 3 NatF_fmap (just (right (right (right (left tt)))))

nat3_test1 : In 3 NatF_fmap (Out 3 NatF_fmap nat3_one) ≡ nat3_one
nat3_test1 = refl

-- Out moves up an approximation, so to typecheck this the operations have to happen at the lower approximation
nat3_test2 : Out 2 NatF_fmap (In 2 NatF_fmap nat3_one) ≡ nat3_one
nat3_test2 = refl

nat3_test3 : nat3_four ≡ nothing
nat3_test3 = refl

nat3_test4 : nat3_one ≡ just (right (left tt))
nat3_test4 = refl
