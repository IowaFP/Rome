module Rome.IndexCalculus.Rows.Properties where

open import Rome.Prelude
open import Rome.Preludes.Level hiding (suc ; zero)

open import Rome.IndexCalculus.Rows
open import Rome.IndexCalculus.GVars

--------------------------------------------------------------------------------
-- Building evidence that ρ pick i · ρ delete i ~ ρ.

pickedIn : ∀ {ℓ} {A : Set ℓ} {ρ : Row {ℓ} A} {i : Ix {ℓ} ρ} → ρ pick i ≲ ρ
pickedIn {ℓ} {A} {suc _ , _} {i} fzero = i , refl

deletedIn : ∀ {ℓ} {A : Set ℓ} {ρ : Row {ℓ} A} {i : Ix {ℓ} ρ} → ρ delete i ≲ ρ
deletedIn {ℓ} {A} {suc _ , f} {fzero} fzero = fsuc fzero , refl
deletedIn {ℓ} {A} {suc _ , f} {fsuc i} fzero = fzero , refl
deletedIn {ℓ} {A} {suc _ , f} {fzero} (fsuc j) = fsuc (fsuc j) , refl
deletedIn {ℓ} {A} {suc _ , f} {fsuc i} (fsuc j) = (fsuc (punchIn i j)) , refl

recombine : ∀ {ℓ} {A : Set ℓ} → (ρ : Row {ℓ} A) → (i : Ix {ℓ} ρ) → ρ pick i · ρ delete i ~ ρ
recombine {ℓ} {A} ρ i = evid ρ i , (pickedIn , deletedIn {i = i}) where
  evid : (ρ : Row {ℓ} A) (i : Ix {ℓ} ρ) (j : Fin (fst ρ)) →
            Σi[ k ≤ fst (ρ pick i) ] (snd (ρ pick i) k ≡ snd ρ j) at ℓ or
            Σi[ k ≤ fst (ρ delete i) ] (snd (ρ delete i) k ≡ snd ρ j) at ℓ
  evid ρ fzero fzero = left (fzero , refl)
  evid ρ fzero (fsuc j) = right (j , refl)
  evid (suc (suc n) , f) (fsuc i) fzero = right (fzero , refl)
  evid (suc zero , f) (fsuc ()) fzero
  evid (suc (suc n) , f) (fsuc i) (fsuc j)
    with evid (suc n , λ x → f (fsuc x)) i j
  ... | left (fzero , g) = left (fzero , g)
  ... | right (i' , g)   = right (( 1 ↑ʳ i') , g)

--------------------------------------------------------------------------------
-- x · y ~ z implies x≲z in our (commutative) row theory.

·-to-≲L : ∀ {ℓ} {A : Set ℓ} → {ρ₁ ρ₂ ρ₃  : Row {ℓ} A} →
         ρ₁ · ρ₂ ~ ρ₃ →
         ρ₁ ≲ ρ₃
·-to-≲L (_ , l , _) = l

·-to-≲R : ∀ {ℓ} {A : Set ℓ} → {ρ₁ ρ₂ ρ₃  : Row {ℓ} A} →
         ρ₁ · ρ₂ ~ ρ₃ →
         ρ₂ ≲ ρ₃
·-to-≲R (_ , _ , r) = r

--------------------------------------------------------------------------------
-- Expected results (monoid properties, etc)

≲-refl : ρ ≲ ρ
≲-refl = λ i → i , refl

ε-≲ : emptyRow ≲ ρ
ε-≲ = λ { () }

ε-id-R : ∀ {ℓ} {A : Set ℓ} {ρ : Row {ℓ} A} → ρ · emptyRow ~ ρ
ε-id-R = (λ i → left ((i , refl))) , ≲-refl , ε-≲

ε-id-L : ∀ {ℓ} {A : Set ℓ} {ρ : Row {ℓ} A} → emptyRow · ρ ~ ρ
ε-id-L = (λ i → right ((i , refl))) , ε-≲ , ≲-refl
