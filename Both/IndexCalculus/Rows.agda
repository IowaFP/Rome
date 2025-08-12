module Rome.Both.IndexCalculus.Rows where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Data.Nat using (ℕ; zero; suc ; _∸_)
open import Data.List
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map)
open import Data.Product
  using (_×_; ∃; ∃-syntax; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
import Data.Fin as Fin
open Fin  renaming (zero to fzero; suc to fsuc)
  hiding (fold)

open import Data.String renaming (String to Label)

--------------------------------------------------------------------------------
-- Syntax

infixl 5 _≲_
infix  5 _·_~_

--------------------------------------------------------------------------------
-- Rows are maps from indices to types.
Row : ∀ {ℓ : Level} (A : Set ℓ) → Set ℓ
Row A = Σ[ n ∈ ℕ ] (Fin n → Label × A)

-- An index in a Row.
Ix : ∀ {ℓ} {A : Set ℓ} → Row {ℓ} A → Set
Ix (n , _) = Fin n

-- The indices in a row.
ixs : (n : ℕ) → List (Fin n)
ixs zero = []
ixs (suc n) = fromℕ n ∷ Data.List.map inject₁ (ixs n)

--------------------------------------------------------------------------------
-- Naive row extension.

_⨾⨾_  : ∀ {ℓ} {A : Set ℓ} → Label × A → Row {ℓ} A → Row {ℓ} A
a ⨾⨾ (m , Q) = ℕ.suc m , λ { fzero → a ; (fsuc x) → Q x }

--------------------------------------------------------------------------------
-- Empty row.

ε : ∀ {ℓ} {A : Set ℓ} → Row {ℓ} A
ε = 0 , λ ()

--------------------------------------------------------------------------------
-- Singletons.

sing : ∀ {ℓ} {A : Set ℓ} →
       Label × A → Row {ℓ} A
sing a = 1 , λ { fzero → a }

--------------------------------------------------------------------------------
-- Helpers, smart constructers, and syntax.

one = lsuc lzero
two = lsuc one
three = lsuc two

Row₀ = Row {one} Set
Row₁ = Row {two} Set₁
Row₂ = Row {three} Set₂

infix 2 Σi-syntax

Σi-syntax : {ℓ : Level} (n : ℕ) → (Fin n → Set ℓ) → Set ℓ
Σi-syntax {ℓ} n P = ∃ {lzero} {ℓ} (λ (j : Fin n) → P j)

-- The syntax
--   Σi[ i ≤ n ] P at ℓ
-- Says "there exists an index i : Fin n such that P i holds at level ℓ."

syntax Σi-syntax {ℓ} n (λ i → B) = Σi[ i ≤ n ] B at ℓ

--------------------------------------------------------------------------------
-- The row z₁ is "in" row z₂ if all indices of z₁ correspond to some index in z₂.

_≲_ : ∀ {ℓ}{A : Set ℓ} → Row {ℓ} A → Row {ℓ} A → Set ℓ
_≲_ {ℓ} (n , P) (m , Q) = ∀ (i : Fin n) → Σi[ j ≤ m ] (P i ≡ Q j) at ℓ

--------------------------------------------------------------------------------
-- Evidence for x · y ~ z.

_·_~_ : ∀ {ℓ} {A : Set ℓ} →
        Row {ℓ} A →
        Row {ℓ} A →
        Row {ℓ} A →
        Set ℓ
_·_~_ {ℓ} (l , P) (m , Q) (n , R) =

  -- (i) Every index in z corresponds to an index in x _or_ y.
  (∀ (i : Fin n) →
    _or_ {ℓ} {ℓ}
      (Σi[ j ≤ l ] (P j ≡ R i) at ℓ)
      (Σi[ j ≤ m ] (Q j ≡ R i) at ℓ))
  -- (ii) Every index in x corresponds to an index in z.
  × (((l , P) ≲ (n , R))
  -- (iii) Every index in y corresponds to an index in z.
  × ((m , Q) ≲ (n , R)))

--------------------------------------------------------------------------------
-- Row Complement.

-- Extremely dumb try.
complement : ∀ {ℓ} {A : Set ℓ}{ρ₁ ρ₃ : Row A} →
               ρ₁ ≲ ρ₃ → Σ[ ρ₂ ∈ Row A ] (ρ₁ · ρ₂ ~ ρ₃)
complement {_} {A} ρ₁@{n , P} ρ₃@{m , Q} ev = 
  ρ₃ , (λ i → right (i , refl)) , ((λ i → ev i) , (λ i → i , refl))


--------------------------------------------------------------------------------
-- "Punching out" an index from ρ.

_pick_ : ∀ {ℓ} {A : Set ℓ} → (ρ : Row {ℓ} A) → Ix {ℓ} ρ → Row {ℓ} A
_pick_ {ℓ} {A} ρ i = sing (snd ρ i)

_delete_ : ∀ {ℓ} {A : Set ℓ} → (ρ : Row {ℓ} A) → Ix {ℓ} ρ → Row {ℓ} A
_delete_ {ℓ} {A} (suc n , f) i = n , (λ j → f (punchIn i j))

--------------------------------------------------------------------------------
-- Lifting functions (and arguments) to rows.

--------------------------------------------------------------------------------
-- Lifting functions (and arguments) to rows.


lift₁  _·⌈_⌉ : ∀ {ℓ ι} {A : Set ℓ} {B : Set ι} → Row {ℓ ⊔ ι} (A → B) → A → Row {ι} B
lift₁ {A = A} {B = B} (n , P) a = (n , λ i →  (P i .fst) , P i .snd a)
ρ ·⌈ X ⌉ = lift₁ ρ X

lift₂ ⌈_⌉·_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → Row {ℓ₁} A → Row {ℓ₂} B
-- lift₂ {A = A} {B = B} f (n , P) = (n , (λ m → f (P m)))
⌈ ϕ ⌉· ρ = lift₂ ϕ ρ
lift₂ f (n , P) = lift₁ ((n , λ i → (P i .fst) , (λ g → g (P i .snd)))) f

--------------------------------------------------------------------------------
-- Complement

_∈Row_ : ∀ {ℓ}{m}{A : Set ℓ} → 
         (l : String) → 
         (Q : Fin m → String × A) → 
         Dec (Σ[ i ∈ Fin m ] (l ≡ Q i .fst))
_∈Row_ {m = zero} l Q = no λ { () }
_∈Row_ {m = suc m} l Q with l ≟ Q fzero .fst
... | yes p = yes (fzero , p)
... | no  p with l ∈Row (Q ∘ fsuc)
...        | yes (n , q) = yes ((fsuc n) , q) 
...        | no  q = no λ { (fzero , q') → p q' ; (fsuc n , q') → q (n , q') }


compl : ∀ {ℓ}{n m} {A : Set ℓ}  → 
        (P : Fin n → String × A) 
        (Q : Fin m → String × A) → 
        Row A
compl {n = zero} {m} P Q = ϵ
compl {n = suc n} {m} P Q with P fzero .fst ∈Row Q 
... | yes _ = compl (P ∘ fsuc) Q 
... | no _ = (P fzero) ፦ (compl (P ∘ fsuc) Q)


_∖_ : ∀ {ℓ} {A : Set ℓ} → Row {ℓ} A → Row {ℓ} A → Row {ℓ} A
(n , P) ∖ (m , Q) = compl P Q