module PreROmega.IndexCalculus where

open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; refl)
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Empty using (⊥)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)

-- Finite Sets
open import Data.Fin.Base

--------------------------------------------------------------------------------
-- Syntax
-- TODO: not sure OOPs, really...

infixl 5 _≲_
infix  5 _·_~_
infixl 5 _⊹_
infix  5 _⊹_Using_
infixl 5 _▿_
infixl 5 _▿_Using_
infixr 7 _፦_

--------------------------------------------------------------------------------
-- Rows are maps from indices to types.
Row : Set₁
Row = Σ[ n ∈ ℕ ] (Fin n → Set)

-- Products say: "If you give me an index in range, I can give you a type"
Π : Row → Set
Π ⟨ n , P ⟩ = ∀ (i : Fin n) → P i

-- Sums say "Of the types in this row, I can give you exactly one."
Σ : Row → Set
Σ ⟨ n , P ⟩ = Σ[ i ∈ Fin n ] (P i)

--------------------------------------------------------------------------------
-- The row z₁ is "in" row z₂ if, for all indices of z₁, I can give you an index
-- in z₂ where the types match.

_≲_ : Row → Row → Set₁
_≲_ ⟨ n , P ⟩ ⟨ m , Q ⟩ = ∀ (i : Fin n) → Σ[ j ∈ (Fin m) ] (P i ≡ Q j)

-- We project out of products, inject into sums.
prj : ∀ (z y : Row) (w : z ≲ y) (p : Π y) → Π z
prj z y w p i with w i
... | ⟨ n , P ⟩ rewrite P = p n

inj : ∀ (z y : Row) (w : z ≲ y) (s : Σ z) → Σ y
inj z y w ⟨ n , P ⟩ with w n
... |  ⟨ m , Q ⟩ rewrite Q = ⟨ m , P ⟩

--------------------------------------------------------------------------------
-- Evidence for x · y ~ z

_·_~_ : Row → Row → Row → Set₁
⟨ l , P ⟩ · ⟨ m , Q ⟩ ~ ⟨ n , R ⟩ =
  -- For all indices in the sum
  ∀ (i : Fin n) →
  -- there is a correspondent index in
  -- (at least) one of the summands.
  ((Σ[ j ∈ Fin l ] (P j ≡ R i)) or
  (Σ[ j ∈ Fin m ] (Q j ≡ R i)))
  -- And,
  × 
  -- for all indices in the summands,
  -- there is a corresponding index in the sum.
  (∀ (j : Fin l or Fin m) →
   Σ[ i ∈ Fin n ] (j=i j i) )
   where
     j=i : Fin l or Fin m → Fin n → Set₁
     j=i (left j) i = P j ≡ R i
     j=i (right j) i = Q j ≡ R i

--------------------------------------------------------------------------------
-- Record concatenation

_⊹_ : ∀ {x y z : Row} {x·y~z : x · y ~ z} (Πx : Π x) (Πy : Π y) → Π z
_⊹_ {x} {y} {z} {x·y~z} Πx Πy i with proj₁ (x·y~z i)
... | left ⟨ j , x[j]=z[i] ⟩ rewrite (sym x[j]=z[i]) = Πx j
... | right ⟨ j , y[j]=z[i] ⟩ rewrite (sym y[j]=z[i]) = Πy j

_⊹_Using_ : ∀ {x y z : Row} (Πx : Π x) (Πy : Π y) (x·y~z : x · y ~ z) → Π z
Πx ⊹ Πy Using pf = (_⊹_) {x·y~z = pf} Πx Πy 

_▿_ : ∀ {x y z : Row}
        {C : Set}
        {x·y~z : x · y ~ z}
        (E-Σx : Σ x → C)
        (E-Σy : Σ y → C) →
        Σ z → C
_▿_ {x} {y} {z} {C} {x·y~z} E-Σx E-Σy ⟨ iz , Pz ⟩ with (proj₁ (x·y~z iz))
... | left ⟨ ix , Px ⟩ rewrite (sym Px) = E-Σx ⟨ ix , Pz ⟩
... | right ⟨ iy , Py ⟩ rewrite (sym Py) = E-Σy ⟨ iy , Pz ⟩

_▿_Using_ :
  ∀ {x y z : Row}
  {C : Set}
  (E-Σx : Σ x → C)
  (E-Σy : Σ y → C)
  (x·y~z : x · y ~ z) →
  Σ z → C

(E-Σx ▿ E-Σy Using x·y~z) = (_▿_) {x·y~z = x·y~z} E-Σx E-Σy

--------------------------------------------------------------------------------
-- Nil & Cons for rows
Lin : Row
Lin = ⟨ 0 , (λ ()) ⟩

_፦_ : Set → Row → Row
t ፦ ⟨ n , P ⟩  = ⟨ suc n , Q ⟩
  where
    Q : Fin (suc n) → Set
    Q zero    = t
    Q (suc n) = P n

--------------------------------------------------------------------------------
-- Examples

-- containment
z₁ z₂ z₃ : Row
z₁ = Bool ፦ (ℕ ፦ Lin)
z₂ = (Bool × Bool) ፦ Lin
z₃ = ℕ ፦ (Bool ፦ ((Bool × Bool) ፦ Lin))

z₂≲z₃ : z₂ ≲ z₃
z₂≲z₃ zero = ⟨ suc (suc zero) , refl ⟩

-- injection
Σz₂ : Σ z₂
Σz₂ = ⟨ zero , ⟨ false , true ⟩ ⟩

Σz₃ : Σ z₃
Σz₃ = inj z₂ z₃ z₂≲z₃ Σz₂

-- Projection
Πz₃ : Π z₃
Πz₃ zero             =  1
Πz₃ (suc zero)       = true
Πz₃ (suc (suc zero)) = ⟨ false , true ⟩

Πz₂ : Π z₂
Πz₂ = prj z₂ z₃ z₂≲z₃ Πz₃




