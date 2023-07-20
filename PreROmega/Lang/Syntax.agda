module PreROmega.Lang.Syntax where

open import Data.String using (String)
open import Data.Nat using (ℕ ; suc)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Function using (_∘_)

open import Data.List 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

-- Our stuff
open import PreROmega.Lib.AssocList
open import PreROmega.Lib.Atom

--------------------------------------------------------------------------------
-- Kinds κ ::= * | L | R[κ] | κ → κ

infix 10 R[_]
infixr 25 _`→_


data Kind : Set where
  ★ : Kind
  L : Kind
  R[_] : Kind → Kind
  _`→_ : Kind → Kind → Kind


--------------------------------------------------------------------------------=
{-
   Types τ, ζ ::= α | τ → τ | π ⇒ τ | ∀ α:κ.τ | λ α:κ. τ | τ τ
                  ℓ | ⌊τ⌋ | τ ▷ τ | Π ζ | Σ ζ
   Predicates ::= ζ ≤ ζ | ζ ⊕ ζ ~ ζ -}
   
infix 6 _▹_
infix 6 _⇒_
infix 10 _·_
infix 10 _≲_
infix 6 _·_~_

-- Declare Type and then open Row.
data Type : Set
-- open Row Type

Label : Set
Label = String

Types : Set
Types = List Type

data Pred : Set
Preds : Set
Preds = List Pred

data Type where
 bvar : ℕ → Type             
 fvar  : Atom → Type
 _`→_   : Type → Type → Type
 _⇒_    : Pred → Type → Type
 `∀     : Kind → Type → Type
 `λ     : Kind → Type → Type
 _·_   : Type → Type → Type
 ℓ     : Label → Type
 ⌊_⌋    : Type → Type
 _▹_   : Type → Type → Type
 Π      : Type → Type
 Σ      : Type → Type
 -- Unit type. For testing.
 O      : Type

data Pred where
  _≲_     : Type → Type → Pred
  _·_~_   : Type → Type → Type → Pred

--------------------------------------------------------------------------------
-- Free variables of a LN representation are simply lists of atoms.
-- TODO: Use finite sets rather than Lists?

fv : Type → Atoms
fvπ : Pred → Atoms

fv (bvar x) = []
fv (fvar a) = [ a ]
fv (t₁ `→ t₂) = fv t₁ ++ fv t₂
fv (p ⇒ t) = fvπ p ++ fv t
fv (`∀ k t) = fv t
fv (`λ k t) = fv t
fv (t₁ · t₂) = fv t₁ ++ fv t₂
fv (ℓ l) = []
fv ⌊ t ⌋ = fv t
fv (t₁ ▹ t₂) = fv t₁ ++ fv t₂
fv (Π t) = fv t
fv (Σ t) = fv t
fv O = []

fvπ (t₁ ≲ t₂) = fv t₁ ++ fv t₂
fvπ (t₁ · t₂ ~ t₃) = fv t₁ ++ fv t₂ ++ fv t₃

--------------------------------------------------------------------------------
-- Opening types (LN)

_^ₜ_at_ : Type → Type → ℕ → Type
_^π_at_ : Pred → Type → ℕ → Pred

t@(bvar j) ^ₜ u at k with k Data.Nat.≟ j
... | yes k=j = u
... | no  k≠j = t
t@(fvar _) ^ₜ u at k = t
(t₁ `→ t₂) ^ₜ u at k =  (t₁ ^ₜ u at k) `→ (t₂ ^ₜ u at k)
(p ⇒ t) ^ₜ u at k    = (p ^π u at k) ⇒ (t ^ₜ u at k)
(`∀ κ t) ^ₜ u at k   = `∀ κ (t ^ₜ u at (suc k))
(`λ κ t) ^ₜ u at k   = `λ κ (t ^ₜ u at (suc k))
(t₁ · t₂) ^ₜ u at k  =  (t₁ ^ₜ u at k) ·  (t₂ ^ₜ u at k)
t@(ℓ _) ^ₜ u at k    = t
⌊ t ⌋ ^ₜ u at k      = ⌊  (t ^ₜ u at k) ⌋
(t₁ ▹ t₂) ^ₜ u at k  =  t₁ ^ₜ u at k ▹  t₂ ^ₜ u at k
(Π t) ^ₜ u at k       = Π ( t ^ₜ u at k)
(Σ t) ^ₜ u at k       = Σ ( t ^ₜ u at k)
O ^ₜ u at k       = O


(z ≲ z') ^π u at k       =  z ^ₜ u at k ≲  z' ^ₜ u at k
(z₁ · z₂ ~ z₃) ^π u at k =  z₁ ^ₜ u at k ·  z₂ ^ₜ u at k ~ (z₃ ^ₜ u at k)

-- In practice, we open from the outermost binding, 0. So we can short-hand:
infix 5 _^ₜ_
_^ₜ_ : Type → Type → Type
t₁ ^ₜ t₂ = t₁ ^ₜ t₂ at 0

--------------------------------------------------------------------------------
-- Cofinite quantification
--
-- This pops up everywhere in the locally nameless representation.  We can save
-- ourselves some eye-ball strain with this helper.

-- cofinite quantification says: For any given list, if I give you a fresh
-- variable w.r.t. that list, then the proposition P a holds. This is one of
-- those numerous examples in PL where we strengthen our assumptions in order to
-- get a stronger IH. See:
-- https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc/STLC_Tutorial.html
-- where cofinite quantification is necessary for the substitution lemma.

cofinite : Atoms → (Atom → Set) → Set
cofinite l P = (∀ a → a ∉ l → P a)

--------------------------------------------------------------------------------
-- Environments

data Binding : Set where
  BindK : Kind → Binding
  BindT : Type → Binding
  BindP : Pred → Binding

Env : Set
Env = List (Atom × Binding)

ε : Env
ε = []

_⦂ₖ_ : Atom → Kind → (Atom × Binding)
_⦂ₜ_ : Atom → Type → (Atom × Binding)
_⦂π_ : Atom → Pred → (Atom × Binding)
a ⦂ₖ k = ⟨ a , BindK k ⟩
x ⦂ₜ t = ⟨ x , BindT t ⟩
a ⦂π p = ⟨ a , BindP p ⟩
--------------------------------------------------------------------------------
-- Terms M, N ::= x ∣ ℓ ∣ λx:τ.M ∣ M N ∣ Λa:k. M ∣ M [τ]
--              ∣ M ▹ M ∣ M/M ∣ prj M ∣ M ⊹ M ∣ inj M ∣ M ▿ M
--              ∣ syn φ M ∣ ana φ M ∣ fold M M M M

-- TODO: I have defined only terms.
-- We will likely need to impose local closure &c restructions.

data Term : Set where
  bvar  : ℕ → Term
  fvar  : Atom → Term
  ℓ     : Label → Term
  `λ    : Type → Term → Term
  _·_   : Term → Term → Term
  `Λ    : Kind → Term → Term
  _·[_] : Term → Type → Term
  _▹_   : Term → Term → Term
  _/_   : Term → Term → Term
  prj   : Term → Term
  _⊹_   : Term → Term → Term
  inj   : Term → Term
  _▿_   : Term → Term → Term
  syn   : Type → Term → Term
  ana   : Type → Term → Term
  fold  : Term → Term → Term → Term → Term
  -- Unit type. For testing.
  o     : Term

--------------------------------------------------------------------------------
-- Term opening.
-- (Still may have problems.)
-- Consider
--   (Λ X : ★. (λ x : X. x))[ ℓ "l" ]
-- Will this reduce to
--   (λ x : ℓ "l". x) ?

data Subst : Set where
  term : Term → Subst
  type : Type → Subst

_^_at_ : Term → Subst → ℕ → Term
o ^ u at k = o
t@(bvar j) ^ (term M) at k with k Data.Nat.≟ j
... | yes k=j = M
... | no  k≠j = t
t@(bvar j) ^ u@(type _) at k = t
t@(fvar _) ^ _ at _          = t
t@(ℓ _) ^ _ at _             = t
(`λ v t) ^ u@(term M) at k   = `λ v (t ^ u at (suc k))
(`λ v t) ^ u@(type t') at k   = `λ (v ^ₜ t' at (suc k)) (t ^ u at (suc k))
(t₁ · t₂) ^ u at k           = (t₁ ^ u at k) · (t₂ ^ u at k)
(`Λ v t₁) ^ u at k           = `Λ v (t₁ ^ u at (suc k))
(t ·[ X ]) ^ u@(term M) at k = (t ^ u at k) ·[ X ]
(t ·[ X ]) ^ u@(type t') at k = (t ^ u at k) ·[ X ^ₜ  t' ]
(t₁ ▹ t₂) ^ u at k           = (t₁ ^  u at k) ▹ (t₂ ^  u at k)
(t₁ / t₂) ^ u at k           = (t₁ ^ u at k) / (t₂ ^ u at k)
(prj t) ^ u at k             = prj (t ^ u at k)
(t₁ ⊹ t₂) ^ u at k           = (t₁ ^ u at k) ⊹ (t₂ ^ u at k)
(inj t) ^ u at k             = inj (t ^ u at k)
(t₁ ▿ t₂) ^ u at k           = (t₁ ^ u at k) ▿ (t₂ ^ u at k)
(syn φ t) ^ u at k           = syn φ (t ^ u at k)
(ana φ t) ^ u at k           = ana φ (t ^ u at k)
(fold t₁ t₂ t₃ t₄) ^ u at k  =
  fold (t₁ ^ u at k) (t₂ ^ u at k) (t₃ ^ u at k) (t₄ ^ u at k)

-- -- -- In practice, we open from the outermost binding, 0. So we can short-hand:
infix 5 _^_
_^_ : Term → Term → Term
M ^ N = M ^ (term N) at 0

-- Because of Λ and ·[_], types exist in terms.
-- So we must also support substitution of types within terms.
_^'_ : Term → Type → Term
M ^' t = M ^ (type t) at 0

