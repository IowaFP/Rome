module PreROmega.Lang.Examples where

open import Data.String using (String; _≟_)
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List 
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
import Relation.Binary.PropositionalEquality as Eq  

open import Function using (_∘_)

open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

import PreROmega.Lib.Biimplication as Bi
import PreROmega.IndexCalculus

open Bi
  using (_⇔_)
  renaming (Equivalence to E)

-- open import Atom
-- open import Row Type
open import PreROmega.Lib.AssocList
open import PreROmega.Lang.Syntax
open import PreROmega.Lang.Typing hiding (l; y)

--------------------------------------------------------------------------------
-- metavars, for convenience.

x₀ x₁ x₂ x₃ : Term
x₀ = bvar 0
x₁ = bvar 1
x₂ = bvar 2
x₃ = bvar 3

a₀ a₁ a₂ a₃ : Type
a₀ = bvar 0
a₁ = bvar 1
a₂ = bvar 2
a₃ = bvar 3

-- x y z : Term
-- x = fvar 0
-- y = fvar 1
-- z = fvar 2

--------------------------------------------------------------------------------
-- Label introduction (t-sing).
--
-- ℓ "l" : ⌊ℓ "l"⌋
-- l = "l"

l : Term
l = ℓ "l"

⌊l⌋ : Type
⌊l⌋ = ⌊ ℓ "l" ⌋

⊢ell : ε ⊢ₜ l ⦂ ⌊l⌋
⊢ell = t-sing ε "l"

--------------------------------------------------------------------------------=
-- Arrow & var introduction (t-→I & t-var).
--
-- idℓ : ℓ "l" → ℓ "l"
-- idℓ = λ x : ⌊ℓ "l"⌋. x

idℓ : Term
idℓ = `λ ⌊l⌋ x₀

⊢idℓ : ε ⊢ₜ idℓ ⦂ ⌊l⌋ `→ ⌊l⌋
⊢idℓ = t-→I ε x₀ ⌊l⌋ ⌊l⌋ [] ⊢⌊l⌋⦂★ cof
  where
    ⊢⌊l⌋⦂★ = (k-sing [] (ℓ "l") (k-lab [] "l"))
    
    cof : cofinite [] (λ x → ((x ⦂ₜ ⌊l⌋) ∷ ε) ⊢ₜ x₀ ^ fvar x ⦂ ⌊l⌋)
    cof a a∉[] = t-var (⟨ a , BindT ⌊l⌋ ⟩ ∷ []) a ⌊l⌋ wf (here  refl)
      where
        -- N.B. Better to use regularity theorem.
        wf : ⊢ₑ (⟨ a , BindT ⌊l⌋ ⟩ ∷ [])
        wf = c-var [] a ⌊l⌋ ⊢⌊l⌋⦂★ c-emp a∉[]

--------------------------------------------------------------------------------
-- Arrow elimination (t-→E).
--
-- id·l : ⌊ℓ "l"⌋
-- id·l = (λ x : ⌊ℓ "l"⌋. x) l

id·l : Term
id·l = idℓ · l

⊢id·l : ε ⊢ₜ id·l ⦂ ⌊l⌋
⊢id·l = t-→E ε idℓ l ⌊l⌋ ⌊l⌋ ⊢idℓ ⊢ell


--------------------------------------------------------------------------------
-- forall introduction (t-∀I).
-- id : ∀ X : ★. X → X
-- id = Λ X : ★. λ x : X. x

id : Term
id = `Λ ★ (`λ a₁ x₀)


⊢id : ε ⊢ₜ id ⦂ `∀ ★ (a₀ `→ a₀)
⊢id = t-∀I ε (`λ a₁ x₀) (a₀ `→ a₀) ★ [] ⊢λx
  where
  
    ⊢λx : cofinite [] (λ x → ((x ⦂ₖ ★) ∷ ε) ⊢ₜ (`λ a₁ x₀) ^' fvar x ⦂ (a₀ `→ a₀ ^ₜ fvar x))
    ⊢λx a a∉[] = t-→I Γ₀ x₀ (fvar a) (fvar a) [ a ] ⊢ₖa⦂★ ⊢ₜx⦂a
      where
        Γ₀ = ((a ⦂ₖ ★) ∷ ε)
        ⊢Γ₀ : ⊢ₑ Γ₀
        ⊢Γ₀ = c-tvar [] a ★ c-emp a∉[]
        
        ⊢ₖa⦂★ : Γ₀ ⊢ₖ fvar a ⦂ ★
        ⊢ₖa⦂★ = k-var Γ₀ a ★ ⊢Γ₀ (here refl)
        ⊢ₜx⦂a :  cofinite [ a ] (λ x → ((x ⦂ₜ fvar a) ∷ Γ₀) ⊢ₜ x₀ ^ fvar x ⦂ fvar a)
        ⊢ₜx⦂a b b∉Γ₀ = t-var Γ₁ b (fvar a) ⊢Γ₁ (here refl)
          where
            Γ₁ = (b ⦂ₜ fvar a) ∷ Γ₀
            ⊢Γ₁ = c-var Γ₀ b (fvar a) ⊢ₖa⦂★ ⊢Γ₀  b∉Γ₀

--------------------------------------------------------------------------------
-- Forall elimination (t-∀E).
--
-- idl  : ℓ "l" `→ ℓ "l"
-- idl = (Λ X : ★. (λ x : X. x))[ ℓ "l" ]

idl : Term
idl = id ·[ ⌊l⌋ ]

⊢idl : ε ⊢ₜ idl ⦂ (⌊l⌋ `→ ⌊l⌋)
⊢idl = t-∀E ε id (a₀ `→ a₀) ⌊l⌋ ★ ⊢id (k-sing ε (ℓ "l") (k-lab ε "l"))

--------------------------------------------------------------------------------
-- Singleton Introduction (t-▹I) & elimination (t-▹E).

⊢labid : ε ⊢ₜ (l ▹ id) ⦂ (ℓ "l" ▹ (`∀ ★ (a₀ `→ a₀)))
⊢labid = t-▹I ε l id (ℓ "l") (`∀ ★ (a₀ `→ a₀)) ⊢ell ⊢id

⊢lstrip :  ε ⊢ₜ (l ▹ id) / l ⦂ (`∀ ★ (a₀ `→ a₀))
⊢lstrip = t-▹E ε (l ▹ id) l (ℓ "l") (`∀ ★ (a₀ `→ a₀)) ⊢labid ⊢ell

--------------------------------------------------------------------------------
-- Singleton Record introduction (t-▹I) and conversion to Π product using t-≡.

sing : String → String → Term
sing k v = (ℓ k) ▹ o

sing' : String → String → Type
sing' k v = (ℓ k) ▹ O

⊢singΠ : ∀ {Γ} (k v : String) → Γ ⊢ₜ sing k v ⦂ Π (sing' k v)
⊢singΠ {Γ} k v = t-≡ Γ s s' p ⊢s⦂p s≡p
  where
    s = (sing k v)
    s' = sing' k v
    p = Π s'
    
    ⊢s⦂p : Γ ⊢ₜ s ⦂ s'
    ⊢s⦂p = t-▹I Γ (ℓ k) o (ℓ k) O (t-sing Γ k) t-o

    s≡p : s' ≡ₜ p
    s≡p = ≡ₜsym (≡ₜΠ▹ (ℓ k) O)

--------------------------------------------------------------------------------
-- Conversion of singleton record into Σ variant using t-≡.

⊢singΣ : (k v : String) → ε ⊢ₜ sing k v ⦂ Σ (sing' k v)
⊢singΣ k v = t-≡ ε s s' p ⊢s⦂p s≡p
  where
    s = sing k v
    s' = sing' k v
    p = Σ s'
    
    ⊢s⦂p : ε ⊢ₜ s ⦂ s'
    ⊢s⦂p = t-▹I ε (ℓ k) o (ℓ k) O (t-sing ε k) t-o

    s≡p : s' ≡ₜ p
    s≡p = ≡ₜsym (≡ₜΣ▹ (ℓ k) O)

--------------------------------------------------------------------------------
-- Composite Record Introduction (t-ΠI and t-⇒I).

s₁ = sing "k₁" "v₁"
s₁' = sing' "k₁" "v₁"

⊢Πs₁' : ∀ {Γ} → Γ ⊢ₜ s₁ ⦂ Π s₁'
⊢Πs₁' {Γ} = ⊢singΠ {Γ} "k₁" "v₁"

s₂ = sing "k₂" "v₂"
s₂' = sing' "k₂" "v₂"
⊢Πs₂' : ∀ {Γ} → Γ ⊢ₜ s₂ ⦂ Π s₂'
⊢Πs₂' {Γ} = ⊢singΠ {Γ} "k₂" "v₂"

-- Singletons *always* have kind κ or R[ κ ], with v : κ.
⊢ₖsing : ∀ {Γ} (k v : String) → Γ ⊢ₖ (sing' k v) ⦂ R[ ★ ]
⊢ₖsing {Γ} k v = k-row Γ (ℓ k) O ★ (k-lab Γ k) k-O

r : Term
r = `Λ R[ ★ ] (s₁ ⊹ s₂)

-- We are are asserting that (a ⊹ s₂) has type
--   ∀ (a₀ : R[★]). a' · s₂' ~ a₀ ⇒ Π a₀
-- which is what
--   Π (a' ++ s₂')
-- desugars to.
⊢r : ε ⊢ₜ r ⦂ (`∀ R[ ★ ] ((s₁' · s₂' ~ a₀) ⇒ Π a₀)) 
⊢r = t-∀I ε (s₁ ⊹ s₂) ((s₁' · s₂' ~ a₀) ⇒ Π a₀) R[ ★ ] [] ⊢r₀
  where
    ⊢r₀ : cofinite [] (λ x →
           ((x ⦂ₖ R[ ★ ]) ∷ ε) ⊢ₜ (s₁ ⊹ s₂) ^' fvar x ⦂
           ((s₁' · s₂' ~ a₀) ⇒ Π a₀ ^ₜ fvar x))
    ⊢r₀ x x∉[] = t-⇒I Γ₀ ((s₁' · s₂' ~ (fvar x))) (s₁ ⊹ s₂) (Π (fvar x)) [ x ]  ⊢πp ⊢r₁
      where
        p = (s₁' · s₂' ~ fvar x)
        
        Γ₀ = ((x ⦂ₖ R[ ★ ]) ∷ ε)
        ⊢ₑΓ₀ : ⊢ₑ Γ₀
        ⊢ₑΓ₀ = c-tvar ε x R[ ★ ] c-emp x∉[]

        ⊢ₖs₁' : Γ₀ ⊢ₖ s₁' ⦂ R[ ★ ]
        ⊢ₖs₁' = ⊢ₖsing "k₁" "v₁"
        

        ⊢ₖs₂' : Γ₀ ⊢ₖ s₂' ⦂ R[ ★ ]
        ⊢ₖs₂' = ⊢ₖsing "k₂" "v₂"
        

        ⊢πp : Γ₀ ⊢π p
        ⊢πp = ⊢π· Γ₀ s₁' s₂' (fvar x) ★ ⊢ₖs₁' ⊢ₖs₂' (k-var Γ₀ x R[ ★ ] ⊢ₑΓ₀ (here refl))

        ⊢r₁ : cofinite [ x ] (λ y →
              ((y ⦂π p) ∷ Γ₀) ⊢ₜ (s₁ ⊹ s₂) ^ fvar y ⦂ (Π (fvar x) ^ₜ fvar y))
        ⊢r₁ y y∉[x] = t-ΠI Γ₁ s₁ s₂ s₁' s₂' (fvar x) ⊢Πs₁' ⊢Πs₂' ⊩p
          where
            Γ₁ = ((y ⦂π p) ∷ Γ₀)
            ⊢ₑΓ₁ : ⊢ₑ Γ₁
            ⊢ₑΓ₁ = c-pred Γ₀ y p ⊢ₑΓ₀ ⊢πp y∉[x]

            ⊩p : Γ₁ ⊩ p
            ⊩p = ⊩var Γ₁ y p ⊢ₑΓ₁ (here refl)

--------------------------------------------------------------------------------
-- Composite Record Elimination (t-ΠE) and further projection (t-▹E) using (t-≡).

-- (skipping this, as I can't project out of r directly... And I don't need
-- further records to play with in Denotational.agda).
-- prja' : ε ⊢ₜ prj r ⦂ Π a'
-- prja' = t-ΠE ε r (`∀ R[ ★ ] ((a' · b' ~ a₀) ⇒ Π a₀)) a' {!⊢r!} {!!}

--------------------------------------------------------------------------------
-- Variant introduction (t-ΣI) and elimination (t-ΣE).

-- (Is this also difficult/impossible/silly without the runtime typing rules?)

-- inja : ε ⊢ₜ inj a ⦂ (`∀ R[ ★ ] ((a' · b' ~ a₀) ⇒ Σ a₀))
-- inja = {!!}

--------------------------------------------------------------------------------
-- ana

--------------------------------------------------------------------------------
-- syn

--------------------------------------------------------------------------------
-- fold

-- =============================================================================
-- examples from paper

--------------------------------------------------------------------------------
-- eqΣ

--------------------------------------------------------------------------------
-- sel

--------------------------------------------------------------------------------
-- con

--------------------------------------------------------------------------------
-- case

--------------------------------------------------------------------------------
-- reify

--------------------------------------------------------------------------------
-- reflect

--------------------------------------------------------------------------------
-- Iter, map, etc

--------------------------------------------------------------------------------
-- 
