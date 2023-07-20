module PreROmega.Semantics.Denotational where

open import Level
open import Data.String using (String; _≟_)
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List 
open import Data.Empty using (⊥;⊥-elim)
open import Data.Unit using (⊤;tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ₚ;tt to ttₚ)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.List.Relation.Unary.Any
open import Data.List.Properties
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties
-- open import Data.List.Membership.DecPropositional
--   renaming (_∈?_ to _∈L_)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary using (Decidable)
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

open import PreROmega.Lib.AssocList
open import PreROmega.Lib.Atom

open import PreROmega.Lang.Syntax
open import PreROmega.Lang.Typing

open import Data.Fin.Base
open PreROmega.IndexCalculus

--------------------------------------------------------------------------------
-- Lemmas & Theorems. Left as postulates.

postulate
  k-regularity : ∀ {Γ t k} → Γ ⊢ₖ t ⦂ k → ⊢ₑ Γ
  t-regularity : ∀ {Γ M t} → Γ ⊢ₜ M ⦂ t → ⊢ₑ Γ
  ≡ₜ-soundness : ∀ {Γ t₁ t₂ k} →
                 Γ ⊢ₖ t₁ ⦂ k → t₁ ≡ₜ t₂ → Γ ⊢ₖ t₂ ⦂ k
  -- I cannot progress very far without an un-opaque def'n of this lemma.
  --
  -- It is used in t2k, which is used in the type-level reduction of the definition:
  --     ⟦_⟧ₜ : ∀ {Γ M t} →
  --          (d : Γ ⊢ₜ M ⦂ t) → ⟦ (t2k d) ⟧⊢ₖ
  -- So this will not reduce until t2k may reduce, which may not reduce for
  -- anything using t-→I, as the t-→ case needs strengthening.      
  ⊢strengthening : ∀ {Γ a t₁ t₂ k} →
                   ((a ⦂ₜ t₁) ∷ Γ) ⊢ₖ t₂ ⦂ k → Γ ⊢ₖ t₂ ⦂ k
--------------------------------------------------------------------------------
-- We postulate bot to reduce holes. Obviously, will remove later.

lone = Level.suc Level.zero
data ⊥₁ : Set lone where

postulate
  bot : ⊥
  bot₁ : ⊥₁

whatever : ∀ {A : Set} → A
whatever = ⊥-elim bot

⊥-elim₁ : ∀ {A : Set lone} → ⊥₁ → A
⊥-elim₁ ()

whatever₁ : ∀ {A : Set lone} → A
whatever₁ {A} = ⊥-elim₁ bot₁

-- Also want ⊤ at level 1.
⊤₁ = ⊤ₚ {lone}
tt₁ : ⊤₁
tt₁ = Level.lift tt
--------------------------------------------------------------------------------
-- The meaning of predicates.
⟦_⟧π : Pred → Env → Set₁
⟦ t₁ Pred.≲ t₂ ⟧π Γ = ⊥₁
⟦ x Pred.· x₁ ~ x₂ ⟧π Γ = ⊥₁

--------------------------------------------------------------------------------
-- The meaning of kinds.
⟦_⟧ₖ : Kind → Set₁
⟦ ★ ⟧ₖ        = Set
⟦ L ⟧ₖ        = ⊤₁
⟦ R[ _ ] ⟧ₖ   = Row
⟦ t₁ `→ t₂ ⟧ₖ = ⟦ t₁ ⟧ₖ → ⟦ t₂ ⟧ₖ

--------------------------------------------------------------------------------
-- The meaning of bindings & environments.
-- Mutually recursive with the meaning of types and kinds.
⟦_⟧⊢ₖ : ∀ {Γ t k} →
       (d : Γ ⊢ₖ t ⦂ k) →
       ⟦ k ⟧ₖ

t2k : ∀ {Γ M t} →
      Γ ⊢ₜ M ⦂ t → Γ ⊢ₖ t ⦂ ★

⟦_⟧ₜ : ∀ {Γ M t} →
      (d : Γ ⊢ₜ M ⦂ t) → ⟦ (t2k d) ⟧⊢ₖ

-- Need to scratch head here. But it's not important for now.
⟦_⟧⊢π : ∀ {Γ p} →
       (d : Γ ⊢π p) → ⟦ p ⟧π Γ

⟦_⟧⊢π d = whatever₁

-- I am starting to suspect I have added a un-well-founded loop between
-- environments and the meaning of kinding derivations.
-- What is the meaning of
--   ((a ⦂ k) ∷ Γ) ⊢ₖ a ⦂ k?
-- And, What is the meaning
--   of ((a ⦂ k) ∷ Γ)?
data ⟦Binding⟧ : Set₁ where
  ⟦BindK⟧ : ∀ (k : Kind) → (d : ⟦ k ⟧ₖ) → ⟦Binding⟧
  ⟦BindT⟧ : ∀ (t : Type) → ⟦ ★ ⟧ₖ → ⟦Binding⟧
  ⟦BindP⟧ : ∀ Γ (p : Pred) → ⟦ p ⟧π Γ → ⟦Binding⟧

⟦Env⟧ = List (Atom × ⟦Binding⟧)

-- TODO:
-- rework this to use Data.List map?
-- So that dom-preservation is a proof over the map, not the list.
⟦_⟧ₑ : ∀ {Γ : Env} → ⊢ₑ Γ → ⟦Env⟧
⟦ c-emp ⟧ₑ = []
⟦ d@(c-tvar Γ a k ⊢Γ a∉domΓ) ⟧ₑ = ⟨ a , ⟦BindK⟧ k {!!} ⟩ ∷ ⟦ ⊢Γ ⟧ₑ
⟦ c-var Γ a t ⊢t ⊢Γ _ ⟧ₑ =  ⟨ a , ⟦BindT⟧ t ⟦ ⊢t ⟧⊢ₖ ⟩ ∷ ⟦ ⊢Γ ⟧ₑ 
⟦ c-pred Γ a p ⊢Γ ⊢p x₄ ⟧ₑ =  ⟨ a , ⟦BindP⟧ Γ p ⟦ ⊢p ⟧⊢π ⟩ ∷ ⟦ ⊢Γ ⟧ₑ

postulate
  -- should be "simple induction", or, consequence of some List theorem.
  dom-preservationₖ : ∀ Γ (a : Atom) (d : ⊢ₑ Γ) (k : Kind) →
                     (a ⦂ₖ k ∈ Γ) →
                     ∃[ ⟦k⟧ ] ⟨ a , ⟦BindK⟧ k ⟦k⟧ ⟩ ∈ ⟦ d ⟧ₑ

--------------------------------------------------------------------------------
-- The meaning of a kinding derivation.

⟦ k-var Γ a k ⊢Γ a∈Γ ⟧⊢ₖ with dom-preservationₖ Γ a ⊢Γ k a∈Γ 
... | ⟨ ⟦k⟧ , f ⟩ = {!!}

⟦ k-→ _ t₁ t₂ ⊢t₁ ⊢t₂ ⟧⊢ₖ  = ⟦ ⊢t₁ ⟧⊢ₖ → ⟦ ⊢t₂ ⟧⊢ₖ 
⟦ k-⇒ Γ p t L' ⊢πp cof ⟧⊢ₖ =  whatever₁ -- ⟦ cof x (fresh∉ L') ⟧⊢ₖ σ'
--   where
--     x = fresh L'
--     x∉L' = fresh∉ L'
⟦ k-∀ _ k t L₁ x ⟧⊢ₖ       = whatever₁
⟦ k-→I _ k₁ k₂ t L₁ x ⟧⊢ₖ  = λ _ → whatever₁
⟦ k-→E  ⊢t ⊢t₂ ⟧⊢ₖ            = ⟦ ⊢t ⟧⊢ₖ ⟦ ⊢t₂ ⟧⊢ₖ
⟦ k-lab _ l₁ ⟧⊢ₖ           = ttₚ
⟦ k-lty _ t₁ t₂ _ _ ⊢t₂ ⟧⊢ₖ = ⟦ ⊢t₂ ⟧⊢ₖ
⟦ k-sing _ t ⊢ₖt ⟧⊢ₖ         = ⊤
⟦ k-row _ t₁ t₂ k c c₁ ⟧⊢ₖ = whatever₁
⟦ k-Π _ z _ c ⟧⊢ₖ          = whatever₁
⟦ k-Σ _ z _ c ⟧⊢ₖ          = whatever₁
⟦ k-lift₁ c c₁ ⟧⊢ₖ         = whatever₁
⟦ k-lift₂ c c₁ ⟧⊢ₖ         = whatever₁
⟦ k-O ⟧⊢ₖ = ⊤

--------------------------------------------------------------------------------
--The meaning of a typing derivation Γ ⊢ M ⦂ t.
t2k (t-var _ a _ ⊢Γ x∈Γ) = whatever
t2k (t-sing Γ l') = k-sing Γ (ℓ l') (k-lab Γ l')
t2k (t-→I Γ M t₁ t₂ L' ⊢ₖt₁ ⊢ₜM) =
  k-→ Γ t₁ t₂ ⊢ₖt₁  (⊢strengthening (t2k (⊢ₜM a a∉L')))
    where
      a    = fresh L'
      a∉L' = fresh∉ L'
t2k (t-→E _ M₁ M₂ t₁ t₂ ⊢M₁ ⊢M₂) = whatever
t2k (t-⇒I _ p _ t L₁ x x₄) = whatever
t2k (t-⇒E _ p _ _ d x) = whatever
t2k (t-∀I _ M t k L₁ x) = whatever
t2k (t-∀E _ M t v k d x) = whatever
t2k (t-▹I Γ M₁ M₂ t₁ t₂ ⊢M₁ ⊢M₂) with t2k ⊢M₁
... | k-sing _ _ ⊢t₁ = k-lty Γ t₁ t₂ ★ ⊢t₁ (t2k ⊢M₂)
-- ... | ⟨ l , t₁≡ₜℓl ⟩ = k-lty Γ t₁ t₂ ★ (≡ₜ-soundness ⊢l (≡ₜsym t₁≡ₜℓl )) (t2k ⊢M₂)
--   where
--     ⊢l : Γ ⊢ₖ ℓ l ⦂ L
--     ⊢l = k-lab Γ l
t2k (t-▹E _ M₁ M₂ t₁ t₂ ⊢M₁ ⊢M₂) with t2k ⊢M₁
... | k-lty _ .t₁ _ .★ _ ⊢t₂ = ⊢t₂
t2k (t-ΠE _ M p₁ p₂ d x) = whatever
t2k (t-ΠI _ M₁ M₂ p₁ p₂ p₃ d d₁ x) = whatever
t2k (t-ΣI _ M p₁ p₂ d x) = whatever
t2k (t-ΣE _ M₁ M₂ p₁ p₂ p₃ t d d₁ x) = whatever
t2k (t-≡ _ _ t _ d x) = whatever
t2k (t-ana _ M z φ t k x x₄ d) = whatever
t2k (t-syn _ M z φ k x x₄ d) = whatever
t2k (t-fold _ M₁ M₂ M₃ N z t _ k d d₁ d₂ d₃) = whatever
t2k t-o = k-O

⟦ t-var _ x _ x₄ x₅ ⟧ₜ = whatever
⟦ t-sing _ _ ⟧ₜ = tt 
⟦ t-→I _ M t₁ t₂ L₁ ⊢ₖt₁ ⊢ₜM ⟧ₜ ⟦⊢ₖt₁⟧ = whatever
⟦ t-→E _ M₁ M₂ t₁ _ d d₁ ⟧ₜ  = whatever
⟦ t-⇒I _ p _ t L₁ x x₄ ⟧ₜ  = whatever
⟦ t-⇒E _ p _ _ d x ⟧ₜ  = whatever
⟦ t-∀I _ M t k L₁ x ⟧ₜ = whatever
⟦ t-∀E _ M t v k d x ⟧ₜ = whatever
⟦ t-▹I Γ M₁ M₂ t₁ t₂ ⊢M₁ ⊢M₂ ⟧ₜ with t2k (t-▹I Γ M₁ M₂ t₁ t₂ ⊢M₁ ⊢M₂) | t2k ⊢M₁
... | k-lty _ _ _ .★ _ _ | k-sing _ _ _ = ⟦ ⊢M₂ ⟧ₜ
⟦ t-▹E _ M₁ M₂ t₁ t₂ ⊢M₁ ⊢M₂ ⟧ₜ with t2k ⊢M₁
... | k-lty _ .t₁ _ .★ ⊢l₁ ⊢t = whatever
⟦ t-ΠE _ M p₁ p₂ d x ⟧ₜ = whatever
⟦ t-ΠI _ M₁ M₂ p₁ p₂ p₃ d d₁ x ⟧ₜ = whatever
⟦ t-ΣI _ M p₁ p₂ d x ⟧ₜ = whatever
⟦ t-ΣE _ M₁ M₂ p₁ p₂ p₃ t d d₁ x ⟧ₜ = whatever
⟦ t-≡ _ _ t _ d x ⟧ₜ = whatever
⟦ t-ana _ M z φ t k x x₄ d ⟧ₜ = whatever
⟦ t-syn _ M z φ k x x₄ d ⟧ₜ = whatever
⟦ t-fold _ M₁ M₂ M₃ N z t _ k d d₁ d₂ d₃ ⟧ₜ = whatever
⟦ t-o ⟧ₜ = tt
  
--------------------------------------------------------------------------------
-- Vertical, try 2.

open import PreROmega.Lang.Examples

-- The unit type in Rω translates to the unit type in Ix.
⟦o⟧ : ⊤
⟦o⟧ = ⟦ t-o {ε} ⟧ₜ


o-id : Term
o-id = `λ O x₀

⊢o-id : ε ⊢ₜ o-id ⦂ (O `→ O)
⊢o-id =
  t-→I ε x₀ O O [] k-O
  (λ a a∉[] → t-var (⟨ a , BindT O ⟩ ∷ []) a O
    (c-var [] a O k-O c-emp a∉[])
    (here refl))

-- This is stuck until I have transparent def'n of
-- strengthening.
-- ⟦⊢o-id⟧ : ⊤ → ⊤
-- ⟦⊢o-id⟧ = ⟦ ⊢o-id ⟧ₜ

--------------------------------------------------------------------------------
-- Labels (as base types)

⟦ell⟧ : ⊤
⟦ell⟧ = ⟦ ⊢ell ⟧ₜ

--------------------------------------------------------------------------------
-- Let's look at the meat of our development:
-- singletons, products, and variants.

s : Term
s = (ℓ "k" ▹ o)

s' : Type
s' = (ℓ "k" ▹ O)

-- -- singleton introduction
⊢sI : ε ⊢ₜ s ⦂ s'
⊢sI = t-▹I ε (ℓ "k") o (ℓ "k") O (t-sing ε "k") t-o

⟦⊢sI⟧ : ⊤
⟦⊢sI⟧ = ⟦ ⊢sI ⟧ₜ

_ : ⟦⊢sI⟧ ≡ tt
_ = refl

--------------------------------------------------------------------------------
-- Singleton elimination (stripping)
-- N.B. Broken. May point to a flaw in type system. Deferred for now.

-- ⊢sE : ε ⊢ₜ s / (ℓ "k") ⦂ O
-- ⊢sE = t-▹E ε s (ℓ "k") (ℓ "k") O ⊢sI (t-sing ε "k")

-- ⟦⊢sE⟧ : ⊤
-- ⟦⊢sE⟧ = ⟦ ⊢sE ⟧ₜ 

-- _ : ⟦⊢sE⟧ ≡ tt
-- _ = refl

--------------------------------------------------------------------------------
-- 


