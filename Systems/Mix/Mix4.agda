module Mix.Mix4 where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

open import Data.Nat using (_⊔_)


-- =============================================================================
-- Symbols, i.e., the untyped syntax.
-- (There is no point in having a term/type distinction.)
-- =============================================================================

data Symbol : Set where
  ★ : Symbol
  𝓤 : Symbol
  --
  var : ℕ → Symbol
  -- 
  Nat  : Symbol
  Zero : Symbol
  Suc  : Symbol → Symbol
  --
  Ix   : Symbol → Symbol
  FZero : Symbol
  FSuc : Symbol → Symbol
  --
  ⊤ : Symbol
  tt : Symbol
  -- 
  Π : Symbol → Symbol → Symbol
  `λ : Symbol → Symbol → Symbol
  _·_ : Symbol → Symbol → Symbol
  --
  Σ : (τ : Symbol) → Symbol → Symbol
  ⟪_⦂_,_⟫ : Symbol → Symbol → Symbol → Symbol
  fst : Symbol → Symbol
  snd : Symbol → Symbol
  --
  _Or_ : Symbol → Symbol → Symbol
  left : Symbol → Symbol
  right : Symbol → Symbol
  case_of[_]or[_] : Symbol → Symbol → Symbol → Symbol
  --
  _~_ : Symbol → Symbol → Symbol
  refl : Symbol
  Sub : Symbol → Symbol → Symbol

-- TD: don't use s for var names here
rename : Symbol → Symbol
rename ★ = ★
rename 𝓤 = 𝓤
rename (var x) = var (suc x)
rename Zero = Zero
rename (Suc s) = Suc (rename s)
rename (Ix s) = Ix (rename s)
rename FZero = FZero
rename (FSuc s) = FSuc (rename s)
rename ⊤ = ⊤
rename tt = tt
rename (Π s s₁) = Π (rename s) (rename s₁)
rename (`λ s s₁) = `λ (rename s) (rename s₁)
rename (s · s₁) = (rename s) · (rename s₁)
rename (Σ s s₁) = Σ (rename s) (rename s₁)
rename ⟪ s ⦂ s₁ , s₂ ⟫ = ⟪ rename s ⦂ rename s₁ , rename s₂ ⟫
rename (fst s) = fst (rename s)
rename (snd s) = snd (rename s)
rename (s Or s₁) = rename s Or rename s₁
rename (left s) = left (rename s)
rename (right s) = right (rename s)
rename case s of[ s₁ ]or[ s₂ ] = case (rename s) of[ rename s₁ ]or[ rename s₂ ]
rename (s ~ s₁) = rename s ~ rename s₁
rename refl = refl
rename (Sub s s₁) = Sub (rename s) (rename s₁)
rename Nat = Nat

-- =============================================================================
-- Formation and typing rules. 
-- =============================================================================
-- 
-- ... are the same judgement.
--     Δ ⊢ τ ⦂ σ
-- is a kinding judgment when the predicate `Sort σ` holds;
--         Δ ⊢ M ⦂ τ
-- is is the translation of a typing judgement otherwise.

--------------------------------------------------------------------------------
-- Declare contexts and judgements.
-- (mutually recursive.)
data Context : Set
data _⊢_⦂_ : Context → Symbol → Symbol → Set

data Context where
  ε : Context
  _,_ : ∀ {M}{τ} → (Δ : Context) → Δ ⊢ M ⦂ τ → Context

private
  variable
    Δ : Context 

--------------------------------------------------------------------------------
-- Sorts (and decision procedure).

data Sort : Symbol → Set where
  ★ : Sort ★
  𝓤 : Sort 𝓤

-- (Wish this were less verbose, but I believe we are forced to discriminate in
-- each case.)
sort? : (s : Symbol) → Dec (Sort s)
sort? ★ = yes ★
sort? 𝓤 = yes 𝓤
sort? (var x) = no (λ ())
sort? Nat = no (λ ())
sort? Zero = no (λ ())
sort? (Suc s) = no (λ ())
sort? (Ix s) = no (λ ())
sort? FZero = no (λ ())
sort? (FSuc s) = no (λ ())
sort? ⊤ = no (λ ())
sort? tt = no (λ ())
sort? (Π s s₁) = no (λ ())
sort? (`λ s s₁) = no (λ ())
sort? (s · s₁) = no (λ ())
sort? (Σ s s₁) = no (λ ())
sort? ⟪ a ⦂ b , c ⟫ = no (λ ())
sort? (fst s) = no (λ ())
sort? (snd s) = no (λ ())
sort? (s Or s₁) = no (λ ())
sort? (left s) = no (λ ())
sort? (right s) = no (λ ())
sort? case s of[ s₁ ]or[ s₂ ] = no (λ ())
sort? (s ~ s₁) = no (λ ())
sort? refl = no (λ ())
sort? (Sub s s₁) = no (λ ())


--------------------------------------------------------------------------------
-- Typing judgements.

data Var : ∀ {Δ' σ τ} → (Δ : Context) → Δ' ⊢ τ ⦂ σ → Set where
  Z : ∀ {Δ} {τ σ}{⊢τ : Δ ⊢ τ ⦂ σ} →
        Var (Δ , ⊢τ) ⊢τ

  -- S : ∀ {Δ Δ'} {τ υ} →
  --     Var {Δ'} Δ τ → Var (Δ , υ) τ

data _⊢_⦂_ where
  ★ : Δ ⊢ ★ ⦂ 𝓤
  --
  ⊤ : ∀ {σ} → Sort σ →  Δ ⊢ ⊤ ⦂ σ
  tt : Δ ⊢ tt ⦂ ⊤
  --
  varZ : ∀ {τ σ} {⊢τ : Δ ⊢ τ ⦂ σ}  → (Δ , ⊢τ) ⊢ (var 0) ⦂ τ
  -- varS : ∀ {τ σ υ}{n} {⊢υ : Δ ⊢ υ ⦂ σ} →
  --           Δ ⊢ (var n) ⦂ τ
  --        → (Δ , ⊢υ) ⊢ (var (suc n)) ⦂ τ
  --
  Nat : Δ ⊢ Nat ⦂ ★
  Zero : Δ ⊢ Zero ⦂ Nat
  Suc : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Suc n ⦂ Nat
  --
  Ix  : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Ix n ⦂ ★
  --
  FZero : ∀ {n} → Δ ⊢ Ix n ⦂ ★ → Δ ⊢ FZero ⦂ Ix n
  FSuc  : ∀ {n} → Δ ⊢ Ix n ⦂ ★ → Δ ⊢ FSuc n ⦂ Ix (Suc n) 
  --
  Π : ∀ {τ υ σ σ'} → -- {_ : True (sort? σ)}
        (t : Δ ⊢ τ ⦂ σ)   →   (Δ , t) ⊢ υ ⦂ σ' →
        -------------------------------------------
        Δ ⊢ (Π τ υ) ⦂ σ'
  `λ : ∀ {τ υ σ M} → (t : Δ ⊢ τ ⦂ σ) → (Δ , t) ⊢ (rename M) ⦂ υ  → Δ ⊢ `λ τ M ⦂ Π τ υ 
  _·_ : ∀ {τ υ M N} → Δ ⊢ M ⦂ Π τ υ → Δ ⊢ N ⦂ τ  → Δ ⊢ M · N ⦂ υ
  --
  Σ : ∀ {τ υ σ σ'} → -- {_ : True (sort? σ)}
        (t : Δ ⊢ τ ⦂ σ)   →   (Δ , t) ⊢ υ ⦂ σ' → 
        ------------------------------------------
        Δ ⊢ (Σ τ υ) ⦂ σ'
  ⟪_⦂_,_⟫ : ∀ {τ υ σ σ₁ σ₂} → (Δ ⊢ τ ⦂ σ₁) → (t : Δ ⊢ σ₁ ⦂ σ₂) → (Δ , t) ⊢ υ ⦂ σ → Δ ⊢ ⟪ τ ⦂ σ₁ , υ ⟫ ⦂ Σ σ₁ σ
  fst : ∀ {τ M σ} → Δ ⊢ M ⦂ Σ τ σ → Δ ⊢ (fst M) ⦂ τ
  snd : ∀ {τ M σ} → (s : Δ ⊢ M ⦂ Σ τ σ) → Δ ⊢ (snd M) ⦂ σ

postulate
  weaken : ∀ {Δ} {τ υ} {κ₁ κ₂} → {u : Δ ⊢ υ ⦂ κ₁} → Δ ⊢ τ ⦂ κ₂ →  (Δ , u) ⊢ τ ⦂ κ₂

-- =============================================================================
-- Translating Rω.  
-- =============================================================================

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public
 open import Rome.Terms.Syntax public
 open import Rome.Entailment.Syntax public

open Rμ.Kind
open Rμ.KEnv
open Rμ.Type
open Rμ.TVar
open Rμ.Term

Row : Symbol → Symbol
Row s = Σ Nat (Π (Ix (var 0)) s)

--------------------------------------------------------------------------------
-- Translating typed Rω to untyped Mix.
--
-- These "flat" translations become indices to the translation of typed Rω to typed
-- Mix terms.

module Sym where

  -- read as "the translation of κ *has sort* ⟦ κ ⟧σ"
  ⟦_⟧σ : (κ : Rμ.Kind) → Symbol
  ⟦ ★ ⟧σ = 𝓤
  ⟦ L ⟧σ = ★
  ⟦ R[ κ ] ⟧σ = 𝓤
  ⟦ κ `→ κ₁ ⟧σ = ★

  -- read as "the translation of κ to type ⟦ κ ⟧κ"
  ⟦_⟧κ : (κ : Rμ.Kind) →  Symbol
  ⟦ ★ ⟧κ = ★
  ⟦ L ⟧κ = ⊤
  ⟦ R[ κ ] ⟧κ = Row ⟦ κ ⟧κ
  ⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ

  ⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Symbol
  ⟦ U ⟧τ = ⊤
  ⟦_⟧τ {.(_ , κ)} {κ} (tvar Z) = var 0 -- ⟦ κ ⟧κ
  ⟦_⟧τ {.(_ , _)} (tvar (S x)) = ⟦ tvar x ⟧τ
  --
  ⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ ⟦ τ₂ ⟧τ
  ⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
  ⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ ⟦ τ ⟧τ
  ⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
  --
  ⟦ lab l ⟧τ = tt
  ⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
  ⟦ _ R▹ τ ⟧τ = ⟪ Suc Zero ⦂ Nat , `λ (Ix (var 0)) ⟦ τ ⟧τ ⟫
  ⟦ ⌊ τ ⌋ ⟧τ = ⊤
  ⟦_⟧τ {Δ} ε = ⟪ Zero ⦂ Nat ,  `λ (Ix (var 0)) ⊤ ⟫
  ⟦ Π ρ ⟧τ = Π (Ix (fst ⟦ ρ ⟧τ)) ((snd ⟦ ρ ⟧τ) · var 0)
  ⟦ Σ ρ ⟧τ = Σ (Ix (fst ⟦ ρ ⟧τ)) ((snd ⟦ ρ ⟧τ) · var 0)
  ⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
  ⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
  --
  ⟦ π ⇒ τ ⟧τ = {!!}
  --
  ⟦ μ τ ⟧τ = {!!}
  ⟦ ν τ ⟧τ = {!!}

  ⟦_⟧ : ∀ {Δ}{Γ}{Φ}{τ} → Rμ.Term Δ Γ Φ τ → Symbol
  ⟦ M ⟧ = {!!}

--------------------------------------------------------------------------------
-- Typed translation of kinds.

⟦_⟧κ : ∀ {Δ} → (κ : Rμ.Kind) → Δ ⊢ Sym.⟦ κ ⟧κ ⦂ 𝓤
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ⊤ 𝓤
⟦ R[ κ ] ⟧κ = Σ Nat (Π (Ix varZ) ⟦ κ ⟧κ) 
⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ (weaken ⟦ κ₂ ⟧κ) 

-- --------------------------------------------------------------------------------
-- -- Typed translation of contexts.
⟦_⟧Δ : Rμ.KEnv → Context
⟦ ε ⟧Δ = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- --------------------------------------------------------------------------------
-- -- Typed translation of types.

⟦_⟧v : ∀ {Δ}{κ} → (v : Rμ.TVar Δ κ) → ⟦ Δ ⟧Δ ⊢ Sym.⟦ (tvar v) ⟧τ ⦂ Sym.⟦ κ ⟧κ
⟦ Z ⟧v = varZ
⟦ S v ⟧v = {!!}

⟦_⟧τ : ∀ {Δ}{κ} → (τ : Rμ.Type Δ κ) → ⟦ Δ ⟧Δ ⊢ Sym.⟦ τ ⟧τ  ⦂ Sym.⟦ κ ⟧κ

⟦ U ⟧τ = ⊤ ★
⟦ tvar x ⟧τ = ⟦ x ⟧v
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ (weaken ⟦ τ₂ ⟧τ)
⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ {!!} -- ⟦ τ ⟧τ
⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
--
⟦ lab l ⟧τ = tt
⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ _ R▹ τ ⟧τ = ⟪ (Suc Zero) ⦂ Nat , `λ (Ix varZ) (weaken (weaken {!!})) ⟫ -- ⟪ (Suc Zero) ⦂ Nat , (Π (Ix varZ) {!⟦ τ ⟧τ!}) ⟫ 
⟦ ⌊ τ ⌋ ⟧τ = ⊤ ★
-- I need to actually do substitution.
⟦ ε ⟧τ = ⟪ Zero ⦂ Nat , `λ (Ix varZ) (⊤ ★) ⟫
-- I need renaming in symbol expressions.
⟦ Π τ ⟧τ = Π (Ix (fst ⟦ τ ⟧τ)) (snd (weaken (⟦ τ ⟧τ)) · {!varZ!})
⟦ Σ τ ⟧τ = Σ {!!} ({!!} · {!!})
⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}

⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}

⟦ π ⇒ τ ⟧τ = {!!}

--------------------------------------------------------------------------------
-- Examples.
  
-- pfft : Δ ⊢ Nat ⦂ ★
-- pfft = Nat₀

-- next : Δ ⊢ Π Nat Nat ⦂ ★
-- next = Π Nat₀ Nat₀

-- type : Δ ⊢ Π ★ ★ ⦂ 𝓤
-- type = Π ★ ★

-- term : Δ ⊢ `λ Nat Zero ⦂ Π Nat Nat
-- term = `λ Nat₀ Zero

-- _ : Δ ⊢ (`λ Nat Zero) · Zero ⦂ Nat
-- _ = (`λ Nat₀ Zero) · Zero



