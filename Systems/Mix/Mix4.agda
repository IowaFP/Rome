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
  𝓟 : Symbol
  𝓣 : Symbol
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
  ⟪_,_⟫ : Symbol → Symbol → Symbol
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
  𝓟 : Sort 𝓟
  𝓣 : Sort 𝓣

-- (Wish this were less verbose, but I believe we are forced to discriminate in
-- each case.)
sort? : (s : Symbol) → Dec (Sort s)
sort? 𝓟 = yes 𝓟
sort? 𝓣 = yes 𝓣
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
sort? ⟪ s , s₁ ⟫ = no (λ ())
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

data _⊢_⦂_ where
  𝓟 : Δ ⊢ 𝓟 ⦂ 𝓣
  --
  ⊤ : ∀ {σ} → Δ ⊢ ⊤ ⦂ σ
  tt : Δ ⊢ tt ⦂ ⊤
  --
  -- (This is blatantly wrong; will do proper var nonsense later.)
  var : ∀ {τ} (n : ℕ) → Δ ⊢ var n ⦂ τ
  --
  Nat : ∀ {σ} → Δ ⊢ Nat ⦂ σ
  Zero : Δ ⊢ Zero ⦂ Nat
  Suc : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Suc n ⦂ Nat
  --
  Ix  : ∀ {σ}{n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Ix n ⦂ σ
  --
  FZero : ∀ {n} → Δ ⊢ Ix n ⦂ 𝓟 → Δ ⊢ FZero ⦂ Ix n
  FSuc  : ∀ {n} → Δ ⊢ Ix n ⦂ 𝓟 → Δ ⊢ FSuc n ⦂ Ix (Suc n) 
  --
  Π : ∀ {τ υ σ σ'} → (t : Δ ⊢ τ ⦂ σ) → {_ : True (sort? σ)} {_ : True (sort? σ')} → (Δ , t) ⊢ υ ⦂ σ' → Δ ⊢ (Π τ υ) ⦂ σ'
  `λ : ∀ {τ υ σ M} → (t : Δ ⊢ τ ⦂ σ) → (Δ , t) ⊢ M ⦂ υ  → Δ ⊢ `λ τ M ⦂ Π τ υ 
  _·_ : ∀ {τ υ M N} → Δ ⊢ M ⦂ Π τ υ → Δ ⊢ N ⦂ τ  → Δ ⊢ M · N ⦂ υ
  --
  Σ : ∀ {τ υ σ σ'} → (t : Δ ⊢ τ ⦂ σ) → {_ : True (sort? σ)} {_ : True (sort? σ')} → (Δ , t) ⊢ υ ⦂ σ' → Δ ⊢ (Σ τ υ) ⦂ σ'
  ⟪_,_⟫ : ∀ {τ υ σ σ'} → (t : Δ ⊢ τ ⦂ σ) → (Δ , t) ⊢ υ ⦂ σ' → Δ ⊢ ⟪ τ , υ ⟫ ⦂ Σ τ σ'
  fst : ∀ {τ M σ} → Δ ⊢ M ⦂ Σ τ σ → Δ ⊢ (fst M) ⦂ τ
  snd : ∀ {τ M σ} → (s : Δ ⊢ M ⦂ Σ τ σ) → (Δ , fst s) ⊢ (snd M) ⦂ σ

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
  ⟦ ★ ⟧σ = 𝓣
  ⟦ L ⟧σ = 𝓟
  ⟦ R[ κ ] ⟧σ = 𝓣
  ⟦ κ `→ κ₁ ⟧σ = 𝓟

  -- read as "the translation of κ to type ⟦ κ ⟧κ"
  ⟦_⟧κ : (κ : Rμ.Kind) →  Symbol
  ⟦ ★ ⟧κ = 𝓟
  ⟦ L ⟧κ = ⊤
  ⟦ R[ κ ] ⟧κ = Row ⟦ κ ⟧κ
  ⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ

  ⟦_⟧ρ : ∀ {Δ}{κ} → Rμ.Type Δ (R[ κ ])  → Symbol
  ⟦ ε ⟧ρ = ⟪ (Suc Zero) , ⊤ ⟫
  ⟦ tvar x ⟧ρ = 𝓟
  ⟦ ρ ·[ ρ₁ ] ⟧ρ = 𝓟
  ⟦ ρ ▹ ρ₁ ⟧ρ = ⟦ ρ₁ ⟧ρ
  ⟦ ρ R▹ ρ₁ ⟧ρ = 𝓟
  ⟦ ρ ·⌈ ρ₁ ⌉ ⟧ρ = ⟦ ρ ⟧ρ
  ⟦ ⌈ ρ ⌉· ρ₁ ⟧ρ = ⟦ ρ₁ ⟧ρ

  ⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Symbol
  ⟦ U ⟧τ = ⊤
  ⟦ tvar x ⟧τ = 𝓟
  --
  ⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ ⟦ τ₂ ⟧τ
  ⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
  ⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ ⟦ τ ⟧τ
  ⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
  --
  ⟦ lab l ⟧τ = tt
  ⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
  ⟦ _ R▹ τ ⟧τ = ⟪ (Suc Zero) , ⟦ τ ⟧τ ⟫
  ⟦ ⌊ τ ⌋ ⟧τ = tt
  ⟦_⟧τ {Δ} ε = ⟦_⟧ρ {Δ} ε
  ⟦ Π ρ ⟧τ = Π (Ix (fst ⟦ ρ ⟧ρ)) ((snd ⟦ ρ ⟧ρ) · (var 0))
  ⟦ Σ ρ ⟧τ = Σ (Ix (fst ⟦ ρ ⟧ρ)) ((snd ⟦ ρ ⟧ρ) · (var 0))
  ⟦ τ ·⌈ τ₁ ⌉ ⟧τ = ⟦ τ₁ ⟧τ
  ⟦ ⌈ τ ⌉· τ₁ ⟧τ = ⟦ τ₁ ⟧τ
  --
  ⟦ π ⇒ τ ⟧τ = ⟦ τ ⟧τ
  --
  ⟦ μ τ ⟧τ = ⟦ τ ⟧τ
  ⟦ ν τ ⟧τ = ⟦ τ ⟧τ

  ⟦_⟧ : ∀ {Δ}{Γ}{Φ}{τ} → Rμ.Term Δ Γ Φ τ → Symbol
  ⟦ M ⟧ = {!!}

--------------------------------------------------------------------------------
-- Typed translation of kinds.

⟦_⟧κ : ∀ {Δ} → (κ : Rμ.Kind) → Δ ⊢ Sym.⟦ κ ⟧κ ⦂ 𝓣
⟦ ★ ⟧κ = 𝓟
⟦ L ⟧κ = ⊤ -- ⊤₁
-- Σ (n : Nat). Π (i : Ix n). 𝓟
-- Σ (n : Nat). Π (i : Ix n). Π (p : 𝓟). 𝓟

⟦ R[ κ ] ⟧κ = Σ (Nat {σ = 𝓟}) (Π (Ix {σ = 𝓟} (var 0)) ⟦ κ ⟧κ)
⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ (weaken ⟦ κ₂ ⟧κ) -- 

-- --------------------------------------------------------------------------------
-- -- Typed translation of contexts.
⟦_⟧Δ : Rμ.KEnv → Context
⟦ ε ⟧Δ = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- --------------------------------------------------------------------------------
-- -- Typed translation of types.

⟦_⟧τ : ∀ {Δ}{κ} → (τ : Rμ.Type Δ κ) → ⟦ Δ ⟧Δ ⊢ Sym.⟦ τ ⟧τ  ⦂ Sym.⟦ κ ⟧κ

⟦ U ⟧τ = ⊤
⟦ tvar x ⟧τ = {!!}
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ (weaken ⟦ τ₂ ⟧τ)
⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
--
⟦ lab l ⟧τ = tt
⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ _ R▹ τ ⟧τ = {!⟪_,_ !}
⟦ ⌊ τ ⌋ ⟧τ = {!!}
⟦ ε ⟧τ = {!!}
⟦ Π τ ⟧τ = Π {!!} ({!!} · (var 0))
⟦ Σ τ ⟧τ = Σ {!!} ({!!} · (var 0))
⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
--
⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}
--
⟦ π ⇒ τ ⟧τ = {!!}

-- --------------------------------------------------------------------------------
-- -- Examples.
  
-- pfft : Δ ⊢ Nat ⦂ 𝓟
-- pfft = Nat₀

-- next : Δ ⊢ Π Nat Nat ⦂ 𝓟
-- next = Π Nat₀ Nat₀

-- type : Δ ⊢ Π 𝓟 𝓟 ⦂ 𝓣
-- type = Π 𝓟 𝓟

-- term : Δ ⊢ `λ Nat Zero ⦂ Π Nat Nat
-- term = `λ Nat₀ Zero

-- _ : Δ ⊢ (`λ Nat Zero) · Zero ⦂ Nat
-- _ = (`λ Nat₀ Zero) · Zero



