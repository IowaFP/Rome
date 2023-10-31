module Mix.Mix4 where

open import Preludes.Data
open import Data.List
open import Preludes.Relation
open import Data.Nat using (_⊔_)


----------------------------------------------------------------------------------
--


-- postulate
--   weaken   : ∀ {τ : Type Δ σ} → Type Δ σ → Type (Δ , τ) σ
  -- subst-τ   : ∀ {τ υ : Type Δ} → Type (Δ , υ) → Type (Δ , τ)
  -- subst   : ∀ {τ υ : Type Δ σ} → Term (Δ , υ) (weaken τ) → Term Δ υ → Term Δ τ

-- There is no point in having a term/type distinction, atm.
data Symbol : Set where
  𝓤₀ : Symbol
  𝓤₁ : Symbol
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


-- private
--   variable
--     Δ : Context

-- ⊢ τ ⦂ σ asserts that τ is a type at sort σ.
-- (Formation rules.)

data Context : Set
data _⊢_⦂_ : Context → Symbol → Symbol → Set

data Context where
  ε : Context
  _,_ : ∀ {M}{τ} → (Δ : Context) → Δ ⊢ M ⦂ τ → Context  

private
  variable
    Δ : Context 

data Sort : Symbol → Set where
  𝓤₀ : Sort 𝓤₀
  𝓤₁ : Sort 𝓤₁


data _⊢_⦂_ where
  𝓤₀ : Δ ⊢ 𝓤₀ ⦂ 𝓤₁
  --
  ⊤₀ : Δ ⊢ ⊤ ⦂ 𝓤₀
  tt : Δ ⊢ tt ⦂ ⊤
  --
  Nat : Δ ⊢ Nat ⦂ 𝓤₀
  Zero : Δ ⊢ Zero ⦂ Nat
  Suc : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Suc n ⦂ Nat
  --
  Ix  : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Ix n ⦂ 𝓤₀
  FZero : ∀ {n} → Δ ⊢ Ix n ⦂ 𝓤₀ → Δ ⊢ FZero ⦂ Ix n
  FSuc  : ∀ {n} → Δ ⊢ Ix n ⦂ 𝓤₀ → Δ ⊢ FSuc n ⦂ Ix (Suc n) 
  --
  Π : ∀ {τ υ σ} → (t : Δ ⊢ τ ⦂ σ) → Sort σ → (Δ , t) ⊢ υ ⦂ σ → Δ ⊢ (Π τ υ) ⦂ σ
  `λ : ∀ {τ υ σ M} → (t : Δ ⊢ τ ⦂ σ) → (Δ , t) ⊢ M ⦂ υ  → Δ ⊢ `λ τ M ⦂ Π τ υ 
  --
  Σ : ∀ {τ υ σ} → (t : Δ ⊢ τ ⦂ σ) → (Δ , t) ⊢ υ ⦂ σ → Δ ⊢ (Σ τ υ) ⦂ σ

  -- Π   : ∀ {M}{s} → (τ : Δ ⊢ M ⦂ τ) → (Δ , τ) ⊢ M ⦂ s
  
  
pfft : Δ ⊢ Nat ⦂ 𝓤₀
pfft = Nat

next : Δ ⊢ Π Nat Nat ⦂ 𝓤₀
next = Π Nat 𝓤₀ Nat

type : Δ ⊢ Π 𝓤₀ 𝓤₀ ⦂ 𝓤₁
type = Π 𝓤₀ 𝓤₁ 𝓤₀

term : Δ ⊢ `λ Nat Zero ⦂ Π Nat Nat
term = `λ Nat Zero





-- data _⊢_⦂_ where


-- Judgement that a term has the type
-- data _⊢_⦂_ : {σ σ' : Sort} (Δ : Context) → Type Δ σ → Type Δ σ' → Set where
--   ★ : Δ ⊢ ★ 

-- data Term where
--   -- vars.
--   var : ∀ {υ} → ℕ → Term υ
--   -- Nat intro/elim.
--   Zero : Term Nat
--   Suc  : Term Nat → Term Nat
--   -- Ix intro/elim.
--   FZero : Term (Ix (Suc Zero))
--   FSuc  : (n : Term Nat) → Term (Ix n) → Term (Ix (Suc n)) 
--   -- ⊤ intro.
--   tt : Term ⊤
--   -- Π intro/elim.
--   `λ : (τ : Type Δ 𝓤₀) {υ : Type (Δ , τ) 𝓤₀} → (u : Term (Δ , τ) υ) → Term (Π τ υ)
--   _·_ : {τ : Type Δ 𝓤₀} {υ : Type (Δ , τ) 𝓤₀} → Term (Π τ υ) → Term τ → Term (Δ , τ) υ    
--   -- Σ intro/elim.
--   ⟪_,_⟫ : {τ : Type Δ σ} {υ : Type (Δ , τ) σ} → Term τ → Term (Δ , τ) υ → Term (Σ τ υ) 
--   fst : {τ : Type Δ σ} {υ : Type (Δ , τ) σ} → Term (Σ τ υ) → Term τ
--   snd : {τ : Type Δ σ} {υ : Type (Δ , τ) σ} → Term (Σ τ υ) → Term (Δ , τ) υ
--   -- Coproducts intro/elim.
--   left : {τ υ : Type Δ σ} → Term τ → Term (τ Or υ)
--   right : {τ υ : Type Δ σ} → Term υ → Term (τ Or υ)
--   case_of[_]or[_] : {τ υ A : Type Δ σ} →
--                     Term (τ Or υ) →  Term (Δ , τ) (weaken A) → Term (Δ , υ) (weaken A) →
--                     Term A
--   -- Eq intro/elim.
--   refl : ∀ {t : Type Δ σ} {τ : Term t} → Term (t ~ t)
--   -- N.b... This *is not* eq elimination---but do we need it?
--   Sub    : ∀ {τ υ : Type Δ σ} → Term τ → Term (τ ~ υ) → Term υ
-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Semantics.

-- module Rμ where
--  open import Rome.Kinds.Syntax public
--  open import Rome.Types.Syntax public
--  open import Rome.Terms.Syntax public
--  open import Rome.Entailment.Syntax public

-- open Rμ.Kind
-- open Rμ.KEnv
-- open Rμ.Type
-- open Rμ.TVar
-- open Rμ.Term

-- postulate
--   weakenTerm : ∀ {τ υ : Type Δ σ} → Term υ → Term (Δ , τ) (weaken υ)

-- row  : (Type Δ σ) → Type Δ σ
-- row τ = Σ Nat (Π (Ix (var 0)) (weaken (weaken τ)))
  
-- ⟦_⟧Δ : Rμ.KEnv → Context
-- ⟦_⟧κ : (κ : Rμ.Kind) →  Type Δ 𝓤₁
-- ⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Type ⟦ Δ ⟧Δ 𝓤₀
-- ⟦_⟧ρ : ∀ {Δ}{κ} → Rμ.Type Δ (R[ κ ])  → Term ⟦ Δ ⟧Δ (⟦ R[ κ ] ⟧κ)
-- ⟦ tvar x ⟧ρ = {!!}
-- ⟦ ρ ·[ ρ₁ ] ⟧ρ = {!!}
-- ⟦ ρ ▹ ρ₁ ⟧ρ = {!!}
-- ⟦ ρ R▹ ρ₁ ⟧ρ = {!!}
-- ⟦ ε ⟧ρ = {!!}
-- ⟦ ρ ·⌈ ρ₁ ⌉ ⟧ρ = {!!}
-- ⟦ ⌈ ρ ⌉· ρ₁ ⟧ρ = {!!}
-- -- ⟦_⟧P : ∀ {Δ}{κ} → Rμ.Pred Δ κ  → Type ⟦ Δ ⟧Δ
-- -- ⟦_⟧π : ∀ {Δ}{κ}{Φ : Rμ.PEnv Δ}{π : Rμ.Pred Δ κ} → Rμ.Ent Δ Φ π  → Term ⟦ Δ ⟧Δ ⟦ π ⟧P
-- -- ⟦_⟧ : ∀ {Δ}{Φ : Rμ.PEnv Δ}{Γ : Rμ.Env Δ} {τ : Rμ.Type Δ ★} → Rμ.Term Φ Γ τ  → Term ⟦ Δ ⟧Δ ⟦ τ ⟧τ

-- --------------------------------------------------------------------------------
-- -- Translation of kinds to (higher-sorted) types.

-- ⟦ ★ ⟧κ        = ★
-- ⟦ L ⟧κ        = ⊤ 
-- ⟦ R[ κ ] ⟧κ   = Σ Nat (Π (Ix (var 0)) ⟦ κ ⟧κ)
-- ⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ



-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Translation of (kinding) environments.
-- ⟦ ε ⟧Δ     = ε
-- ⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- -- --------------------------------------------------------------------------------
-- -- -- Translation of types to types.

-- -- -- units and labels.
-- ⟦ U ⟧τ = ⊤
-- ⟦ ⌊ τ ⌋ ⟧τ = ⊤
-- ⟦ lab l ⟧τ = ⊤
-- -- Row bits.
-- ⟦ Π ρ ⟧τ = Π (Ix (fst ⟦ ρ ⟧ρ)) {!!}
-- ⟦ Σ ρ ⟧τ = {!!} -- Σ (Ix (fst ⟦ ρ ⟧ρ)) ★ 
-- ⟦ ℓ ▹ τ ⟧τ = ⟦ τ ⟧τ
-- ⟦ ℓ R▹ τ ⟧τ = {!!} -- inst (Row ★) ⟪ Zero , `λ (Ix (tvar zero)) {!⟦ τ ⟧τ!} ⟫ -- Might be wrong, but maybe the right idea. Still needs ix discrimination.
-- ⟦ ε ⟧τ = {!!} -- inst (Row ★) ⟦ ε ⟧ρ
-- ⟦ _·⌈_⌉ {Δ} {κ₂ = κ₂} τ₁ τ₂ ⟧τ = {!⟦ τ₁ ⟧ρ!} -- inst (Row {!inst ⟦ τ₁ ⟧ ?!}) {!!} -- Need Row (⟦ κ₂ ⟧κ Δ) 
-- ⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
-- -- Fω bits.
-- ⟦ tvar x ⟧τ = {!!}
-- ⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ (weaken ⟦ τ₂ ⟧τ)
-- ⟦_⟧τ (`∀ {Δ} κ τ) = {!!} -- Π (⟦ κ ⟧κ Δ) ⟦ τ ⟧τ 
-- ⟦_⟧τ (`λ {Δ} κ τ) = {!!} --  Π (⟦ κ ⟧κ Δ) ⟦ τ ⟧τ
-- ⟦ τ ·[ υ ] ⟧τ = {!subst-τ τ υ!}
-- -- qualified types.
-- ⟦ π ⇒ τ ⟧τ = {!!} -- Π ⟦ π ⟧P (weaken ⟦ τ ⟧τ)
-- -- recursive bits.
-- ⟦ μ τ ⟧τ = {!!}
-- ⟦ ν τ ⟧τ = {!!}


-- -- -- -- Translation of Terms to terms.
-- -- -- -- (Is this a mess?)
-- -- -- ⟦ M ⟧ = {!!}
