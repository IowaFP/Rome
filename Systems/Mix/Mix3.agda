module Mix.Mix3 where

open import Preludes.Data
open import Data.List
open import Preludes.Relation
open import Data.Nat using (_⊔_)


----------------------------------------------------------------------------------
--

data Sort : Set where
  𝓤₁    : Sort
  𝓤₀    : Sort

data Context : Set

private
  variable
    Δ : Context
    σ : Sort

data Type : Context → Sort → Set 
data Term : (Δ : Context) → Type Δ σ → Set 

data Context where
  ε : Context
  _,_ : ∀ (Δ : Context){s : Sort} → Type Δ s → Context  

-- There is no point in having a term/type distinction, atm.
data Type where
  ★ : Type Δ 𝓤₁
  -- 
  Nat  : Type Δ σ
  Ix   : Term Δ Nat → Type Δ σ
  -- --
  ⊤ : Type Δ σ
  Π : (τ : Type Δ σ) → Type (Δ , τ) σ → Type Δ σ
  Σ : (τ : Type Δ σ) → Type (Δ , τ) σ → Type Δ σ
  _Or_ : Type Δ  σ → Type Δ σ → Type Δ σ
  _~_ : Type Δ σ → Type Δ σ → Type Δ σ
  -- As ★ : ★, all terms are also well-formed types.
  inst : (τ : Type Δ σ) → Term Δ τ → Type Δ σ

data _⊢_⦂_ : {σ σ' : Sort} (Δ : Context) → Type Δ σ → Type Δ σ' → Set where
  ★ : Δ ⊢ ★ 



postulate
  weaken   : ∀ {τ : Type Δ σ} → Type Δ σ → Type (Δ , τ) σ
  -- subst-τ   : ∀ {τ υ : Type Δ} → Type (Δ , υ) → Type (Δ , τ)
  -- subst   : ∀ {τ υ : Type Δ σ} → Term (Δ , υ) (weaken τ) → Term Δ υ → Term Δ τ

data Term where
  -- vars.
  var : ∀ {υ} → ℕ → Term Δ υ
  -- Nat intro/elim.
  Zero : Term Δ Nat
  Suc  : Term Δ Nat → Term Δ Nat
  -- Ix intro/elim.
  FZero : Term Δ (Ix (Suc Zero))
  FSuc  : (n : Term Δ Nat) → Term Δ (Ix n) → Term Δ (Ix (Suc n)) 
  -- ⊤ intro.
  tt : Term Δ ⊤
  -- Π intro/elim.
  `λ : (τ : Type Δ 𝓤₀) {υ : Type (Δ , τ) 𝓤₀} → (u : Term (Δ , τ) υ) → Term Δ (Π τ υ)
  _·_ : {τ : Type Δ 𝓤₀} {υ : Type (Δ , τ) 𝓤₀} → Term Δ (Π τ υ) → Term Δ τ → Term (Δ , τ) υ    
  -- Σ intro/elim.
  ⟪_,_⟫ : {τ : Type Δ σ} {υ : Type (Δ , τ) σ} → Term Δ τ → Term (Δ , τ) υ → Term Δ (Σ τ υ) 
  fst : {τ : Type Δ σ} {υ : Type (Δ , τ) σ} → Term Δ (Σ τ υ) → Term Δ τ
  snd : {τ : Type Δ σ} {υ : Type (Δ , τ) σ} → Term Δ (Σ τ υ) → Term (Δ , τ) υ
  -- Coproducts intro/elim.
  left : {τ υ : Type Δ σ} → Term Δ τ → Term Δ (τ Or υ)
  right : {τ υ : Type Δ σ} → Term Δ υ → Term Δ (τ Or υ)
  case_of[_]or[_] : {τ υ A : Type Δ σ} →
                    Term Δ (τ Or υ) →  Term (Δ , τ) (weaken A) → Term (Δ , υ) (weaken A) →
                    Term Δ A
  -- Eq intro/elim.
  refl : ∀ {t : Type Δ σ} {τ : Term Δ t} → Term Δ (t ~ t)
  -- N.b... This *is not* eq elimination---but do we need it?
  Sub    : ∀ {τ υ : Type Δ σ} → Term Δ τ → Term Δ (τ ~ υ) → Term Δ υ
-- -- --------------------------------------------------------------------------------
-- -- -- Semantics.

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

postulate
  weakenTerm : ∀ {τ υ : Type Δ σ} → Term Δ υ → Term (Δ , τ) (weaken υ)

row  : (Type Δ σ) → Type Δ σ
row τ = Σ Nat (Π (Ix (var 0)) (weaken (weaken τ)))
  
⟦_⟧Δ : Rμ.KEnv → Context
⟦_⟧κ : (κ : Rμ.Kind) →  Type Δ 𝓤₁
⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Type ⟦ Δ ⟧Δ 𝓤₀
⟦_⟧ρ : ∀ {Δ}{κ} → Rμ.Type Δ (R[ κ ])  → Term ⟦ Δ ⟧Δ (⟦ R[ κ ] ⟧κ)
⟦ tvar x ⟧ρ = {!!}
⟦ ρ ·[ ρ₁ ] ⟧ρ = {!!}
⟦ ρ ▹ ρ₁ ⟧ρ = {!!}
⟦ ρ R▹ ρ₁ ⟧ρ = {!!}
⟦ ε ⟧ρ = {!!}
⟦ ρ ·⌈ ρ₁ ⌉ ⟧ρ = {!!}
⟦ ⌈ ρ ⌉· ρ₁ ⟧ρ = {!!}
-- ⟦_⟧P : ∀ {Δ}{κ} → Rμ.Pred Δ κ  → Type ⟦ Δ ⟧Δ
-- ⟦_⟧π : ∀ {Δ}{κ}{Φ : Rμ.PEnv Δ}{π : Rμ.Pred Δ κ} → Rμ.Ent Δ Φ π  → Term ⟦ Δ ⟧Δ ⟦ π ⟧P
-- ⟦_⟧ : ∀ {Δ}{Φ : Rμ.PEnv Δ}{Γ : Rμ.Env Δ} {τ : Rμ.Type Δ ★} → Rμ.Term Δ Φ Γ τ  → Term ⟦ Δ ⟧Δ ⟦ τ ⟧τ

--------------------------------------------------------------------------------
-- Translation of kinds to (higher-sorted) types.

⟦ ★ ⟧κ        = ★
⟦ L ⟧κ        = ⊤ 
⟦ R[ κ ] ⟧κ   = Σ Nat (Π (Ix (var 0)) ⟦ κ ⟧κ)
⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ



-- -- --------------------------------------------------------------------------------
-- -- -- Translation of (kinding) environments.
⟦ ε ⟧Δ     = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- --------------------------------------------------------------------------------
-- -- Translation of types to types.

-- -- units and labels.
⟦ U ⟧τ = ⊤
⟦ ⌊ τ ⌋ ⟧τ = ⊤
⟦ lab l ⟧τ = ⊤
-- Row bits.
⟦ Π ρ ⟧τ = Π (Ix (fst ⟦ ρ ⟧ρ)) {!!}
⟦ Σ ρ ⟧τ = {!!} -- Σ (Ix (fst ⟦ ρ ⟧ρ)) ★ 
⟦ ℓ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ ℓ R▹ τ ⟧τ = {!!} -- inst (Row ★) ⟪ Zero , `λ (Ix (tvar zero)) {!⟦ τ ⟧τ!} ⟫ -- Might be wrong, but maybe the right idea. Still needs ix discrimination.
⟦ ε ⟧τ = {!!} -- inst (Row ★) ⟦ ε ⟧ρ
⟦ _·⌈_⌉ {Δ} {κ₂ = κ₂} τ₁ τ₂ ⟧τ = {!⟦ τ₁ ⟧ρ!} -- inst (Row {!inst ⟦ τ₁ ⟧ ?!}) {!!} -- Need Row (⟦ κ₂ ⟧κ Δ) 
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
-- Fω bits.
⟦ tvar x ⟧τ = {!!}
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ (weaken ⟦ τ₂ ⟧τ)
⟦_⟧τ (`∀ {Δ} κ τ) = {!!} -- Π (⟦ κ ⟧κ Δ) ⟦ τ ⟧τ 
⟦_⟧τ (`λ {Δ} κ τ) = {!!} --  Π (⟦ κ ⟧κ Δ) ⟦ τ ⟧τ
⟦ τ ·[ υ ] ⟧τ = {!subst-τ τ υ!}
-- qualified types.
⟦ π ⇒ τ ⟧τ = {!!} -- Π ⟦ π ⟧P (weaken ⟦ τ ⟧τ)
-- recursive bits.
⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}


-- -- -- Translation of Terms to terms.
-- -- -- (Is this a mess?)
-- -- ⟦ M ⟧ = {!!}
