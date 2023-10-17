module Mix.Mix2 where

open import Preludes.Data
open import Data.List
open import Preludes.Relation
open import Data.Nat using (_⊔_)


----------------------------------------------------------------------------------
-- N.b. Maybe useful (https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Term.agda)

data Context : Set
data Type : Context → Set 
data Term : (Δ : Context) → Type Δ → Set 

data Context where
  ε : Context
  _,_ : (Δ : Context) → Type Δ → Context

private
  variable
    Δ : Context

-- "types", i.e., formation rules.
data Type where
  -- 
  ★    : Type Δ
  Nat  : Type Δ
  Ix   : Term Δ Nat → Type Δ
  --
  ⊤ : Type Δ
  Π : (τ : Type Δ) → Type (Δ , τ) → Type Δ
  Σ : (τ : Type Δ) → Type (Δ , τ) → Type Δ
  _Or_ : Type Δ → Type Δ → Type Δ
  _~_ : Type Δ → Type Δ → Type Δ
  -- As ★ : ★, all terms are also well-formed types.
  inst : (τ : Type Δ) → Term Δ τ → Type Δ

postulate
  weaken   : ∀ {τ : Type Δ} → Type Δ → Type (Δ , τ)
  -- subst-τ   : ∀ {τ υ : Type Δ} → Type (Δ , υ) → Type (Δ , τ)
  subst   : ∀ {τ υ : Type Δ} → Term (Δ , υ) (weaken τ) → Term Δ υ → Term Δ τ

-- typing rules for "small types". N.b.  terms and types are mutually
-- reclusive. So the Term vs. Type distinction is largely for readability.
data Term where
  -- vars.
  tvar : ∀ {υ} → ℕ → Term Δ υ
  -- Nat intro/elim.
  Zero : Term Δ Nat
  Suc  : Term Δ Nat → Term Δ Nat
  -- Ix intro/elim.
  FZero : Term Δ (Ix (Suc Zero))
  FSuc  : (n : Term Δ Nat) → Term Δ (Ix n) → Term Δ (Ix (Suc n)) 
  -- ⊤ intro.
  tt : Term Δ ⊤
  -- Π intro/elim.
  `λ : (τ : Type Δ) {υ : Type (Δ , τ)} → (u : Term (Δ , τ) υ) → Term Δ (Π τ υ)
  _·_ : {τ : Type Δ} {υ : Type (Δ , τ)} → Term Δ (Π τ υ) → Term Δ τ → Term (Δ , τ) υ    
  -- Σ intro/elim.
  ⟪_,_⟫ : {τ : Type Δ} {υ : Type (Δ , τ)} → Term Δ τ → Term (Δ , τ) υ → Term Δ (Σ τ υ) 
  fst : {τ : Type Δ} {υ : Type (Δ , τ)} → Term Δ (Σ τ υ) → Term Δ τ
  snd : {τ : Type Δ} {υ : Type (Δ , τ)} → Term Δ (Σ τ υ) → Term (Δ , τ) υ
  -- Coproducts intro/elim.
  left : {τ υ : Type Δ} → Term Δ τ → Term Δ (τ Or υ)
  right : {τ υ : Type Δ} → Term Δ υ → Term Δ (τ Or υ)
  case_of[_]or[_] : {τ υ A : Type Δ} →
                    Term Δ (τ Or υ) →  Term (Δ , τ) (weaken A) → Term (Δ , υ) (weaken A) →
                    Term Δ A
  -- Eq intro/elim.
  refl : ∀ {t : Type Δ} {τ : Term Δ t} → Term Δ (t ~ t)
  -- N.b... This *is not* eq elimination---but do we need it?
  Sub    : ∀ {τ υ : Type Δ} → Term Δ τ → Term Δ (τ ~ υ) → Term Δ υ
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
  weakenTerm : ∀ {τ υ : Type Δ} → Term Δ υ → Term (Δ , τ) (weaken υ)

Row  : (Type Δ) → Type Δ
Row τ = Σ Nat (Π (Ix (tvar 0)) (weaken (weaken τ)))
  
⟦_⟧Δ : Rμ.KEnv → Context
⟦_⟧κ : Rμ.Kind → (Δ : Rμ.KEnv) → Type ⟦ Δ ⟧Δ
⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Type ⟦ Δ ⟧Δ
⟦_⟧ρ : ∀ {Δ}{κ} → Rμ.Type Δ (R[ κ ])  → Term ⟦ Δ ⟧Δ (Row (⟦ κ ⟧κ Δ))
⟦_⟧P : ∀ {Δ}{κ} → Rμ.Pred Δ κ  → Type ⟦ Δ ⟧Δ
⟦_⟧ : ∀ {Δ}{Φ : Rμ.PEnv Δ}{Γ : Rμ.Env Δ} {τ : Rμ.Type Δ ★} → Rμ.Term Δ Φ Γ τ  → Term ⟦ Δ ⟧Δ ⟦ τ ⟧τ

⟦ tvar x ⟧ρ = {!!}
⟦ τ ·[ τ₁ ] ⟧ρ = {!!}
⟦ _ ▹ τ ⟧ρ = ⟦ τ ⟧ρ
⟦ _ R▹ τ ⟧ρ = ⟪ (Suc Zero) , `λ (Ix (tvar zero)) {!!} ⟫ -- <-- Need ix elimination & substitution...
⟦ ε ⟧ρ = {!!}
⟦ τ ·⌈ τ₁ ⌉ ⟧ρ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧ρ = {!!}

⟦ ρ₁ Rμ.≲ ρ₂ ⟧P      = {!!}
⟦ ρ₁ Rμ.· ρ₂ ~ ρ₃ ⟧P = {!!}

--------------------------------------------------------------------------------
-- Translation of kinds to types.
⟦ ★ ⟧κ _ =  ★
⟦ L ⟧κ _ = ⊤
⟦ R[ κ ] ⟧κ Δ = Row (⟦ κ ⟧κ Δ)
⟦ κ₁ `→ κ₂ ⟧κ Δ = Π (⟦ κ₁ ⟧κ Δ ) (weaken (⟦ κ₂ ⟧κ Δ))

--------------------------------------------------------------------------------
-- Translation of (kinding) environments.
⟦ ε ⟧Δ     = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ Δ 

--------------------------------------------------------------------------------
-- Translation of types to types.

-- units and labels.
⟦ U ⟧τ = ⊤
⟦ ⌊ τ ⌋ ⟧τ = ⊤
⟦ lab l ⟧τ = inst ⊤ tt
-- Row bits.
⟦ Π ρ ⟧τ = Π (Ix (fst ⟦ ρ ⟧ρ)) ★
⟦ Σ ρ ⟧τ = Σ (Ix (fst ⟦ ρ ⟧ρ)) ★ 
⟦ ℓ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ ℓ R▹ τ ⟧τ = {!!} -- (Not sure here). inst (Row ⟦ τ ⟧τ) ⟪ (Suc Zero) , (`λ (Ix (tvar zero)) {!!}) ⟫ -- <-- need Ix discrimination.
⟦ ε ⟧τ = inst (Row ★) ⟦ ε ⟧ρ
⟦ _·⌈_⌉ {Δ} {κ₂ = κ₂} τ₁ τ₂ ⟧τ = {!⟦ τ₁ ⟧ρ!} -- inst (Row {!inst ⟦ τ₁ ⟧ ?!}) {!!} -- Need Row (⟦ κ₂ ⟧κ Δ) 
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
-- Fω bits.
⟦ tvar x ⟧τ = {!!}
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ (weaken ⟦ τ₂ ⟧τ)
⟦_⟧τ (`∀ {Δ} κ τ) = Π (⟦ κ ⟧κ Δ) ⟦ τ ⟧τ 
⟦_⟧τ (`λ {Δ} κ τ) = Π (⟦ κ ⟧κ Δ) ⟦ τ ⟧τ
⟦ τ ·[ υ ] ⟧τ = {!subst-τ τ υ!}
-- qualified types.
⟦ π ⇒ τ ⟧τ = Π ⟦ π ⟧P (weaken ⟦ τ ⟧τ)
-- recursive bits.
⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}


-- Translation of Terms to terms.
-- (Is this a mess?)
⟦ M ⟧ = {!!}
