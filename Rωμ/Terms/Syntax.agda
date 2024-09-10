module Rωμ.Terms.Syntax where

open import Preludes.Level
open import Preludes.Relation

open import Rωμ.Kinds
open import Rωμ.Types
import Rωμ.Types as Types
open import Rωμ.Types.Substitution
open import Rωμ.Equivalence.Syntax
open import Rωμ.Entailment.Syntax
open import Rωμ.GVars.Kinds

--------------------------------------------------------------------------------
-- Environments.

data Env : KEnv → Set where
  ε : Env Δ
  _،_ : Env Δ → Type Δ ★ → Env Δ

infixl 5 _،_
-- Weakening of the kinding env.
weakΓ : Env Δ → Env (Δ ، κ)
weakΓ ε = ε
weakΓ (Γ ، τ) = weakΓ Γ ، rename S τ

private
  variable
    Γ : Env Δ

--------------------------------------------------------------------------------
-- Variables.

data Var : Env Δ → Type Δ κ → Set where
  Z : ∀ {Γ : Env Δ} {τ : Type Δ ★} →
      Var (Γ ، τ) τ
  S : ∀ {Γ : Env Δ}
        {τ : Type Δ ★} {υ : Type Δ ★} →
         Var Γ υ → Var (Γ ، τ) υ
private
  variable
    τ : Type Δ ★
    τ₁ : Type Δ ★
    τ₂ : Type Δ ★
    τ₃ : Type Δ ★
    τ₄ : Type Δ ★
    τ₅ : Type Δ ★

S² : Var Γ τ → Var (Γ ، τ₁ ، τ₂) τ
S³ : Var Γ τ → Var (Γ ، τ₁ ، τ₂ ، τ₃) τ
S⁴ : Var Γ τ → Var (Γ ، τ₁ ، τ₂ ، τ₃ ، τ₄) τ
S⁵ : Var Γ τ → Var (Γ ، τ₁ ، τ₂ ، τ₃ ، τ₄ ، τ₅) τ

S² x = S (S x)
S³ x = S (S² x)
S⁴ x = S (S³ x)
S⁵ x = S (S⁴ x)


--------------------------------------------------------------------------------
-- Synonyms, used later.

SynT : (κ : Kind) → (ρ : Type Δ R[ κ ]) →
       (φ : Type Δ (κ `→ ★)) → Type Δ (★ )
SynT κ ρ φ =
  `∀ L (`∀ κ (`∀ R[ κ ] ((l R▹ u) · y ~ ρ' ⇒
    (⌊ l ⌋ `→ φ' ·[ u ]))))
    where
      ρ' = weaken (weaken (weaken ρ))
      φ' = weaken (weaken (weaken φ))
      y = tvar Z
      u = tvar (S Z)
      l = tvar (S (S Z))

AnaT : (κ : Kind) → (ρ : Type Δ R[ κ ])
       (φ : Type Δ (κ `→ ★)) (τ : Type Δ ★) →
       Type Δ (★ )
AnaT  κ ρ φ τ =
  `∀ L (`∀ κ (((l R▹ u) ≲ K² ρ ⇒
    ⌊ l ⌋ `→ K² φ ·[ u ] `→ K² τ)))
    where
      u = tvar Z
      l = tvar (S Z)

FoldT : ∀ (ρ : Type Δ R[ ★ ]) (υ : Type Δ ★) →
       Type Δ (★ )
FoldT ρ υ =
  `∀ L (`∀ ★ (`∀ R[ ★ ] ((l R▹ t) · y ~ ρ' ⇒
    ⌊ l ⌋ `→ t `→ υ')))
    where
      ρ' = weaken (weaken (weaken ρ))
      υ' = weaken (weaken (weaken υ))
      y = tvar Z
      t = tvar (S Z)
      l = tvar (S (S Z))

--------------------------------------------------------------------------------
-- Terms.

infixl 5 _·_ 

data Term : KEnv → PEnv Δ → Env Δ → Type Δ ★ → Set where
  ------------------------------------------------------------
  -- System Fω.

  var : ∀ {Φ : PEnv Δ} {Γ : Env Δ} {τ : Type Δ ★} →

          Var Γ τ →
          -------------
          Term Δ Φ Γ τ

  `λ : ∀ {Φ : PEnv Δ} {Γ : Env Δ} {υ : Type Δ (★)}

           (τ : Type Δ (★)) → Term Δ Φ (Γ ، τ) υ →
           -------------------------------------
           Term Δ Φ Γ (τ `→ υ)

  _·_ : ∀ {Φ : PEnv Δ} {Γ : Env Δ}
          {τ : Type Δ (★)} {υ : Type Δ (★)} →

          Term Δ Φ Γ (τ `→ υ) → Term Δ Φ Γ τ →
          ----------------------------
          Term Δ Φ Γ υ

  `Λ : ∀ {Φ : PEnv Δ} {Γ : Env Δ}
         (κ : Kind) {τ : Type (Δ ، κ) ★} →

         Term (Δ ، κ) (weakΦ Φ) (weakΓ Γ) τ →
         ----------------------------------------------------
         Term Δ Φ Γ (`∀ κ τ)


  _·[_] : ∀ {Φ : PEnv Δ} {Γ : Env Δ}
            {κ : Kind} {τ : Type (Δ ، κ) ★} →

            Term Δ Φ Γ (`∀ κ τ) → (υ : Type Δ κ) →
            ----------------------------------
            Term Δ Φ Γ (τ β[ υ ])

--   ------------------------------------------------------------
--   -- Qualified types.

  `ƛ : ∀  {Φ : PEnv Δ} {Γ : Env Δ}
          {κ : Kind} {τ : Type Δ ★} →

           (π : Pred Δ κ) → Term Δ (Φ , π) Γ τ →
           -------------------------------------
           Term Δ Φ Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {Φ : PEnv Δ} {Γ : Env Δ}
           {π : Pred Δ κ} {τ : Type Δ ★} →

         Term Δ Φ Γ (π ⇒ τ) → Ent Δ Φ π →
         ----------------------------------
         Term Δ Φ Γ τ

  rowCompl : ∀ {Φ : PEnv Δ} {Γ : Env Δ}
           {ρ₁ ρ₂ : Type Δ R[ κ ]} {τ : Type Δ ★} →

         Ent Δ Φ (ρ₁ ≲ ρ₂) → 
         Term Δ Φ Γ (`∀ R[ κ ] (K ρ₁ · (tvar Z) ~ K ρ₂ ⇒ K τ)) →
         --------------------------------------------------
         Term Δ Φ Γ τ

--   ------------------------------------------------------------
--   -- System Rω.

--   -- labels.
  lab : ∀ {Γ : Env Δ} {Φ : PEnv Δ}

          (l : Type Δ L) →
          ----------------------------------------
          Term Δ Φ Γ (⌊_⌋  l)


--   -- singleton introduction.
  _▹_ : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ L} {υ : Type Δ ★} →
          (M₁ : Term Δ Φ Γ (⌊_⌋  τ)) (M₂ : Term Δ Φ Γ υ) →
          ----------------------------------------
          Term Δ Φ Γ (τ ▹ υ)

--   -- singleton elimination.
  _/_ : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ L} {υ : Type Δ ★} →
          (M₁ : Term Δ Φ Γ (τ ▹ υ)) (M₂ : Term Δ Φ Γ (⌊_⌋  τ)) →
          ----------------------------------------
          Term Δ Φ Γ υ


  -- record introduction.
  _⊹_ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ])} →

          (M : Term Δ Φ Γ (Π ρ₁)) (N : Term Δ Φ Γ (Π ρ₂)) →
          (π : Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃)) →
          ------------------------------
          Term Δ Φ Γ (Π ρ₃)

  -- record "elimination".
  prj : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
        {ρ₁ ρ₂ : Type Δ (R[ ★ ])} →

          (M : Term Δ Φ Γ (Π ρ₁)) → (π : Ent Δ Φ (ρ₂ ≲ ρ₁)) →
          ------------------------------
          Term Δ Φ Γ (Π ρ₂)

  -- Singleton → Singleton Record.
  Π : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ L} {υ : Type Δ ★} →

          Term Δ Φ Γ (τ ▹ υ) →
          ---------------------
          Term Δ Φ Γ (Π (τ R▹ υ))

  -- Singleton Record → Singleton.
  Π⁻¹ : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ L} {υ : Type Δ ★} →

          (M : Term Δ Φ Γ (Π (τ R▹ υ))) →
          ----------------------------------------
          Term Δ Φ Γ (τ ▹ υ)

  -- Subsumption.
  t-≡ : ∀ {Φ : PEnv Δ} {Γ : Env Δ}
          {τ υ : Type Δ ★}  →

          τ ≡t υ → (M : Term Δ Φ Γ τ) →
          ----------------------------
          Term Δ Φ Γ υ

  -- Variant introduction.
  inj : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
          {ρ₁ ρ₂ : Type Δ (R[ ★ ])} →

          (M : Term Δ Φ Γ (Σ ρ₁)) → (Ent Δ Φ (ρ₁ ≲ ρ₂)) →
          ----------------------------------------------
          Term Δ Φ Γ (Σ ρ₂)

  -- Singleton Record → Singleton.
  Σ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ L} {υ : Type Δ ★} →

          Term Δ Φ Γ (τ ▹ υ) →
          ---------------------
          Term Δ Φ Γ (Σ (τ R▹ υ))

  -- Singleton Variant → Singleton.
  Σ⁻¹ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ L} {υ : Type Δ ★} →

          (M : Term Δ Φ Γ (Σ (τ R▹ υ))) →
          ----------------------------------------
          Term Δ Φ Γ (τ ▹ υ)

  -- Variant elimination.
  _▿_ : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
        {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ])} {τ : Type Δ ★} →

          Term Δ Φ Γ ((Σ ρ₁) `→ τ) →
          Term Δ Φ Γ ((Σ ρ₂) `→ τ) →
          Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
          ------------------------------
          Term Δ Φ Γ ((Σ ρ₃) `→ τ)

  -- Synthesis.
  syn : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} {κ : Kind}

          (ρ : Type Δ R[ κ ]) →
          (φ : Type Δ (κ `→ ★)) →
          Term Δ Φ Γ (SynT κ ρ φ) →
          --------------------------
          Term Δ Φ Γ (Π (φ ↑ ·[ ρ ]))

  -- Analysis.
  ana : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} {κ : Kind}

         (ρ : Type Δ R[ κ ]) →
         (φ : Type Δ (κ `→ ★)) →
         (τ : Type Δ ★) →
         Term Δ Φ Γ (AnaT κ ρ φ τ) →
         --------------------------
         Term Δ Φ Γ (Σ (φ ↑ ·[ ρ ]) `→ τ)

  -- Fold.
  fold : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
         {ρ : Type Δ R[ ★ ]} {υ : Type Δ (★)} →

         (M₁ : Term Δ Φ Γ (FoldT ρ υ)) →
         (M₂ : Term Δ Φ Γ (υ `→ (υ `→ υ))) →
         (M₃ : Term Δ Φ Γ υ) →
         (N  : Term Δ Φ Γ (Π ρ)) →
         ------------------------
         Term Δ Φ Γ υ

  ------------------------------------------------------------
  -- System Rωμ.

  In : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
         {F : Type Δ ((★) `→ (★))} →

         Term Δ Φ Γ (F ·[ μ F ]) → Term Δ Φ Γ (Functor ·[ F ]) →
         ------------------------------------------------
         Term Δ Φ Γ (μ F)

  Out : ∀ {Γ : Env Δ} {Φ : PEnv Δ}
         {F : Type Δ ((★) `→ (★))} →

         Term Δ Φ Γ (μ F) → Term Δ Φ Γ (Functor ·[ F ]) →
         ----------------------
         Term Δ Φ Γ (F ·[ μ F ])

  fix :  {Γ : Env Δ} {Φ : PEnv Δ}
         {τ : Type Δ ★} →

         ----------------------------
         Term Δ Φ Γ ((τ `→ τ) `→ τ)
