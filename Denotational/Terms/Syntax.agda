module Rome.Denotational.Terms.Syntax where

open import Rome.Preludes.Level
open import Rome.Preludes.Relation

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types
import Rome.Denotational.Types as Types
open import Rome.Denotational.Types.Substitution
open import Rome.Denotational.Equivalence.Syntax
open import Rome.Denotational.Entailment.Syntax
open import Rome.Denotational.GVars.Kinds

--------------------------------------------------------------------------------
-- Environments.

data Env : KEnv ℓ → Level → Set where
  ε : Env Δ lzero
  _،_ : Env Δ ℓΓ → Type Δ (★ ℓ) → Env Δ (ℓΓ ⊔ ℓ)

infixl 5 _،_
-- Weakening of the kinding env.
weakΓ : Env Δ ℓΓ → Env (Δ ، κ) ℓΓ
weakΓ ε = ε
weakΓ (Γ ، τ) = weakΓ Γ ، rename S τ

private
  variable
    Γ : Env Δ ℓΓ

--------------------------------------------------------------------------------
-- Variables.

data Var : Env Δ ℓΓ → Type Δ κ → Set where
  Z : ∀ {Γ : Env Δ ℓΓ} {τ : Type Δ (★ ℓ)} →
      Var (Γ ، τ) τ
  S : ∀ {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓ)} {υ : Type Δ (★ ι)} →
         Var Γ υ → Var (Γ ، τ) υ
private
  variable
    τ : Type Δ (★ ℓ)
    τ₁ : Type Δ (★ ℓ)
    τ₂ : Type Δ (★ ℓ)
    τ₃ : Type Δ (★ ℓ)
    τ₄ : Type Δ (★ ℓ)
    τ₅ : Type Δ (★ ℓ)

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

SynT : (κ : Kind ℓκ) → (ρ : Type Δ R[ κ ]) →
       (φ : Type Δ (κ `→ ★ ℓκ)) → Type Δ (★ (lsuc ℓκ))
SynT κ ρ φ =
  `∀ (L lzero) (`∀ κ (`∀ R[ κ ] ((l R▹ u) · y ~ ρ' ⇒
    (⌊_⌋ {ℓ = lzero} l `→ φ' ·[ u ]))))
    where
      ρ' = weaken (weaken (weaken ρ))
      φ' = weaken (weaken (weaken φ))
      y = tvar Z
      u = tvar (S Z)
      l = tvar (S (S Z))

AnaT : (κ : Kind ℓκ) → (ρ : Type Δ R[ κ ])
       (φ : Type Δ (κ `→ ★ ℓκ)) (τ : Type Δ (★ ℓ)) →
       Type Δ (★ (ℓ ⊔ lsuc ℓκ))
AnaT  κ ρ φ τ =
  `∀ (L lzero) (`∀ κ (((l R▹ u) ≲ K² ρ ⇒
    ⌊_⌋ {ℓ = lzero} l `→ K² φ ·[ u ] `→ K² τ)))
    where
      u = tvar Z
      l = tvar (S Z)

FoldT : (ρ : Type Δ R[ ★ ℓκ ]) (υ : Type Δ (★ ℓ)) →
       Type Δ (★ (ℓ ⊔ lsuc ℓκ))
FoldT {ℓκ = ℓκ} ρ υ =
  `∀ (L lzero) (`∀ (★ ℓκ) (`∀ R[ ★ ℓκ ] ((l R▹ t) · y ~ ρ' ⇒
    ⌊_⌋ {ℓ = lzero} l `→ t `→ υ')))
    where
      ρ' = weaken (weaken (weaken ρ))
      υ' = weaken (weaken (weaken υ))
      y = tvar Z
      t = tvar (S Z)
      l = tvar (S (S Z))

--------------------------------------------------------------------------------
-- Terms.

infixl 5 _·_ 

data Term : KEnv ℓΔ → PEnv Δ ℓΦ → Env Δ ℓΓ → Type Δ (★ ℓ) → Set where
  ------------------------------------------------------------
  -- System Fω.

  var : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ} {τ : Type Δ (★ ℓ)} →

          Var Γ τ →
          -------------
          Term Δ Φ Γ τ

  `λ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ} {υ : Type Δ (★ ℓ₁)}

           (τ : Type Δ (★ ℓ₂)) → Term Δ Φ (Γ ، τ) υ →
           -------------------------------------
           Term Δ Φ Γ (τ `→ υ)

  _·_ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
          {τ : Type Δ (★ ℓ₁)} {υ : Type Δ (★ ℓ₂)} →

          Term Δ Φ Γ (τ `→ υ) → Term Δ Φ Γ τ →
          ----------------------------
          Term Δ Φ Γ υ

  `Λ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
         (κ : Kind ℓκ) {τ : Type (Δ ، κ) (★ ℓ)} →

         Term (Δ ، κ) (weakΦ Φ) (weakΓ Γ) τ →
         ----------------------------------------------------
         Term Δ Φ Γ (`∀ κ τ)


  _·[_] : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
            {κ : Kind ℓκ} {τ : Type (Δ ، κ) (★ ℓ)} →

            Term Δ Φ Γ (`∀ κ τ) → (υ : Type Δ κ) →
            ----------------------------------
            Term Δ Φ Γ (τ β[ υ ])

--   ------------------------------------------------------------
--   -- Qualified types.

  `ƛ : ∀  {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
          {κ : Kind ℓκ} {τ : Type Δ (★ ℓ)} →

           (π : Pred Δ κ) → Term Δ (Φ , π) Γ τ →
           -------------------------------------
           Term Δ Φ Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
           {π : Pred Δ κ} {τ : Type Δ (★ ℓ)} →

         Term Δ Φ Γ (π ⇒ τ) → Ent Δ Φ π →
         ----------------------------------
         Term Δ Φ Γ τ

  -- rowCompl : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
  --          {ρ₁ ρ₂ : Type Δ R[ κ ]} {τ : Type Δ (★ ℓ)} →

  --        Ent Δ Φ (ρ₁ ≲ ρ₂) → 
  --        Term Δ Φ Γ (`∀ R[ κ ] (K ρ₁ · (tvar Z) ~ K ρ₂ ⇒ K τ)) →
  --        --------------------------------------------------
  --        Term Δ Φ Γ τ

--   ------------------------------------------------------------
--   -- System Rω.

--   -- labels.
  lab : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}

          (l : Type Δ (L ℓ)) →
          ----------------------------------------
          Term Δ Φ Γ (⌊_⌋ {ℓ = ℓ} l)


--   -- singleton introduction.
  _▹_ : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L ℓ)} {υ : Type Δ (★ ℓκ)} →
          (M₁ : Term Δ Φ Γ (⌊_⌋ {ℓ = ℓ} τ)) (M₂ : Term Δ Φ Γ υ) →
          ----------------------------------------
          Term Δ Φ Γ (τ ▹ υ)

--   -- singleton elimination.
  _/_ : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L ℓ)} {υ : Type Δ (★ ℓκ)} →
          (M₁ : Term Δ Φ Γ (τ ▹ υ)) (M₂ : Term Δ Φ Γ (⌊_⌋ {ℓ = ℓ} τ)) →
          ----------------------------------------
          Term Δ Φ Γ υ


  -- record introduction.
  _⊹_ : ∀ {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ℓ ])} →

          (M : Term Δ Φ Γ (Π ρ₁)) (N : Term Δ Φ Γ (Π ρ₂)) →
          (π : Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃)) →
          ------------------------------
          Term Δ Φ Γ (Π ρ₃)

  -- record "elimination".
  prj : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
        {ρ₁ ρ₂ : Type Δ (R[ ★ ℓ ])} →

          (M : Term Δ Φ Γ (Π ρ₁)) → (π : Ent Δ Φ (ρ₂ ≲ ρ₁)) →
          ------------------------------
          Term Δ Φ Γ (Π ρ₂)

  -- Singleton → Singleton Record.
  Π : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
        {τ : Type Δ (L ℓ)} {υ : Type Δ (★ ℓκ)} →

          Term Δ Φ Γ (τ ▹ υ) →
          ---------------------
          Term Δ Φ Γ (Π (τ R▹ υ))

  -- Singleton Record → Singleton.
  Π⁻¹ : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {τ : Type Δ (L ℓ)} {υ : Type Δ (★ ℓκ)} →

          (M : Term Δ Φ Γ (Π (τ R▹ υ))) →
          ----------------------------------------
          Term Δ Φ Γ (τ ▹ υ)

  -- Subsumption.
  t-≡ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
          {τ υ : Type Δ (★ ℓ)}  →

          τ ≡t υ → (M : Term Δ Φ Γ τ) →
          ----------------------------
          Term Δ Φ Γ υ

  -- Variant introduction.
  inj : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
          {ρ₁ ρ₂ : Type Δ (R[ ★ ℓ ])} →

          (M : Term Δ Φ Γ (Σ ρ₁)) → (Ent Δ Φ (ρ₁ ≲ ρ₂)) →
          ----------------------------------------------
          Term Δ Φ Γ (Σ ρ₂)

  -- Singleton Record → Singleton.
  Σ : ∀ {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
        {τ : Type Δ (L ℓ)} {υ : Type Δ (★ ℓκ)} →

          Term Δ Φ Γ (τ ▹ υ) →
          ---------------------
          Term Δ Φ Γ (Σ (τ R▹ υ))

  -- Singleton Variant → Singleton.
  Σ⁻¹ : ∀ {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
        {τ : Type Δ (L ℓ)} {υ : Type Δ (★ ℓκ)} →

          (M : Term Δ Φ Γ (Σ (τ R▹ υ))) →
          ----------------------------------------
          Term Δ Φ Γ (τ ▹ υ)

  -- Variant elimination.
  _▿_ : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
        {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ℓ ])} {τ : Type Δ (★ ℓκ)} →

          Term Δ Φ Γ ((Σ ρ₁) `→ τ) →
          Term Δ Φ Γ ((Σ ρ₂) `→ τ) →
          Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
          ------------------------------
          Term Δ Φ Γ ((Σ ρ₃) `→ τ)

  -- Synthesis.
  syn : ∀ {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ}

          (ρ : Type Δ R[ κ ]) →
          (φ : Type Δ (κ `→ ★ ℓκ)) →
          Term Δ Φ Γ (SynT κ ρ φ) →
          --------------------------
          Term Δ Φ Γ (Π (φ ↑ ·[ ρ ]))

  -- Analysis.
  ana : ∀ {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {κ : Kind ℓκ}

         (ρ : Type Δ R[ κ ]) →
         (φ : Type Δ (κ `→ ★ ℓκ)) →
         (τ : Type Δ (★ ℓ)) →
         Term Δ Φ Γ (AnaT κ ρ φ τ) →
         --------------------------
         Term Δ Φ Γ (Σ (φ ↑ ·[ ρ ]) `→ τ)

  -- -- Fold.
  -- fold : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
  --        {ρ : Type Δ R[ ★ ℓ₁ ]} {υ : Type Δ (★ ℓ₂)} →

  --        (M₁ : Term Δ Φ Γ (FoldT ρ υ)) →
  --        (M₂ : Term Δ Φ Γ (υ `→ (υ `→ υ))) →
  --        (M₃ : Term Δ Φ Γ υ) →
  --        (N  : Term Δ Φ Γ (Π ρ)) →
  --        ------------------------
  --        Term Δ Φ Γ υ

  ------------------------------------------------------------
  -- System Rωμ.

  In : ∀ {ℓμ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
         {F : Type Δ ((★ ℓμ) `→ (★ ℓμ))} →

         Term Δ Φ Γ (F ·[ μ F ]) → Term Δ Φ Γ (Functor ·[ F ]) →
         ------------------------------------------------
         Term Δ Φ Γ (μ F)

  Out : ∀ {ℓμ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
         {F : Type Δ ((★ ℓμ) `→ (★ ℓμ))} →

         Term Δ Φ Γ (μ F) → Term Δ Φ Γ (Functor ·[ F ]) →
         ----------------------
         Term Δ Φ Γ (F ·[ μ F ])

  fix :  {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
         {τ : Type Δ (★ ℓ)} →

         ----------------------------
         Term Δ Φ Γ ((τ `→ τ) `→ τ)
