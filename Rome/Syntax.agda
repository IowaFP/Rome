module Rome.Syntax where

open import Preludes.Level
open import Preludes.Data
open import Preludes.Relation

open import Rome.Kinds
open import Rome.GVars.Kinds


--------------------------------------------------------------------------------
-- infix OOP.

infixr 9 _`→_
infixr 9 _⇒_
infixr 10 _▹_
infixr 10 _R▹_
infixr 10 _≲_
infix 10 _·_~_
infixl 11 _·[_]

infix 12 ↑_ _↑

--------------------------------------------------------------------------------
-- Labels are Strings.

Label : Set
Label = String

--------------------------------------------------------------------------------
-- Types and type vars.

data Pred : (Δ : KEnv ℓ) → (κ : Kind ι) → Set 
data PEnv : KEnv ℓ → Level → Set 


data Type : (Δ : KEnv ℓ) → (Φ : PEnv Δ ℓΦ) → Kind ι →  Set
data TVar : KEnv ℓ → Kind ι → Set
data Ent (Δ : KEnv ℓΔ) (Φ : PEnv Δ ℓΦ) : Pred Δ κ → Set
data _≡p_ : (π₁ π₂ : Pred Δ κ) → Set
data _≡t_ : ∀ {Φ : PEnv Δ ℓΦ} → (τ υ : Type Δ Φ κ) → Set

infix 0 _≡p_
infix 0 _≡t_

weakΦ : PEnv Δ ℓΦ → PEnv (Δ ، κ) ℓΦ

_β[_] : ∀ {ℓΔ ℓκ ℓι} {Δ : KEnv ℓΔ} {κ : Kind ℓκ}{ι : Kind ℓι} {Φ : PEnv Δ ℓΦ}
         → Type (Δ ، ι) (weakΦ Φ) κ → Type Δ Φ ι → Type Δ Φ κ

-- A Δ-map (renaming) maps type vars in environment Δ₁ to environment Δ₂.
Δ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Δ-map Δ₁ Δ₂ =
  (∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → TVar Δ₂ κ)

rebase-Φ : {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} → PEnv Δ₁ ℓ₁ → PEnv Δ₂ ℓ₂

-- A mapping from types to types.
π-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
τ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) (Φ : PEnv Δ₁ ℓ₁) → Set
τ-map {ℓ₁} {ℓ₂} Δ₁ Δ₂ Φ = (∀ {ℓ₃} {κ : Kind ℓ₃} → Type Δ₁ Φ κ → Type Δ₂ (rebase-Φ Φ) κ)

-- A mapping from preds to preds.
π-map Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} → Pred Δ₁ κ → Pred Δ₂ κ

-- A Context maps type vars to types.
Context : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Context {ℓ₁} Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} {Φ : PEnv Δ₁ ℓ₁} → TVar Δ₁ κ → Type Δ₂ (rebase-Φ Φ) κ


subst : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} {Φ : PEnv Δ₁ ℓ₁} →
           Context Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂ Φ

substPred : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
          Context Δ₁ Δ₂ →
          π-map Δ₁ Δ₂




data TVar where
  Z : TVar (Δ ، κ) κ
  S : TVar Δ κ₁ → TVar (Δ ، κ₂) κ₁

S² : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂) κ
S³ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃) κ
S⁴ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄) κ
S⁵ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄ ، κ₅) κ

S² x = S (S x)
S³ x = S (S² x)
S⁴ x = S (S³ x)
S⁵ x = S (S⁴ x)

--------------------------------------------------------------------------------
-- Predicates.

data Pred where
  _≲_ : ∀ {κ : Kind ι}{Φ : PEnv Δ ℓΦ} →
          (ρ₁ : Type Δ Φ R[ κ ]) →
          (ρ₂ : Type Δ Φ R[ κ ]) →
          Pred Δ κ

  _·_~_ : ∀ {κ : Kind ι} {Φ : PEnv Δ ℓΦ} →
            (ρ₁ : Type Δ Φ R[ κ ]) →
            (ρ₂ : Type Δ Φ R[ κ ]) →
            (ρ₃ : Type Δ Φ R[ κ ]) →
            Pred Δ κ

--------------------------------------
-- Predicate Environments & weakening.

data PEnv where
  ε : PEnv Δ lzero
  _,_ : {κ : Kind ℓκ} →
        PEnv Δ ℓΦ → Pred Δ κ → PEnv Δ (ℓΦ ⊔ ℓκ)
  _؛_ :  PEnv Δ ℓΦ → (κ : Kind ℓκ) → PEnv (Δ ، κ) (ℓΦ ⊔ ℓκ)


-----------------------
-- Predicate variables.

data PVar : PEnv Δ ℓΦ → Pred Δ κ → Set where
  Z : ∀ {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
        PVar (Φ , π) π

  S : ∀ {Φ : PEnv Δ ℓΦ}
        {π : Pred Δ κ₁} {ϕ : Pred Δ κ₂} →
        PVar Φ π → PVar (Φ , ϕ) π


--------------------------------------------------------------------------------
-- Types.
private
  variable
    Φ : PEnv Δ ℓΦ

data Type where

  ------------------------------------------------------------
  -- System Fω.

  tvar :

         TVar Δ κ →
         -----------
         Type Δ Φ κ

  _`→_ :
          Type Δ Φ (★ ℓ₁) → Type Δ Φ (★ ℓ₂) →
          -----------------------------------
          Type Δ Φ (★ (ℓ₁ ⊔ ℓ₂))

  `∀ :
          (κ : Kind ℓκ) → Type (Δ ، κ) (weakΦ Φ)  (★ ℓ) →
          -------------------------------------
          Type Δ Φ (★ (ℓ ⊔ (lsuc ℓκ)))

  `λ :
          (κ₁ : Kind ℓκ₁) → Type (Δ ، κ₁) (weakΦ Φ) κ₂ →
          -----------------------------------------
          Type Δ Φ (κ₁ `→ κ₂)

  _·[_] :
          Type Δ Φ (κ₁ `→ κ₂) → Type Δ Φ κ₁ →
          -----------------------------
          Type Δ Φ κ₂

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind ℓκ} →
         (π : Pred Δ κ) → Type Δ (Φ , π) (★ ℓ) →
         --------------------------------
         Type Δ Φ (★ (lsuc ℓκ ⊔ ℓ))

  ------------------------------------------------------------
  -- System Rω.

  -- The empty row.
  ε : Type Δ Φ R[ κ ]

  -- Row complement
  _─_ : 
        (ρ₂ : Type Δ Φ R[ κ ]) → (ρ₁ : Type Δ Φ R[ κ ]) → Ent Δ Φ (ρ₁ ≲ ρ₂) →
        ---------------------------------------------
        Type Δ Φ R[ κ ]


  -- Labels.
  lab :
        Label →
        ----------
        Type Δ Φ (L ℓ)

  -- singleton formation.
  _▹_ :
        Type Δ Φ (L ℓ) → Type Δ Φ κ →
        -------------------
        Type Δ Φ κ

  -- Row singleton formation.
  _R▹_ :
         Type Δ Φ (L ℓ) → Type Δ Φ κ →
         ---------------------------
         Type Δ Φ R[ κ ]

  -- label constant formation.
  ⌊_⌋ :
        Type Δ Φ (L ℓ) →
        ----------
        Type Δ Φ (★ ℓ)

  -- Record formation.
  Π :
      Type Δ Φ R[ κ ] →
      -------------
      Type Δ Φ κ

  -- Variant formation.
  Σ :
      Type Δ Φ R[ κ ] →
      -------------
      Type Δ Φ κ

  -- Lifting/mapping operations... I claim the kinds are at least
  -- self-evident now, even if the placement of arrows is a little bit
  -- arbitrary...

  ↑_ : {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
       Type Δ Φ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       Type Δ Φ (κ₁ `→ R[ κ₂ ])


  _↑ : {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
       Type Δ Φ (κ₁ `→ κ₂) →
       ------------------------------
       Type Δ Φ (R[ κ₁ ] `→ R[ κ₂ ])

  ------------------------------------------------------------
  -- System Rωμ.

  -- μ formation.
  μ : ∀ {ℓ} →
      (τ : Type Δ Φ ((★ ℓ) `→ (★ ℓ))) →
      -----------------------------------------------
      Type Δ Φ (★ ℓ)

--------------------------------------------------------------------------------
-- Type & Predicate equivalence.

data _≡p_ where
  peq-≲ : ∀ {τ₁ τ₂ υ₁ υ₂ : Type Δ Φ R[ κ ]} →

          τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
          ------------------------
          (τ₁ ≲ τ₂) ≡p υ₁ ≲ υ₂

  peq-· : ∀ {τ₁ τ₂ τ₃ υ₁ υ₂ υ₃ : Type Δ Φ R[ κ ]} →

            τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → τ₃ ≡t υ₃ →
            ----------------------------------
            τ₁ · τ₂ ~ τ₃ ≡p υ₁ · υ₂ ~ υ₃

data _≡t_ where
  teq-refl : {τ : Type Δ Φ κ} →

             ---------------
             τ ≡t τ

  teq-sym : ∀ {τ₁ τ₂ : Type Δ Φ κ} →

              τ₁ ≡t τ₂ →
              ---------------
              τ₂ ≡t τ₁

  teq-trans : ∀ {τ₁ τ₂ τ₃ : Type Δ Φ κ} →

                τ₁ ≡t τ₂ → τ₂ ≡t τ₃ →
                ----------------------
                τ₁ ≡t τ₃

  -- Problematic!!
  -- teq-⇒ : ∀ {π₁ π₂ : Pred Δ κ} {τ₁ : Type Δ (Φ , π₁) (★ ℓ)} {τ₂ : Type Δ (Φ , π₂) (★ ℓ)} →

  --              π₁ ≡p π₂ → τ₁ ≡t τ₂ →
  --              -----------------------
  --              π₁ ⇒ τ₁ ≡t π₂ ⇒ τ₂

  teq-∀ : ∀ {τ υ : Type (Δ ، κ) (weakΦ Φ) (★ ℓ)} →

            τ ≡t υ →
            ----------------
            `∀ κ τ ≡t `∀ κ υ

  teq-β     : ∀ {τ : Type (Δ ، κ) (weakΦ Φ) κ'} {υ : Type Δ Φ κ} →

                ------------------------------
                ((`λ κ τ) ·[ υ ]) ≡t (τ β[ υ ])

  teq-· : ∀ {τ₁ υ₁ : Type Δ Φ (κ `→ κ')} {τ₂ υ₂ : Type Δ Φ κ} →

           τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
           ------------------------
           τ₁ ·[ τ₂ ] ≡t υ₁ ·[ υ₂ ]

  teq-sing : ∀  {l₁ l₂ : Type Δ Φ (L ℓ)} →
                {τ₁ τ₂ : Type Δ Φ κ₁} →

                l₁ ≡t l₂ → τ₁ ≡t τ₂ →
                --------------------------------------
                (l₁ R▹ τ₁) ≡t (l₂ R▹ τ₂)

  teq-lift₁ : ∀ {l : Type Δ Φ (L ℓ)} {υ : Type Δ Φ κ} {τ : Type Δ Φ (κ `→ κ')} →

                --------------------------------------
                (↑ (l R▹ τ)) ·[ υ ] ≡t (l R▹ (τ ·[ υ ]))


  teq-lift₂ : ∀ {l : Type Δ Φ (L ℓ)} {υ : Type Δ Φ (κ₁ `→ κ₂)} {τ : Type Δ Φ κ₁} →

                --------------------------------------
                (υ ↑) ·[ l R▹ τ ] ≡t (l R▹ (υ ·[ τ ]))

  teq-⌊⌋    : ∀ {τ υ : Type Δ Φ (L ℓ)} →

                τ ≡t υ →
                -------------
                ⌊_⌋ {ℓ = ℓ} τ ≡t ⌊_⌋ {ℓ = ℓ} υ

  teq-Π : ∀ {ρ₁ ρ₂ : Type Δ Φ R[ ★ ℓκ ] } →
          ρ₁ ≡t ρ₂ →
          -------------
          Π ρ₁ ≡t Π ρ₂

  teq-Σ : ∀ {ρ₁ ρ₂ : Type Δ Φ R[ ★ ℓκ ] } →
          ρ₁ ≡t ρ₂ →
          -------------
          Σ ρ₁ ≡t Σ ρ₂

  teq-lift₃ : ∀ {ρ₁ : Type Δ Φ R[ κ `→ ★ ℓκ ] } {τ : Type Δ Φ κ} →

                ---------------------------
                Σ ρ₁ ·[ τ ] ≡t Σ ((↑ ρ₁) ·[ τ ])

--------------------------------------------------------------------------------
-- Entailment.

data Ent Δ Φ where

  n-var : ∀ {π : Pred Δ κ} →
           PVar Φ π →
           -----------
           Ent Δ Φ π

  n-refl : ∀  {τ : Type Δ Φ R[ κ ]}  →

          --------------
          Ent Δ Φ (τ ≲ τ)

  n-trans : ∀  {τ₁ τ₂ τ₃ : Type Δ Φ R[ κ ]} →

          Ent Δ Φ (τ₁ ≲ τ₂) → Ent Δ Φ (τ₂ ≲ τ₃) →
          ---------------------------------------
          Ent Δ Φ (τ₁ ≲ τ₃)

  n-≡ : ∀ {π₁ π₂ : Pred Δ κ} →

        π₁ ≡p π₂ → Ent Δ Φ π₁ →
        ------------------------
        Ent Δ Φ π₂

  n-≲lift₁ : ∀ {ρ₁ ρ₂ : Type Δ Φ R[ κ₁ `→ κ₂ ]}
             {τ : Type Δ Φ κ₁} →

             Ent Δ Φ (ρ₁ ≲ ρ₂) →
             ---------------------
             Ent Δ Φ ((↑ ρ₁ ·[ τ ]) ≲ (↑ ρ₂ ·[ τ ]))

  n-≲lift₂ : ∀ {ρ₁ ρ₂ : Type Δ Φ R[ κ₁ ]}
               {ϕ : Type Δ Φ (κ₁ `→ κ₂)} →

             Ent Δ Φ (ρ₁ ≲ ρ₂) →
             ---------------------
             Ent Δ Φ ((ϕ ↑ ·[ ρ₁ ]) ≲ (ϕ ↑ ·[ ρ₂ ]))

  n-·lift₁ : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ Φ R[ κ₁ `→ κ₂ ]}
               {τ : Type Δ Φ κ₁} →

             Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             ---------------------
             Ent Δ Φ ((↑ ρ₁ ·[ τ ]) · (↑ ρ₂ ·[ τ ]) ~ (↑ ρ₃ ·[ τ ]))

  n-·lift₂ : ∀  {κ₁ : Kind ℓκ}
             {ρ₁ ρ₂ ρ₃ : Type Δ Φ R[ κ₁ ]}
             {τ : Type Δ Φ (κ₁ `→ κ₂)} →

             Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             ---------------------
             Ent Δ Φ ((τ ↑ ·[ ρ₁ ]) · (τ ↑ ·[ ρ₂ ]) ~ (τ ↑ ·[ ρ₃ ]))

  n-·≲L : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ Φ R[ κ ]} →

        Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Δ Φ (ρ₁ ≲ ρ₃)


  n-·≲R : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ Φ R[ κ ]} →

        Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Δ Φ (ρ₂ ≲ ρ₃)

  n-ε-R : ∀  {κ₁ : Kind ℓκ}
             {ρ : Type Δ Φ R[ κ₁ ]} →

             -------------------------
             Ent Δ Φ (ρ · ε ~ ρ)

  n-ε-L : ∀  {κ₁ : Kind ℓκ}
             {ρ : Type Δ Φ R[ κ₁ ]} →

             -------------------------
             Ent Δ Φ (ε · ρ ~ ρ)


--------------------------------------------------------------------------------
-- Substitution


--------------------------------------------------------------------------------
-- Defs.

--------------------------------------------------------------------------------
-- Extension.
--
-- Given a map from variables in one Context to variables in another, extension
-- yields a map from the first Context extended to the second Context similarly
-- extended.

ext : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} {ι : Kind ℓ₃} →
         Δ-map Δ₁ Δ₂ →
         Δ-map (Δ₁ ، ι) (Δ₂ ، ι)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming.
--
-- Renaming is a necessary prelude to substitution، enabling us to “rebase” a
-- type from one Context to another.

rename : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} {Φ : PEnv Δ₁ ℓ₁} →
           Δ-map Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂ Φ
renamePred : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Δ-map Δ₁ Δ₂ →
           π-map Δ₁ Δ₂

rebase-Φ Φ = ?

rename ρ (tvar v) = tvar (ρ v)
rename ρ (τ `→ υ) = rename ρ τ `→ rename ρ υ
rename ρ (`∀ κ τ) = `∀ κ ? -- (rename (ext ρ) τ)
rename ρ (`λ s τ) = `λ s ? -- (rename (ext ρ) τ)
rename ρ (τ ·[ υ ]) = rename ρ τ ·[ rename ρ υ ]
rename ρ (lab l) = lab l
rename ρ (t ▹ v) = (rename ρ t) ▹ (rename ρ v)
rename ρ (⌊ t ⌋) = ⌊ rename ρ t ⌋
rename ρ (t R▹ v) = rename ρ t R▹ rename ρ v
rename ρ (Π r) = Π (rename ρ r)
rename ρ (Type.Σ r) = Type.Σ (rename ρ r)
rename ρ (π ⇒ τ) = renamePred ρ π ⇒ ? -- rename ρ τ
rename ρ (↑ f) = ↑ rename ρ f
rename ρ (f ↑) = rename ρ f ↑
rename ρ ε = ε
rename ρ ((τ ─ υ) ent)  = _─_ (rename ρ τ) (rename ρ υ) ? -- ent
rename ρ (μ X) = μ (rename ρ X)

renamePred ρ (ρ₁ ≲ ρ₂) = rename ρ ρ₁ ≲ rename ρ ρ₂
renamePred ρ (ρ₁ · ρ₂ ~ ρ₃) = rename ρ ρ₁ ·  rename ρ ρ₂ ~ rename ρ ρ₃

--------------------------------------------------------------------------------
-- Weakening (of a typing derivation.)

weaken : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
           τ-map Δ (Δ ، κ)
weaken = rename S

--------------------------------------------------------------------------------
-- Repeated weakening (helpers)
K = weaken
K¹ = weaken
K² : ∀ {ℓΔ ℓ₁ ℓ₂} {Δ : KEnv ℓΔ} {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
           τ-map Δ (Δ ، κ₁ ، κ₂)
K² = λ x → weaken (weaken x)

K³ : ∀ {ℓΔ ℓ₁ ℓ₂ ℓ₃} {Δ : KEnv ℓΔ} {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} {κ₃ : Kind ℓ₃} →
           τ-map Δ (Δ ، κ₁ ، κ₂ ، κ₃)
K³ = λ x → K¹ (K² x)

K⁴ : ∀ {ℓΔ ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Δ : KEnv ℓΔ} {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} {κ₃ : Kind ℓ₃} {κ₄ : Kind ℓ₄} →
           τ-map Δ (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄)
K⁴ = λ x → K² (K² x)

--------------------------------------------------------------------------------
-- Simultaneous Substitution.
--
-- Instead of substituting a closed term for a single variable, we provide a
-- map that takes each free variable of the original type to another
-- tye. Further, the substituted terms are over an arbitrary Context, and need
-- not be closed.


exts : ∀ {ℓ₁ ℓ₂ ℓ₃}
         {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂}
         {ι : Kind ℓ₃} →
         Context Δ₁ Δ₂ →
         Context (Δ₁ ، ι) (Δ₂ ، ι)
exts θ Z = tvar Z
exts θ (S x) = rename S (θ x)

--------------------------------------------------------------------------------
-- Substitution.
--

subst θ (tvar x) = θ x
subst θ (τ `→ υ) = subst θ τ `→ subst θ υ
subst θ (`∀ κ τ) = `∀ κ (subst (exts θ) τ)
subst θ (`λ s τ) = `λ s (subst (exts θ) τ)
subst θ (τ ·[ υ ]) = subst θ τ ·[ subst θ υ ]
subst θ (lab l) = lab l
subst θ (t ▹ v) = (subst θ t) ▹ (subst θ v)
subst θ (⌊ t ⌋) = ⌊ subst θ t ⌋
subst θ (t R▹ v) = subst θ t R▹ subst θ v
subst θ (Π r) = Π (subst θ r)
subst θ (Type.Σ r) = Type.Σ (subst θ r)
subst θ (π ⇒ τ) = substPred θ π ⇒ subst θ τ
subst θ (↑ f) = ↑ subst θ f
subst θ (f ↑) = subst θ f ↑
subst θ ε = ε
subst θ ((τ ─ υ)) = _─_ (subst θ τ) (subst θ υ)
subst ρ (μ X) = μ (subst ρ X)

substPred θ (ρ₁ ≲ ρ₂)      = subst θ ρ₁ ≲ subst θ ρ₂
substPred θ (ρ₁ · ρ₂ ~ ρ₃) = subst θ ρ₁ ·  subst θ ρ₂ ~ subst θ ρ₃

--------------------------------------------------------------------------------
-- Single substitution.

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
        Type Δ Φ κ → Context (Δ ، κ) Δ
Z↦ τ Z = τ
Z↦ τ (S x) = tvar x

-- Regular ol' substitution.
τ β[ υ ] = subst (Z↦ υ) τ

weakΦ ε = ε
weakΦ (Φ , π) = weakΦ Φ , renamePred S π
