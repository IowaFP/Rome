module Rome.Operational.Types.Presentation where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Data.String using (_<_; _<?_)

postulate
  any : ∀ {A : Set} → A

-- =============================================================================
-- Constraining Types with Predicates
--   (presentation 04/30/25)
--
-- =============================================================================
-- 
-- Today I'll present on a technique in "restricting" a datatype to just certain
-- forms. In particular, we are going to try to model the following typing judgment:
--
--   Δ ⊢ ξᵢ : L    Δ ⊢ τᵢ : κ    ∀ i < j. ξᵢ < ξⱼ
--  --------------------------------------------
--              Δ ⊢ {ξᵢ ▹ τᵢ} : R[ κ ]
--
-- Where _<_ is a total ordering on strings (the type of concrete labels).
--
-- (For this exercise, your task is to mechanize a language intrinsically by
--  using inductive data to represent typing/kinding judgments. Imagine you see
--  this judgment on paper. How do you represent it in your AST?)
--
-- Firstly, let's think on the challenges in representing this judgment in Agda:
-- - 1. I cannot iterate over i, but I need to assert *all* of the judgments
--      on the top (for each i).
-- - 2. ξᵢ could be a variable, an application, etc. How do I order these?


--------------------------------------------------------------------------------
-- We define types and predicates, which I have presented before.

infixl 5 _·_
infixr 5 _≲_
data Pred (Ty : KEnv → Kind → Set) Δ : Kind → Set
data Type Δ : Kind → Set 

-- We address problem (1) by defining a "Simple Row" recursively to be a list of
-- types and labels.  Because my development has both Types and NormalTypes, I
-- index the definition by (Ty : KEnv → Kind → Set).  I want a SimpleRow to only
-- make sense when indexed by row kind, so we use a recursive definition to
-- define the type only at such a kind.
SimpleRow : (Ty : KEnv → Kind → Set) → KEnv → Kind → Set 
SimpleRow Ty Δ ★        = ⊥
SimpleRow Ty Δ L        = ⊥
SimpleRow Ty Δ (_ `→ _) = ⊥
SimpleRow Ty Δ R[ κ ]   = List (Ty Δ L × Ty Δ κ)

open import Data.String using (_<_)

-- We address the ordering problem by a predicate on SimpleRows. This is not
-- quite an inductive-inductive definition, but it will function similarly.
-- We need this predicate to assert that:
-- - When a row has > 2 entries, (i) its label components are Strings, and
--   (ii) these labels are ordered.
Ordered : SimpleRow Type Δ R[ κ ] → Set 

-- The ordered? function asserts that the Ordered predicate is decidable:
-- Given a SimpleRow, I can always tell you if it is ordered or not.
ordered? : ∀ (xs : SimpleRow Type Δ R[ κ ]) → Dec (Ordered xs)

-- We now define predicates and types. (boring.)

--------------------------------------------------------------------------------
-- Predicates


data Pred Ty Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Ty Δ R[ κ ]) → 
       --------------------- 
       Pred Ty Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : Ty Δ R[ κ ]) →
       ----------
       Pred Ty Δ R[ κ ]  
       
data Type Δ where

  ` : 
      (α : KVar Δ κ) →
      --------
      Type Δ κ

  `λ : 
      
      (τ : Type (Δ ,, κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ ★) →
         (τ₂ : Type Δ ★) → 
         --------
         Type Δ ★

  `∀    :
      
         {κ : Kind} → (τ : Type (Δ ,, κ) ★) →
         -------------
         Type Δ ★

  μ     :
      
         (φ : Type Δ (★ `→ ★)) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : Pred Type Δ R[ κ₁ ]) → (τ : Type Δ ★) → 
         ---------------------
         Type Δ ★       


  ------------------------------------------------------------------
  -- Rω business

  -- The ⦅_⦆ constructor builds a type from a simpleRow. (This is the judgment
  -- from before.)  We assert that a SimpleRow can only form a Type if it is
  -- ordered.  Note the PLFA trick: instead of asserting that Ordered xs is inhabited,
  -- we assert that ordered? xs == True. This means that the ordered evidence
  -- can be synthesized by Agda for concrete examples (we will see this below).
  ⦅_⦆ : (xs : SimpleRow Type Δ R[ κ ]) (ordered : True (ordered? xs)) →
        ----------------------
        Type Δ R[ κ ]

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ L

  -- label constant formation
  ⌊_⌋ :
        (τ : Type Δ L) →
        ----------
        Type Δ ★

--   ε : 

--     ------------
--     Type Δ R[ κ ]

  -- Row formation
  -- _▹_ :
  --        (l : Type Δ L) → (τ : Type Δ κ) → 
  --        -------------------
  --        Type Δ R[ κ ]

  _<$>_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          ----------------
          Type Δ (R[ κ ] `→ κ)


--------------------------------------------------------------------------------
-- Simple row well-formedness

--------------------------------------------------------------------------------
-- We now define the Ordered predicate. Recall our specification:
-- - When a row has > 2 entries, (i) its label components are Strings, and
--   (ii) these labels are ordered.
-- 
-- Note that, a single-entry row may have a variable/unreduced component.
-- We express this by letting the empty row [] and a single-entry row map to ⊤.
-- Hence the predicate is always satisfied when the row has < 2 entries.
Ordered [] = ⊤
Ordered (x ∷ []) = ⊤
-- When the row has > 2 entries, we assert (on the LHS)
-- that the components are string labels (constructed by `lab`).
-- Then on the rhs we assert that these labels are totally ordered.
-- This enforces that the labels are in order and also that there are no duplicates.
-- The recursive portion `Ordered xs` asserts similar
Ordered ((lab l₁ , τ₁) ∷ (lab l₂ , τ₂) ∷ xs) = l₁ < l₂ × Ordered ((lab l₂ , τ₂) ∷ xs)
Ordered _ = ⊥

-- We now complete the straightforward but tedious exercise of showing this predicate is
-- decidable. We proceed by the structure of induction in which the predicate is defined.
-- The first two cases are trivial.
ordered? [] = yes tt
ordered? (x ∷ []) = yes tt
-- In the meaningful case, we have to check if the labels are truly ordered and if the
-- rest of the list is ordered.
ordered? ((lab l₁ , _) ∷ (lab l₂ , τ) ∷ xs) with l₁ <? l₂ | ordered? ((lab l₂ , τ) ∷ xs)
-- Yes they are! Proceed.
... | yes p | yes q  = yes (p , q) 
-- No they're not! Find a contradiction.
... | yes p | no q  = no (λ { (_ , oxs) → q oxs }) 
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})
-- Perhaps most annoyingly, we must show in *totality* that the rest 
-- of the cases are impossible.
ordered? ((` α , snd₁) ∷ (` α₁ , snd₂) ∷ xs) = no (λ ())
ordered? ((` α , snd₁) ∷ (fst₂ · fst₃ , snd₂) ∷ xs) = no (λ ())
ordered? ((` α , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
ordered? ((fst₁ · fst₂ , snd₁) ∷ (` α , snd₂) ∷ xs) = no (λ ())
ordered? ((fst₁ · fst₂ , snd₁) ∷ (fst₃ · fst₄ , snd₂) ∷ xs) = no (λ ())
ordered? ((fst₁ · fst₂ , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
ordered? ((lab l , snd₁) ∷ (` α , snd₂) ∷ xs) = no (λ ())
ordered? ((lab l , snd₁) ∷ (fst₂ · fst₃ , snd₂) ∷ xs) = no (λ ())

--------------------------------------------------------------------------------
-- These are some helpers that we can come back to.

fmap× : ∀ {Ty : KEnv → Kind → Set} → (∀ {κ} → Ty Δ₁ κ → Ty Δ₂ κ) → 
          Ty Δ₁ L × Ty Δ₁ κ → Ty Δ₂ L × Ty Δ₂ κ
fmap× f (x , y) = f x , f y

map-map₂ : ∀ (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) (f : Type Δ₁ κ₁ → Type Δ₁ κ₂) → 
              Ordered ρ → Ordered (map (map₂ f) ρ)
map-map₂ [] f oρ = tt
map-map₂ (x ∷ []) f oρ = tt
map-map₂ ((lab l₁ , _) ∷ (lab l₂ , τ) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , map-map₂ ((lab l₂ , τ) ∷ ρ) f oρ

--------------------------------------------------------------------------------
-- Some examples.


-- THe empty row is the row constructed from an empty list. Note that its evidence is just tt.
ε : Type Δ R[ κ ]
ε = ⦅ [] ⦆ tt

-- The unit type is Π applied to the empty row.
Unit : Type Δ ★
Unit = Π · ε

-- Here's a single-entry row that does *not* have a string label
sing : Type (Δ ,, L) R[ ★ ]
sing = ⦅ [ (` Z) , Unit ] ⦆ tt

-- Here's a simple row. Let's play with the ordering.
sr₁ : Type Δ R[ ★ ] 
sr₁ = ⦅ (lab "a" , Unit) ∷ (lab "b" , (Σ · ε)) ∷ (lab "c" , ((`λ (` Z)) · Unit)) ∷ (lab "d" , Unit) ∷ [] ⦆ tt

-- Here we see that it's impossible to create a no-no row: We have ⊥ as a goal.
sr₂ : Type Δ R[ ★ ]   
sr₂ = ⦅ (lab "a" , Unit) ∷ (lab "b" , Unit) ∷ (lab "a" , Unit) ∷ [] ⦆ {!!}
-- Let's also see that I can't sneak in variables or applications into the labels:
-- This one fails.
sr₃ : Type (Δ ,, L) R[ ★ ]   
sr₃ = ⦅ (` Z , Unit) ∷ (lab "b" , Unit) ∷ [] ⦆ {!!}

-- nope again
sr₄ : Type Δ R[ ★ ]   
sr₄ = ⦅ ((`λ (` Z)) · lab "a" , Unit) ∷ (lab "b" , Unit) ∷ [] ⦆ {!!}
--------------------------------------------------------------------------------
-- Summary (intermission)
-- 
-- Recognize here that the technique we've employed has effectively "constricted"
-- terms with type Type Δ R[ κ ]. Let's see what Agda "thinks" such types can look like.

canonical-forms? : Type Δ R[ κ ] → ⊤
-- A row can be a variable
canonical-forms? (` α) = tt
-- An application
canonical-forms? (ρ · ρ₁) = tt
-- A mapping
canonical-forms? (ρ <$> ρ₁) = tt
-- Or a simple row with just the three cases.
canonical-forms? (⦅ [] ⦆ ordered) = tt
canonical-forms? (⦅ l ∷ [] ⦆ ordered) = tt
canonical-forms? (⦅ (lab l₁ , τ₁) ∷ (lab l , τ₂) ∷ xs ⦆ ordered) = tt
-- These two cases are a nuisance
canonical-forms? (⦅ (lab l₁ , τ₁) ∷ (` α , τ₂) ∷ xs ⦆ ())
canonical-forms? (⦅ (lab l₁ , τ₁) ∷ (l · l₂ , τ₂) ∷ xs ⦆ ())

--------------------------------------------------------------------------------
-- Now let's see why we made a big fuss over that mere proposition nonsense.  
-- Our first order of business in mechanizing metatheory is renaming. This
-- development follows PLFA closely and I won't explain too much.

-- A renaming maps type variables in environment Δ₁ to Δ₂
Renamingₖ : KEnv → KEnv → Set
Renamingₖ Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → KVar Δ₂ κ

-- We define a convenient helper for (extensional) equivalence of renamings
_≈_ : ∀ {Δ₁} (ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂) → Set
_≈_ {Δ₁ = Δ₁} ρ₁ ρ₂ = ∀ {κ} (x : KVar Δ₁ κ) → ρ₁ x ≡ ρ₂ x


-- Lifting---sort of like weakeking for a renaming. 
liftₖ : Renamingₖ Δ₁ Δ₂ → Renamingₖ (Δ₁ ,, κ) (Δ₂ ,, κ)
liftₖ ρ Z = Z
liftₖ ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Now we go about defining renaming, renₖ.

renₖ : Renamingₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₖ : Renamingₖ Δ₁ Δ₂ → Pred Type Δ₁ R[ κ ] → Pred Type Δ₂ R[ κ ]
renRowₖ : Renamingₖ Δ₁ Δ₂ → SimpleRow Type Δ₁ R[ κ ] → SimpleRow Type Δ₂ R[ κ ]

renₖ r (` x) = ` (r x)
renₖ r (`λ τ) = `λ (renₖ (liftₖ r) τ)
renₖ r (τ₁ · τ₂) = (renₖ r τ₁) · (renₖ r τ₂)
renₖ r (τ₁ `→ τ₂) = (renₖ r τ₁) `→ (renₖ r τ₂)
renₖ r (π ⇒ τ) = renPredₖ r π ⇒ renₖ r τ 
renₖ r (`∀ τ) = `∀ (renₖ (liftₖ r) τ)
renₖ r (μ F) = μ (renₖ r F)
renₖ r (Π ) = Π 
renₖ r Σ = Σ
renₖ r (lab x) = lab x
renₖ r ⌊ ℓ ⌋ = ⌊ (renₖ r ℓ) ⌋
renₖ r (f <$> m) = renₖ r f <$> renₖ r m
-- Let's walk through the proof process here.
-- What must we additionally show?
renₖ r (⦅ xs ⦆ oxs) = {!!} -- ⦅ (renRowₖ r xs) ⦆ {!!} -- 

-- We define renaming over rows in an obvious fashion.
renRowₖ r [] = [] 
renRowₖ r ((l , τ) ∷ xs) = (renₖ r l , renₖ r τ) ∷ renRowₖ r xs

-- ignore
renPredₖ ρ (ρ₁ · ρ₂ ~ ρ₃) = renₖ ρ ρ₁ · renₖ ρ ρ₂ ~ renₖ ρ ρ₃
renPredₖ ρ (ρ₁ ≲ ρ₂) = (renₖ ρ ρ₁) ≲ (renₖ ρ ρ₂) 


-- We must fulfill our obligation to show that renaming respects the Ordered predicate.
orderedRenRowₖ : (r : Renamingₖ Δ₁ Δ₂) → (ρ : SimpleRow Type Δ₁ R[ κ ]) → Ordered ρ → 
                 Ordered (renRowₖ r ρ)
orderedRenRowₖ r [] oxs = tt
orderedRenRowₖ r ((l , τ) ∷ []) oxs = tt
orderedRenRowₖ r ((lab l₁ , τ) ∷ (lab l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , (orderedRenRowₖ r ((lab l₂ , υ) ∷ xs) oxs)


--------------------------------------------------------------------------------
-- It becomes imperative in the development to show that certain properties 
-- of renaming hold. A simple one is that the identity renaming does nothing.


renₖ-id : ∀ (τ : Type Δ κ) → renₖ id τ ≡ τ
renRowₖ-id : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → renRowₖ id ρ ≡ ρ

-- Let's work together to solve this:
renₖ-id (⦅ ρ ⦆ oρ)  =  {!!}
-- We're ignoring the rest of the cases.
renₖ-id whatever = any

renRowₖ-id [] = refl
renRowₖ-id ((l , τ) ∷ xs) = cong₂ _∷_ (cong₂ _,_ (renₖ-id l) (renₖ-id τ)) (renRowₖ-id xs)

--------------------------------------------------------------------------------
-- The problem above is that we need to show two things:
--   1. renRowₖ id ρ = ρ 
--   2. (fromWitness (orderedRenRowₖ id ρ (toWitness oρ))) ≡ oρ 
-- In other words, the rows are equal and each evidence is equal.
-- We have already that (1.) holds, but 2 is actually nonsensical:
-- the LHS and RHS have different types.

-- To get out of this mess, we are going to show that these two proofs must
-- actually be the same.  In particular, we show that any proof of the form 
-- True (ordered? ρ) is a *mere proposition*, meaning any two inhabitants of the type
-- are equal. In other words, proofs of this proposition are *irrellevant*.
-- 
IsIrrelevant : ∀ (A : Set) → Set 
IsIrrelevant A = (p₁ p₂ : A) → p₁ ≡ p₂

-- You would expect this shit to be true: any two inhabitants of True (ordered?
-- p) equal ⊤. There is a broader generalization here then to utilize:
--  any predicate of the form (True d) for (d : Dec P) is a mere proposition.
Dec→Irrelevant : ∀ (P : Set) → (d : Dec P) → IsIrrelevant (True d)
Dec→Irrelevant P (yes d) p₁ p₂ = {!!}
Dec→Irrelevant P (no  d) p₁ p₂ = {!!}

-- It's simple to show that True (ordered? ρ) is a mere proposition now.
IrrelevantOrdered : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → IsIrrelevant (True (ordered? ρ))
IrrelevantqOrdered ρ = Dec→Irrelevant (Ordered ρ) (ordered? ρ)

-- The punchline follows: We may now write a congruence lemma for row types.
-- The lemma states that if we have two simplerows which are equivalent (but
-- perhaps have different evidence!)  that their evidences are also equivalent.
cong-SimpleRow : {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} {wf₁ : True (ordered? ρ₁)} {wf₂ : True (ordered? ρ₂)} → 
                 ρ₁ ≡ ρ₂ → 
                ⦅ ρ₁ ⦆ wf₁ ≡ ⦅ ρ₂ ⦆ wf₂
cong-SimpleRow {ρ₁ = ρ₁} {ρ₂} {wf₁} {wf₂} eq = {!!} 


-- **We can move this code above the last section and finish the proof**.
--------------------------------------------------------------------------------

