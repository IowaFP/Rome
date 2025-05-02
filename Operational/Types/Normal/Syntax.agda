module Rome.Operational.Types.Normal.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (liftₖ ; Renamingₖ)



--------------------------------------------------------------------------------
-- 3.1. NormalType types
--
-- - NeutralType types are either 
--    (i)  variables, or
--    (ii) applications with variables stuck in head position. 
--         (And hence cannot reduce).
-- - NormalType types are types precluded from any applications (barring neutral forms).

-- infixr 1 _▹_
data NormalType (Δ : KEnv) : Kind → Set

NormalPred : KEnv → Kind → Set 
NormalPred = Pred NormalType

NormalOrdered : SimpleRow NormalType Δ R[ κ ] → Set 
normalOrdered? : ∀ (xs : SimpleRow NormalType Δ R[ κ ]) → Dec (NormalOrdered xs)

data NeutralType Δ : Kind → Set where

  ` : 
      (α : KVar Δ κ) → 
      ---------------------------
      NeutralType Δ κ

  _·_ : 
      
      (f : NeutralType Δ (κ₁ `→ κ)) → 
      (τ : NormalType Δ κ₁) → 
      ---------------------------
      NeutralType Δ κ

  _<$>_ : 

       (φ : NormalType Δ (κ₁ `→ κ₂)) → (τ : NeutralType Δ R[ κ₁ ]) → 
       -------------------------------------------------
       NeutralType Δ (R[ κ₂ ])

  _─₁_ : NeutralType Δ R[ κ ] → NormalType Δ R[ κ ] → 
        ----------------------------------------------
        NeutralType Δ R[ κ ]

  _─₂_ : NormalType Δ R[ κ ] → NeutralType Δ R[ κ ] → 
        ----------------------------------------------
        NeutralType Δ R[ κ ]



data NormalType Δ where

  ne : 

      (x : NeutralType Δ κ) → {ground : True (ground? κ)} → 
      --------------
      NormalType Δ κ

  `λ :

      (τ : NormalType (Δ ,, κ₁) κ₂) → 
      --------------------------
      NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 

      (τ₁ τ₂ : NormalType Δ ★) →
      -----------------
      NormalType Δ ★

  `∀    :
      
      (τ : NormalType (Δ ,, κ) ★) →
      --------------------------------------
      NormalType Δ ★

  μ     :
      
      (φ : NormalType Δ (★ `→ ★)) →
      -------------------------
      NormalType Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : NormalPred Δ R[ κ₁ ]) → (τ : NormalType Δ ★) → 
         ---------------------
         NormalType Δ ★       

  ------------------------------------------------------------------
  -- Rω business


  ⦅_⦆ : (ρ : SimpleRow NormalType Δ R[ κ ]) → (oρ : True (normalOrdered? ρ)) →
        ----------------------
       NormalType Δ R[ κ ]

  -- _▹_ : 
      
  --     (l : NormalType Δ L) → 
  --     (τ : NormalType Δ κ) → 
  --     ---------------------------
  --     NormalType Δ R[ κ ]

--   -- labels
  lab :
    
      (l : Label) → 
      --------
      NormalType Δ L

  -- label constant formation
  ⌊_⌋ :
      (l : NormalType Δ L) →
      -----------------
      NormalType Δ ★

  Π  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ------------------
      NormalType Δ ★

  ΠL  : 

      (ρ : NormalType Δ R[ L ]) →
      ------------------
      NormalType Δ L


  Σ  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ---------------
      NormalType Δ ★

  ΣL  : 

      (ρ : NormalType Δ R[ L ]) →
      ------------------
      NormalType Δ L

--------------------------------------------------------------------------------
-- Ordered predicate

_≪_ : NormalType Δ L → NormalType Δ L → Set 
(lab l₁) ≪ (lab l₂) = l₁ < l₂
_ ≪ _ = ⊥

NormalOrdered [] = ⊤
NormalOrdered ((l , _) ∷ []) = ⊤
NormalOrdered ((l₁ , _) ∷ (l₂ , τ) ∷ xs) = l₁ ≪ l₂ × NormalOrdered ((l₂ , τ) ∷ xs)

normalOrdered? [] = yes tt
normalOrdered? ((l , τ) ∷ []) = yes tt
normalOrdered? ((lab l₁ , _) ∷ (lab l₂ , _) ∷ xs) with l₁ <? l₂ | normalOrdered? ((lab l₂ , _) ∷ xs)
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})
normalOrdered? ((ne x , snd₁) ∷ (ne x₁ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ne x , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ne x , snd₁) ∷ (ΠL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ne x , snd₁) ∷ (ΣL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((lab l , snd₁) ∷ (ne x , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((lab l , snd₁) ∷ (ΠL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((lab l , snd₁) ∷ (ΣL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΠL τ , snd₁) ∷ (ne x , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΠL τ , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΠL τ , snd₁) ∷ (ΠL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΠL τ , snd₁) ∷ (ΣL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΣL τ , snd₁) ∷ (ne x , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΣL τ , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΣL τ , snd₁) ∷ (ΠL τ₂ , snd₂) ∷ xs) = no (λ ())
normalOrdered? ((ΣL τ , snd₁) ∷ (ΣL τ₂ , snd₂) ∷ xs) = no (λ ())

NormalMerePropOrdered : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → MereProp (True (normalOrdered? ρ))
NormalMerePropOrdered ρ = Dec→MereProp (NormalOrdered ρ) (normalOrdered? ρ)

cong-NormalSimpleRow : {sr₁ sr₂ : SimpleRow NormalType Δ R[ κ ]} {wf₁ : True (normalOrdered? sr₁)} {wf₂ : True (normalOrdered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂)
cong-NormalSimpleRow {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalMerePropOrdered sr₁ wf₁ wf₂ = refl


--------------------------------------------------------------------------------
-- There are no neutral types in empty contexts

noNeutrals : NeutralType ∅ κ → ⊥
noNeutrals (n · τ) = noNeutrals n
noNeutrals (φ <$> n) = noNeutrals n
noNeutrals (n ─₁ _) = noNeutrals n
noNeutrals (_ ─₂ n) = noNeutrals n

--------------------------------------------------------------------------------
-- Mapping type definitions over predicates 


mapPred : ∀ {Δ₁ Δ₂} {κ₁ κ₂} (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
          NormalPred Δ₁ R[ κ₁ ] → NormalPred Δ₂ R[ κ₂ ]
mapPred P (ρ₁ · ρ₂ ~ ρ₃) = P ρ₁ · P ρ₂ ~ P ρ₃
mapPred P (ρ₁ ≲ ρ₂)      = P ρ₁ ≲ P ρ₂

mapPredHO : ∀ {Δ₁ Δ₂} {κ₁ κ₂}
            (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) (Q : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
            (q : ∀ (τ : NormalType Δ₁ R[ κ₁ ]) → P τ ≡ Q τ) →
            (π : NormalPred Δ₁ R[ κ₁ ]) → mapPred P π ≡ mapPred Q π
mapPredHO P Q q (ρ₁ · ρ₂ ~ ρ₃) rewrite 
  q ρ₁ | q ρ₂ | q ρ₃ = refl
mapPredHO P Q q (ρ₁ ≲ ρ₂) rewrite 
  q ρ₁ | q ρ₂ = refl

mapPred-id : ∀ (π : NormalPred Δ R[ κ ]) → mapPred id π ≡ π
mapPred-id (ρ₁ · ρ₂ ~ ρ₃) = refl
mapPred-id (ρ₁ ≲ ρ₂) = refl

--------------------------------------------------------------------------------
-- injectivity ne constructor

inj-ne : ∀ {e₁ e₂ : NeutralType Δ κ} {g₁ g₂ : True (ground? κ)} → ne e₁ {g₁} ≡ ne e₂ {ground = g₂} → e₁ ≡ e₂
inj-ne {κ = κ} {g₁ = g₁} {g₂ = g₂} refl rewrite Dec→MereProp (Ground κ) (ground? κ) g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Congruene for ne constructor

cong-ne : ∀ {x y : NeutralType Δ κ} {g₁ : True (ground? κ)} {g₂ : True (ground? κ)} →
          x ≡ y → ne x {g₁} ≡ ne y {g₂}
cong-ne {κ = κ} {g₁ = g₁} {g₂} refl rewrite Dec→MereProp (Ground κ) (ground? κ) g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Rows are either neutral or labeled types

row-canonicity : (ρ : NormalType Δ R[ κ ]) →  
    Σ[ sr ∈ SimpleRow NormalType Δ R[ κ ] ] 
      (Σ[ oρ ∈ True (normalOrdered? sr) ] (ρ ≡ ⦅ sr ⦆ oρ)) or 
    Σ[ τ ∈ NeutralType Δ R[ κ ] ] ((ρ ≡ ne τ))
row-canonicity (⦅ x ⦆ oρ) = left (x , oρ , refl) 
row-canonicity (ne x) = right (x , refl)

--------------------------------------------------------------------------------
-- arrow-canonicity

arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl

--------------------------------------------------------------------------------
-- label canonicity

-- label-canonicity : (l : NormalType Δ L) → ⊤ 
-- label-canonicity (ne x) = {!!}
-- label-canonicity (lab l) = {!!}
-- label-canonicity (ΠL l) = {!!}
-- label-canonicity (ΣL l) = {!!}
--                     ∃[ l₁ ] (l ≡ ΠL l₁) or
--                     ∃[ l₂ ] (l ≡ ΣL l₂) or
--                     ∃[ x  ] (l ≡ ne x)
-- label-canonicity (ne x) = right (right (x , refl))
-- label-canonicity (ΠL l) = left (l , refl)
-- label-canonicity (ΣL l) = right (left (l , refl))


--------------------------------------------------------------------------------
-- Embedding Normal/neutral types back to Types

⇑ : NormalType Δ κ → Type Δ κ
⇑Row : SimpleRow NormalType Δ R[ κ ] → SimpleRow Type Δ R[ κ ]

⇑NE : NeutralType Δ κ → Type Δ κ
⇑Pred : NormalPred Δ R[ κ ] → Pred Type Δ R[ κ ] 

Ordered⇑ : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → NormalOrdered ρ → 
             Ordered (⇑Row ρ)

⇑ (ne x) = ⇑NE x
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ τ) = `∀ (⇑ τ)
⇑ (μ τ) = μ (⇑ τ)
⇑ (lab l) = lab l
⇑ ⌊ τ ⌋ = ⌊ ⇑ τ ⌋
⇑ (Π x) = Π · ⇑ x
⇑ (ΠL x) = Π · ⇑ x
⇑ (Σ x) = Σ · ⇑ x
⇑ (ΣL x) = Σ · ⇑ x
⇑ (π ⇒ τ) = (⇑Pred π) ⇒ (⇑ τ)
-- ⇑ (l ▹ τ) = ⇑ l ▹ ⇑ τ
⇑ (⦅ ρ ⦆ oρ) = ⦅ ⇑Row ρ ⦆ (fromWitness (Ordered⇑ ρ (toWitness oρ)))

⇑Row [] = []
⇑Row ((l , τ) ∷ ρ) = ((⇑ l , ⇑ τ) ∷ ⇑Row ρ)

Ordered⇑ [] oρ = tt
Ordered⇑ (x ∷ []) oρ = tt
Ordered⇑ ((lab l₁ , _) ∷ (lab l₂ , _) ∷ ρ) (l₁<l₂ , oρ) = l₁<l₂ , Ordered⇑ ((lab l₂ , _) ∷ ρ) oρ

⇑Row-isMap : ∀ (xs : SimpleRow NormalType Δ₁ R[ κ ]) → 
               ⇑Row xs ≡ map (λ { (l , τ) → ⇑ l , ⇑ τ }) xs
⇑Row-isMap [] = refl
⇑Row-isMap (x ∷ xs) = cong₂ _∷_ refl (⇑Row-isMap xs)

⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
⇑NE (F <$> τ) = (⇑ F) <$> (⇑NE τ) 
⇑NE (ρ₂ ─₁ ρ₁) = (⇑NE ρ₂) ─ (⇑ ρ₁)
⇑NE (ρ₂ ─₂ ρ₁) = (⇑ ρ₂) ─ (⇑NE ρ₁)

⇑Pred (ρ₁ · ρ₂ ~ ρ₃) = (⇑ ρ₁) · (⇑ ρ₂) ~ (⇑ ρ₃)
⇑Pred (ρ₁ ≲ ρ₂) = (⇑ ρ₁) ≲ (⇑ ρ₂)


--------------------------------------------------------------------------------
-- row "constructors"

εNF : NormalType Δ R[ κ ]
εNF = ⦅ [] ⦆ tt

_▹'_ : NeutralType Δ L → NormalType Δ κ → NormalType Δ R[ κ ] 
x ▹' τ = ⦅ [ (ne x , τ) ] ⦆ tt

_▹''_ : Label → NormalType Δ κ → NormalType Δ R[ κ ] 
l ▹'' τ = ⦅ [ (lab l , τ) ] ⦆ tt

--------------------------------------------------------------------------------
-- Admissable constants

UnitNF : NormalType Δ ★
UnitNF = Π (⦅ [] ⦆ tt)
