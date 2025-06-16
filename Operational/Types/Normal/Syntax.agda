{-# OPTIONS --safe #-}
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

IsNeutral IsNormal : NormalType Δ κ → Set 
NotSimpleRow : NormalType Δ R[ κ ] → Set 

isNeutral? : ∀ (τ : NormalType Δ κ) → Dec (IsNeutral τ)
isNormal? : ∀ (τ : NormalType Δ κ) → Dec (IsNormal τ)
notSimpleRows? : ∀ (τ₁ τ₂ : NormalType Δ R[ κ ]) → Dec (NotSimpleRow τ₁ or NotSimpleRow τ₂)

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

  _<$>_ : NormalType Δ (κ₁ `→ κ₂) → NeutralType Δ R[ κ₁ ] → 
          --------------------------------------------------
          NeutralType Δ R[ κ₂ ]


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


  Σ  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ---------------
      NormalType Δ ★

  _─_ : (ρ₂ ρ₁ : NormalType Δ R[ κ ]) → {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
        NormalType Δ R[ κ ]

  _▹ₙ_ : (l : NeutralType Δ L) (τ : NormalType Δ κ) → 
         ------------------------------------
         NormalType Δ R[ κ ]


--------------------------------------------------------------------------------
-- Ordered predicate

open IsStrictPartialOrder (SPO) renaming (trans to <-trans)

_≪_ : NormalType Δ L → NormalType Δ L → Set 
(lab l₁) ≪ (lab l₂) = l₁ < l₂
_ ≪ _ = ⊥

≪-trans : ∀ {l₁ l₂ l₃ : NormalType Δ L} → l₁ ≪ l₂ → l₂ ≪ l₃ → l₁ ≪ l₃ 
≪-trans {l₁ = lab l₁} {lab l₂} {lab l₃} i₁ i₂ = <-trans {i = l₁} {j = l₂} {l₃} i₁ i₂  

NormalOrdered [] = ⊤
NormalOrdered ((l , _) ∷ []) = ⊤
NormalOrdered ((l₁ , _) ∷ (l₂ , τ) ∷ xs) = l₁ < l₂ × NormalOrdered ((l₂ , τ) ∷ xs)

normalOrdered? [] = yes tt
normalOrdered? ((l , τ) ∷ []) = yes tt
normalOrdered? ((l₁ , _) ∷ (l₂ , _) ∷ xs) with l₁ <? l₂ | normalOrdered? ((l₂ , _) ∷ xs)
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})

NormalIrrelevantOrdered : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → Irrelevant (True (normalOrdered? ρ))
NormalIrrelevantOrdered ρ = Dec→Irrelevant (NormalOrdered ρ) (normalOrdered? ρ)

cong-⦅⦆ : {sr₁ sr₂ : SimpleRow NormalType Δ R[ κ ]} {wf₁ : True (normalOrdered? sr₁)} {wf₂ : True (normalOrdered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂)
cong-⦅⦆ {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalIrrelevantOrdered sr₁ wf₁ wf₂ = refl


inj-⦅⦆ : {sr₁ sr₂ : SimpleRow NormalType Δ R[ κ ]} 
         {wf₁ : True (normalOrdered? sr₁)} 
         {wf₂ : True (normalOrdered? sr₂)} → 
         _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂) → 
         sr₁ ≡ sr₂
inj-⦅⦆ {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalIrrelevantOrdered sr₁ wf₁ wf₂ = refl
                

--------------------------------------------------------------------------------
-- Mapping over preserves ordering

normal-map-overᵣ : ∀ (ρ : SimpleRow NormalType Δ₁ R[ κ₁ ]) (f : NormalType Δ₁ κ₁ → NormalType Δ₁ κ₂) → 
                   NormalOrdered ρ → NormalOrdered (map (overᵣ f) ρ)
normal-map-overᵣ [] f oρ = tt
normal-map-overᵣ (x ∷ []) f oρ = tt
normal-map-overᵣ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (normal-map-overᵣ ((l₂ , _) ∷ ρ) f oρ)


--------------------------------------------------------------------------------
-- IsNeutral and IsNormal predicates

IsNeutral (ne x) = ⊤ 
IsNeutral _ = ⊥

isNeutral? (ne x) = yes tt
isNeutral? (l ▹ₙ τ) = no λ ()
isNeutral? (`λ x) = no λ ()
isNeutral? (x `→ x₁) = no λ ()
isNeutral? (`∀ x) = no λ ()
isNeutral? (μ x) = no λ ()
isNeutral? (π ⇒ x) = no λ ()
isNeutral? (⦅ ρ ⦆ oρ) = no λ ()
isNeutral? (lab l) = no λ ()
isNeutral? ⌊ x ⌋ = no λ ()
isNeutral? (Π x) = no λ ()
isNeutral? (Σ x) = no λ ()
-- isNeutral? (x ─₁ ρ) = no λ ()
-- isNeutral? (ρ ─₂ x) = no λ ()
-- isNeutral? (_<$>_─₁_ c x d) = no λ ()
isNeutral? (c ─ c₁) = no λ ()

IsNormal (ne x)     = ⊥
IsNormal _     = ⊤

isNormal? (ne x) = no λ ()
isNormal? (l ▹ₙ τ) = yes tt
isNormal? (`λ x) = yes tt
isNormal? (x `→ x₁) = yes tt
isNormal? (`∀ x) = yes tt
isNormal? (μ x) = yes tt
isNormal? (π ⇒ x) = yes tt
isNormal? (⦅ ρ ⦆ oρ) = yes tt
isNormal? (lab l) = yes tt
isNormal? ⌊ x ⌋ = yes tt
isNormal? (Π x) = yes tt
isNormal? (Σ x) = yes tt
isNormal? (ρ₂ ─ ρ₁) = yes tt

NotSimpleRow (ne x) = ⊤
NotSimpleRow (⦅ ρ ⦆ oρ) = ⊥
NotSimpleRow (τ ─ τ₁) = ⊤
NotSimpleRow (x ▹ₙ τ) = ⊤

notSimpleRows? (ne x) _ = yes (left tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (ne x) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (⦅ ρ₁ ⦆ oρ₁) = no λ { (left ()) ; (right ()) }
notSimpleRows? (⦅ ρ ⦆ oρ) (ρ₁ ─ ρ₂) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (x ▹ₙ ρ₁) = yes (right tt)
notSimpleRows? (ρ₂ ─ ρ₃) _ = yes (left tt)
notSimpleRows? (x ▹ₙ ρ₂) _ = yes (left tt)


NormalIrrelevant : ∀ (τ : NormalType Δ κ) → Irrelevant (True (isNormal? τ))
NormalIrrelevant ρ = Dec→Irrelevant (IsNormal ρ) (isNormal? ρ)

cong-─ : {τ₂ υ₂ : NormalType Δ R[ κ ]}
          {τ₁ υ₁ : NormalType Δ R[ κ ]}
          {nsr₁ : True (notSimpleRows? τ₂ τ₁)} 
          {nsr₂ : True (notSimpleRows? υ₂ υ₁)} → 
                 τ₂ ≡ υ₂ → 
                 τ₁ ≡ υ₁ → 
                _≡_ {A = NormalType Δ R[ κ ]} ((τ₂ ─ τ₁) {nsr₁}) ((υ₂ ─ υ₁) {nsr₂})
cong-─ {τ₂ = τ₂} {τ₁ = τ₁} {nsr₁ = x} {x₁} refl refl rewrite Dec→Irrelevant _ (notSimpleRows? τ₂ τ₁) x x₁ = refl

-- cong-─₂ : {τ₂ υ₂ : NormalType Δ R[ κ ]}
--           {τ₁ υ₁ : NeutralType Δ R[ κ ]}
--           {isNorm₁ : True (isNormal? τ₂)} {isNorm₂ : True (isNormal? υ₂)} → 
--                  τ₂ ≡ υ₂ → 
--                  τ₁ ≡ υ₁ → 
--                 _≡_ {A = NeutralType Δ R[ κ ]} ((τ₂ ─₂ τ₁) {isNorm₁}) ((υ₂ ─₂ υ₁) {isNorm₂})
-- cong-─₂ {τ₂ = τ₂} {isNorm₁ = isNorm₁} {isNorm₂} refl refl rewrite NormalIrrelevant τ₂ isNorm₁ isNorm₂ = refl

-- inj-─₂ : {τ₂ υ₂ : NormalType Δ R[ κ ]}
--           {τ₁ υ₁ : NeutralType Δ R[ κ ]}
--           {isNorm₁ : True (isNormal? τ₂)} {isNorm₂ : True (isNormal? υ₂)} → 
--           _≡_ {A = NeutralType Δ R[ κ ]} ((τ₂ ─₂ τ₁) {isNorm₁}) ((υ₂ ─₂ υ₁) {isNorm₂}) → 
--           τ₁ ≡ υ₁ × τ₂ ≡ υ₂
-- inj-─₂ {τ₂ = τ₂} {isNorm₁ = isNorm₁} {isNorm₂} refl rewrite NormalIrrelevant τ₂ isNorm₁ isNorm₂ = refl , refl


--------------------------------------------------------------------------------
-- 

--------------------------------------------------------------------------------
-- There are no neutral types in empty contexts

noNeutrals : NeutralType ∅ κ → ⊥

noNeutrals (n · τ) = noNeutrals n 
noNeutrals (φ <$> n) = noNeutrals n

--------------------------------------------------------------------------------
-- There are no complements in empty contexts 

noComplements : ∀ {ρ₁ ρ₂ ρ₃ : NormalType ∅ R[ κ ]}
                  (nsr : True (notSimpleRows? ρ₃ ρ₂)) → 
                  ρ₁ ≡ (ρ₃ ─ ρ₂) {nsr} → 
                  ⊥
noComplements {ρ₁ = ne x₁ ─ _} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ne x₁} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ((ρ₂ ─ ρ₃) {nsr'})} {_} {_} nsr refl = noComplements {ρ₂ = ρ₃} {ρ₂} nsr' refl
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ (l ▹ₙ ρ₂)} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ((ρ₃ ─ ρ₂) {nsr'}) ─ _} {_} {_} nsr refl = noComplements {ρ₂ = ρ₂} {ρ₃} nsr' refl
noComplements {ρ₁ = (l ▹ₙ ρ₃) ─ _} {_} {_} nsr refl = ⊥-elim (noNeutrals l)

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
-- Injectivity lemmas for fucking everything

inj-` : ∀ {α β : KVar Δ κ} → _≡_ {A = NeutralType Δ κ} (` α) (` β) → α ≡ β 
inj-` refl = refl

inj-· : ∀ {f₁ f₂ : NeutralType Δ (κ₁ `→ κ₂)} {τ₁ τ₂ : NormalType Δ κ₁} → 
         f₁ · τ₁ ≡ f₂ · τ₂ → 
         f₁ ≡ f₂ × τ₁ ≡ τ₂ 
inj-· refl = refl , refl

-- inj-<$> : ∀ {φ₁ φ₂ : NormalType Δ (κ₁ `→ κ₂)} {τ₁ τ₂ : NeutralType Δ R[ κ₁ ]} → 
--           φ₁ <$> τ₁ ≡ φ₂ <$> τ₂ → 
--           φ₁ ≡ φ₂ × τ₁ ≡ τ₂ 
-- inj-<$> refl = refl , refl

-- inj-─₁ : ∀ {ρ₄ ρ₂ : NeutralType Δ R[ κ ]} {ρ₃ ρ₁ : NormalType Δ R[ κ ]} → 
--            ρ₄ ─₁ ρ₃ ≡ ρ₂ ─₁ ρ₁ → 
--            ρ₄ ≡ ρ₂ × ρ₃ ≡ ρ₁ 
-- inj-─₁ refl = refl , refl

inj-`λ :  {τ₁ τ₂ : NormalType (Δ ,, κ₁) κ₂} → `λ τ₁ ≡ `λ τ₂ → τ₁ ≡ τ₂
inj-`λ refl = refl

inj-`→ : ∀ {τ₁ τ₂ υ₁ υ₂ : NormalType Δ ★} → 
            τ₁ `→ τ₂ ≡ υ₁ `→ υ₂ → 
            τ₁ ≡ υ₁ × τ₂ ≡ υ₂ 
inj-`→ refl = refl , refl

inj-`∀ : ∀ {τ₁ τ₂ : NormalType (Δ ,, κ) ★} → 
           `∀ τ₁ ≡ `∀ τ₂ → 
           τ₁ ≡ τ₂ 
inj-`∀ refl = refl

inj-μ : ∀ {F₁ F₂ : NormalType Δ (★ `→ ★)} →
          μ F₁ ≡ μ F₂ → 
          F₁ ≡ F₂ 
inj-μ refl = refl

inj-⇒ : ∀ {π₁ π₂ : NormalPred Δ R[ κ₁ ]} {τ₁ τ₂ : NormalType Δ ★} → 
           π₁ ⇒ τ₁ ≡ π₂ ⇒ τ₂ → 
           π₁ ≡ π₂ × τ₁ ≡ τ₂ 
inj-⇒ refl = refl , refl

inj-lab : ∀ {l₁ l₂ : Label} → _≡_ {A = NormalType Δ L} (lab l₁) (lab l₂) → l₁ ≡ l₂
inj-lab refl = refl

inj-⌊⌋ : ∀ {l₁ l₂ : NormalType Δ L} → ⌊ l₁ ⌋ ≡ ⌊ l₂ ⌋ → l₁ ≡ l₂ 
inj-⌊⌋ refl = refl

inj-Π : ∀ {ρ₁ ρ₂ : NormalType Δ R[ ★ ]} → Π ρ₁ ≡ Π ρ₂ → ρ₁ ≡ ρ₂
inj-Π refl = refl

inj-Σ : ∀ {ρ₁ ρ₂ : NormalType Δ R[ ★ ]} → Σ ρ₁ ≡ Σ ρ₂ → ρ₁ ≡ ρ₂
inj-Σ refl = refl


--------------------------------------------------------------------------------
-- injectivity ne constructor

inj-ne : ∀ {e₁ e₂ : NeutralType Δ κ} {g₁ g₂ : True (ground? κ)} → ne e₁ {g₁} ≡ ne e₂ {ground = g₂} → e₁ ≡ e₂
inj-ne {κ = κ} {g₁ = g₁} {g₂ = g₂} refl rewrite Dec→Irrelevant (Ground κ) (ground? κ) g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Congruene for ne constructor

cong-ne : ∀ {x y : NeutralType Δ κ} {g₁ : True (ground? κ)} {g₂ : True (ground? κ)} →
          x ≡ y → ne x {g₁} ≡ ne y {g₂}
cong-ne {κ = κ} {g₁ = g₁} {g₂} refl rewrite Dec→Irrelevant (Ground κ) (ground? κ) g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Rows are either neutral or labeled types

row-canonicity : (ρ : NormalType Δ R[ κ ]) →  ⊤
row-canonicity (⦅ x ⦆ oρ) = tt
row-canonicity (ne x) = tt
-- row-canonicity (ρ <$> x) = tt
-- row-canonicity (x ─₁ ρ) = tt
-- row-canonicity (x ─₂ ρ) = tt
-- -- row-canonicity ([ x ▹ ρ ]─ ρ₁) = tt
row-canonicity (x ▹ₙ ρ) = tt
-- row-canonicity (F <$> x ─₁ ρ) = tt
row-canonicity (ρ₂ ─ ρ₁) = tt

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
-- ⇑NEapp : NeutralType Δ κ → Type Δ κ

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
⇑ (Σ x) = Σ · ⇑ x
⇑ (π ⇒ τ) = (⇑Pred π) ⇒ (⇑ τ)
⇑ (⦅ ρ ⦆ oρ) = ⦅ ⇑Row ρ ⦆ (fromWitness (Ordered⇑ ρ (toWitness oρ)))
-- ⇑ (F <$> x ─₁ ρ) = ((⇑ F) <$> (⇑NE x)) ─ (⇑ ρ)
⇑ (ρ₂ ─ ρ₁) = ⇑ ρ₂ ─ ⇑ ρ₁
-- ⇑ (x ─₁ ρ) = ⇑NE x ─ ⇑ ρ
-- ⇑ (x ─₂ ρ) = ⇑ x ─ ⇑NE ρ
-- ⇑ ([ l ▹ τ ]─ ρ) = ((⇑NE l) ▹ (⇑ τ)) ─ (⇑ ρ)
⇑ (l ▹ₙ τ) = (⇑NE l) ▹ (⇑ τ)

⇑Row [] = []
⇑Row ((l , τ) ∷ ρ) = ((l , ⇑ τ) ∷ ⇑Row ρ)

Ordered⇑ [] oρ = tt
Ordered⇑ (x ∷ []) oρ = tt
Ordered⇑ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) (l₁<l₂ , oρ) = l₁<l₂ , Ordered⇑ ((l₂ , _) ∷ ρ) oρ

⇑Row-isMap : ∀ (xs : SimpleRow NormalType Δ₁ R[ κ ]) → 
               ⇑Row xs ≡ map (λ { (l , τ) → l , ⇑ τ }) xs
⇑Row-isMap [] = refl
⇑Row-isMap (x ∷ xs) = cong₂ _∷_ refl (⇑Row-isMap xs)

⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
⇑NE (F <$> τ) = (⇑ F) <$> (⇑NE τ) 


-- ⇑NE (app x) = ⇑NEapp x
-- ⇑NE (ρ₂ ─₁ ρ₁) = (⇑NE ρ₂) ─ (⇑ ρ₁)
-- ⇑NE (ρ₂ ─₂ ρ₁) = (⇑ ρ₂) ─ (⇑NE ρ₁)

⇑Pred (ρ₁ · ρ₂ ~ ρ₃) = (⇑ ρ₁) · (⇑ ρ₂) ~ (⇑ ρ₃)
⇑Pred (ρ₁ ≲ ρ₂) = (⇑ ρ₁) ≲ (⇑ ρ₂)


--------------------------------------------------------------------------------
-- row "constructors"

εNF : NormalType Δ R[ κ ]
εNF = ⦅ [] ⦆ tt

_▹'_ : Label → NormalType Δ κ → NormalType Δ R[ κ ] 
x ▹' τ = ⦅ [ (x , τ) ] ⦆ tt

--------------------------------------------------------------------------------
-- Admissable constants

UnitNF : NormalType Δ ★
UnitNF = Π (⦅ [] ⦆ tt)
