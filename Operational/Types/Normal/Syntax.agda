{-# OPTIONS --safe #-}
module Rome.Operational.Types.Normal.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (liftₖ ; Renamingₖ)



--------------------------------------------------------------------------------
-- Normal & Neutral types 

data NormalType (Δ : KEnv) : Kind → Set

NormalPred : KEnv → Kind → Set 
NormalPred = Pred NormalType

NormalOrdered : SimpleRow NormalType Δ R[ κ ] → Set 
normalOrdered? : ∀ (xs : SimpleRow NormalType Δ R[ κ ]) → Dec (NormalOrdered xs)

IsNeutral IsNormal : NormalType Δ κ → Set 
isNeutral? : ∀ (τ : NormalType Δ κ) → Dec (IsNeutral τ)
isNormal? : ∀ (τ : NormalType Δ κ) → Dec (IsNormal τ)

NotSimpleRow : NormalType Δ R[ κ ] → Set 
notSimpleRows? : ∀ (τ₁ τ₂ : NormalType Δ R[ κ ]) → Dec (NotSimpleRow τ₁ or NotSimpleRow τ₂)

data NeutralType Δ : Kind → Set where
  ` : 
      (α : TVar Δ κ) → 
      ---------------------------
      NeutralType Δ κ

  _·_ : 
      
      (f : NeutralType Δ (κ₁ `→ κ)) → 
      (τ : NormalType Δ κ₁) → 
      ---------------------------
      NeutralType Δ κ

data NormalType Δ where

  ne : 

      (x : NeutralType Δ κ) → {ground : True (ground? κ)} → 
      --------------
      NormalType Δ κ

  _<$>_ : (φ : NormalType Δ (κ₁ `→ κ₂)) → NeutralType Δ R[ κ₁ ] →
          --------------------------------------------------
          NormalType Δ R[ κ₂ ]

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

  _∖_ : (ρ₂ ρ₁ : NormalType Δ R[ κ ]) → {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
        NormalType Δ R[ κ ]

  _▹ₙ_ : (l : NeutralType Δ L) (τ : NormalType Δ κ) → 
         ------------------------------------
         NormalType Δ R[ κ ]

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
isNeutral? (c ∖ c₁) = no λ ()
isNeutral? ((φ <$> n)) = no λ ()

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
isNormal? (ρ₂ ∖ ρ₁) = yes tt
isNormal? ((φ <$> n)) = yes tt                

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
-- Ordered lists yield ordered tails

normalOrdered-tail : ∀ (x : Label × NormalType Δ κ) (ρ : SimpleRow NormalType Δ R[ κ ]) → 
               NormalOrdered (x ∷ ρ) → 
               NormalOrdered ρ 
normalOrdered-tail x [] oxρ = tt
normalOrdered-tail (l , snd₁) ((l₁ , snd₂) ∷ ρ) (_ , oxρ) = oxρ 

--------------------------------------------------------------------------------
-- Mapping over preserves ordering

normal-map-map₂ : ∀ (ρ : SimpleRow NormalType Δ₁ R[ κ₁ ]) (f : NormalType Δ₁ κ₁ → NormalType Δ₁ κ₂) → 
                   NormalOrdered ρ → NormalOrdered (map (map₂ f) ρ)
normal-map-map₂ [] f oρ = tt
normal-map-map₂ (x ∷ []) f oρ = tt
normal-map-map₂ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (normal-map-map₂ ((l₂ , _) ∷ ρ) f oρ)

NotSimpleRow (ne x) = ⊤
NotSimpleRow ((φ <$> τ)) = ⊤
NotSimpleRow (⦅ ρ ⦆ oρ) = ⊥
NotSimpleRow (τ ∖ τ₁) = ⊤
NotSimpleRow (x ▹ₙ τ) = ⊤

notSimpleRows? (ne x) _ = yes (left tt)
notSimpleRows? ((τ₁ <$> ρ)) _ = yes (left tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (ne x) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (⦅ ρ₁ ⦆ oρ₁) = no λ { (left ()) ; (right ()) }
notSimpleRows? (⦅ ρ ⦆ oρ) (ρ₁ ∖ ρ₂) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (x ▹ₙ ρ₁) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) ((φ <$> _)) = yes (right tt)
notSimpleRows? (ρ₂ ∖ ρ₃) _ = yes (left tt)
notSimpleRows? (x ▹ₙ ρ₂) _ = yes (left tt)


cong-∖ : {τ₂ υ₂ : NormalType Δ R[ κ ]}
          {τ₁ υ₁ : NormalType Δ R[ κ ]}
          {nsr₁ : True (notSimpleRows? τ₂ τ₁)} 
          {nsr₂ : True (notSimpleRows? υ₂ υ₁)} → 
                 τ₂ ≡ υ₂ → 
                 τ₁ ≡ υ₁ → 
                _≡_ {A = NormalType Δ R[ κ ]} ((τ₂ ∖ τ₁) {nsr₁}) ((υ₂ ∖ υ₁) {nsr₂})
cong-∖ {τ₂ = τ₂} {τ₁ = τ₁} {nsr₁ = x} {x₁} refl refl rewrite Dec→Irrelevant _ (notSimpleRows? τ₂ τ₁) x x₁ = refl


--------------------------------------------------------------------------------
-- There are no neutral types in empty contexts

noNeutrals : NeutralType ∅ κ → ⊥

noNeutrals (n · τ) = noNeutrals n 

--------------------------------------------------------------------------------
-- There are no complements in empty contexts 

noComplements : ∀ {ρ₁ ρ₂ ρ₃ : NormalType ∅ R[ κ ]}
                  (nsr : True (notSimpleRows? ρ₃ ρ₂)) → 
                  ρ₁ ≡ (ρ₃ ∖ ρ₂) {nsr} → 
                  ⊥
noComplements {ρ₁ = ne x₁ ∖ _} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ∖ ne x₁} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ∖ ((ρ₂ ∖ ρ₃) {nsr'})} {_} {_} nsr refl = noComplements {ρ₂ = ρ₃} {ρ₂} nsr' refl
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ∖ (l ▹ₙ ρ₂)} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ∖ ((φ <$> τ))} {_} {_} nsr refl = ⊥-elim (noNeutrals τ)
noComplements {ρ₁ = ((ρ₃ ∖ ρ₂) {nsr'}) ∖ _} {_} {_} nsr refl = noComplements {ρ₂ = ρ₂} {ρ₃} nsr' refl
noComplements {ρ₁ = (l ▹ₙ ρ₃) ∖ _} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ((φ <$> τ)) ∖ _} nsr refl = ⊥-elim (noNeutrals τ)

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
-- Injectivity lemmas for all the NormalType syntax

inj-` : ∀ {α β : TVar Δ κ} → _≡_ {A = NeutralType Δ κ} (` α) (` β) → α ≡ β 
inj-` refl = refl

inj-· : ∀ {f₁ f₂ : NeutralType Δ (κ₁ `→ κ₂)} {τ₁ τ₂ : NormalType Δ κ₁} → 
         f₁ · τ₁ ≡ f₂ · τ₂ → 
         f₁ ≡ f₂ × τ₁ ≡ τ₂ 
inj-· refl = refl , refl

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
-- injectivity of ne constructor (erasing proofs)

inj-ne : ∀ {e₁ e₂ : NeutralType Δ κ} {g₁ g₂ : True (ground? κ)} → ne e₁ {g₁} ≡ ne e₂ {ground = g₂} → e₁ ≡ e₂
inj-ne {κ = κ} {g₁ = g₁} {g₂ = g₂} refl rewrite Dec→Irrelevant (Ground κ) (ground? κ) g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Congruene for ne constructor

cong-ne : ∀ {x y : NeutralType Δ κ} {g₁ : True (ground? κ)} {g₂ : True (ground? κ)} →
          x ≡ y → ne x {g₁} ≡ ne y {g₂}
cong-ne {κ = κ} {g₁ = g₁} {g₂} refl rewrite Dec→Irrelevant (Ground κ) (ground? κ) g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Canonical forms of rows

row-canonicity : (ρ : NormalType Δ R[ κ ]) →  ⊤
row-canonicity (⦅ x ⦆ oρ) = tt
row-canonicity (ne x) = tt
row-canonicity (x ▹ₙ ρ) = tt
row-canonicity ((φ <$> ρ)) = tt
row-canonicity (ρ₂ ∖ ρ₁) = tt

row-canonicity-∅ : (ρ : NormalType ∅ R[ κ ]) → 
                    ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
                    (ρ ≡ ⦅ xs ⦆ oxs)
row-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
row-canonicity-∅ (⦅ ρ ⦆ oρ) = ρ , oρ , refl
row-canonicity-∅ ((ρ ∖ ρ₁) {nsr}) = ⊥-elim (noComplements nsr refl)
row-canonicity-∅ (l ▹ₙ ρ) = ⊥-elim (noNeutrals l)
row-canonicity-∅ ((φ <$> ρ)) = ⊥-elim (noNeutrals ρ)

--------------------------------------------------------------------------------
-- arrow-canonicity

arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl

--------------------------------------------------------------------------------
-- label canonicity

label-canonicity : (l : NormalType Δ L) → ⊤ 
label-canonicity (ne x) = tt
label-canonicity (lab l) = tt

label-canonicity-∅ : ∀ (l : NormalType ∅ L) → ∃[ s ] (l ≡ lab s)
label-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
label-canonicity-∅ (lab s) = s , refl

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
⇑ (Σ x) = Σ · ⇑ x
⇑ (π ⇒ τ) = (⇑Pred π) ⇒ (⇑ τ)
⇑ (⦅ ρ ⦆ oρ) = ⦅ ⇑Row ρ ⦆ (fromWitness (Ordered⇑ ρ (toWitness oρ)))
⇑ (ρ₂ ∖ ρ₁) = ⇑ ρ₂ ∖ ⇑ ρ₁
⇑ (l ▹ₙ τ) = (⇑NE l) ▹ (⇑ τ)
⇑ ((F <$> τ)) = (⇑ F) <$> (⇑NE τ) 

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
