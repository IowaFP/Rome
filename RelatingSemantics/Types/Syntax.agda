module Rome.RelatingSemantics.Types.Syntax where 

open import Rome.RelatingSemantics.Prelude
open import Rome.RelatingSemantics.Kinds.Syntax
open import Rome.RelatingSemantics.Kinds.GVars

--------------------------------------------------------------------------------
-- signatures 

data NormalType (Δ : KEnv ι₁) : Kind ι₂ → Set
data NormalPred (Δ : KEnv ι₁) : Kind ι₂ → Set

SimpleRow : KEnv ι₁ → Kind ι₂ → Set 
SimpleRow Δ R[ κ ]   = List (Label × NormalType Δ κ)
SimpleRow Δ _ = ⊥

NormalOrdered : SimpleRow Δ R[ κ ] → Set 
normalOrdered? : ∀ (xs : SimpleRow Δ R[ κ ]) → Dec (NormalOrdered xs)

NotSimpleRow : NormalType Δ R[ κ ] → Set 
notSimpleRows? : ∀ (τ₁ τ₂ : NormalType Δ R[ κ ]) → Dec (NotSimpleRow τ₁ or NotSimpleRow τ₂)


--------------------------------------------------------------------------------
-- Predicates

infixl 5 _·_
infixr 5 _≲_
data NormalPred Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]) → 
       --------------------- 
       NormalPred Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : NormalType Δ R[ κ ]) →
       ----------
       NormalPred Δ R[ κ ]  

       
--------------------------------------------------------------------------------
-- Neutral and normal types 

data NeutralType (Δ : KEnv ι₁) : Kind ι₂ → Set where
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

         (τ₁ : NormalType Δ (★ {ι₁})) →
         (τ₂ : NormalType Δ (★ {ι₂})) → 
         --------
         NormalType Δ (★ {ι₁ ⊔ ι₂})

  `∀    :
      
         {κ : Kind ικ} → (τ : NormalType (Δ ,, κ) (★ {ι})) →
         -------------
         NormalType Δ (★ {ι ⊔ (lsuc ικ)})

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : NormalPred Δ R[ κ₁ ]) → (τ : NormalType Δ (★ {ι})) → 
         ---------------------
         NormalType Δ (★ {ι})             

  ------------------------------------------------------------------
  -- Rω business


  ⦅_⦆ : (ρ : SimpleRow Δ R[ κ ]) → (oρ : True (normalOrdered? ρ)) →
        ----------------------
       NormalType Δ R[ κ ]

--   -- labels
  lab :
    
        (l : Label) → 
        --------
        NormalType Δ (L {ι})

  -- label constant formation
  ⌊_⌋ :
        (τ : NormalType Δ (L {ι})) →
        ----------
        NormalType Δ (★ {ι})

  Π  : 

      (ρ : NormalType Δ R[ (★ {ι}) ]) →
      ------------------
      NormalType Δ (★ {ι})


  Σ  : 

      (ρ : NormalType Δ R[ (★ {ι}) ]) →
      ---------------
      NormalType Δ (★ {ι})

  _─_ : (ρ₂ ρ₁ : NormalType Δ R[ κ ]) → {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
        NormalType Δ R[ κ ]

  _▹ₙ_ : (l : NeutralType Δ (L {ι})) (τ : NormalType Δ κ) → 
         ------------------------------------
         NormalType Δ R[ κ ]

--------------------------------------------------------------------------------
-- Ordered predicate

open IsStrictPartialOrder (SPO) renaming (trans to <-trans)

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

NormalIrrelevantOrdered : ∀ (ρ : SimpleRow Δ R[ κ ]) → Irrelevant (True (normalOrdered? ρ))
NormalIrrelevantOrdered ρ = Dec→Irrelevant (NormalOrdered ρ) (normalOrdered? ρ)

cong-⦅⦆ : {sr₁ sr₂ : SimpleRow Δ R[ κ ]} {wf₁ : True (normalOrdered? sr₁)} {wf₂ : True (normalOrdered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂)
cong-⦅⦆ {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalIrrelevantOrdered sr₁ wf₁ wf₂ = refl


inj-⦅⦆ : {sr₁ sr₂ : SimpleRow Δ R[ κ ]} 
         {wf₁ : True (normalOrdered? sr₁)} 
         {wf₂ : True (normalOrdered? sr₂)} → 
         _≡_ {A = NormalType Δ R[ κ ]} (⦅ sr₁ ⦆ wf₁) (⦅ sr₂ ⦆ wf₂) → 
         sr₁ ≡ sr₂
inj-⦅⦆ {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite NormalIrrelevantOrdered sr₁ wf₁ wf₂ = refl

--------------------------------------------------------------------------------
-- Not simple rows

NotSimpleRow (ne x) = ⊤
NotSimpleRow ((φ <$> τ)) = ⊤
NotSimpleRow (⦅ ρ ⦆ oρ) = ⊥
NotSimpleRow (τ ─ τ₁) = ⊤
NotSimpleRow (x ▹ₙ τ) = ⊤

notSimpleRows? (ne x) _ = yes (left tt)
notSimpleRows? ((τ₁ <$> ρ)) _ = yes (left tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (ne x) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (⦅ ρ₁ ⦆ oρ₁) = no λ { (left ()) ; (right ()) }
notSimpleRows? (⦅ ρ ⦆ oρ) (ρ₁ ─ ρ₂) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) (x ▹ₙ ρ₁) = yes (right tt)
notSimpleRows? (⦅ ρ ⦆ oρ) ((φ <$> _)) = yes (right tt)
notSimpleRows? (ρ₂ ─ ρ₃) _ = yes (left tt)
notSimpleRows? (x ▹ₙ ρ₂) _ = yes (left tt)


cong-─ : {τ₂ υ₂ : NormalType Δ R[ κ ]}
          {τ₁ υ₁ : NormalType Δ R[ κ ]}
          {nsr₁ : True (notSimpleRows? τ₂ τ₁)} 
          {nsr₂ : True (notSimpleRows? υ₂ υ₁)} → 
                 τ₂ ≡ υ₂ → 
                 τ₁ ≡ υ₁ → 
                _≡_ {A = NormalType Δ R[ κ ]} ((τ₂ ─ τ₁) {nsr₁}) ((υ₂ ─ υ₁) {nsr₂})
cong-─ {τ₂ = τ₂} {τ₁ = τ₁} {nsr₁ = x} {x₁} refl refl rewrite Dec→Irrelevant _ (notSimpleRows? τ₂ τ₁) x x₁ = refl

--------------------------------------------------------------------------------
-- There are no neutral types in empty contexts

noNeutrals : NeutralType (∅ {ι}) κ → ⊥

noNeutrals (n · τ) = noNeutrals n 

--------------------------------------------------------------------------------
-- There are no complements in empty contexts 

noComplements : ∀ {ρ₁ ρ₂ ρ₃ : NormalType (∅ {ι}) R[ κ ]}
                  (nsr : True (notSimpleRows? ρ₃ ρ₂)) → 
                  ρ₁ ≡ (ρ₃ ─ ρ₂) {nsr} → 
                  ⊥
noComplements {ρ₁ = ne x₁ ─ _} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ne x₁} {_} {_} nsr refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ((ρ₂ ─ ρ₃) {nsr'})} {_} {_} nsr refl = noComplements {ρ₂ = ρ₃} {ρ₂} nsr' refl
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ (l ▹ₙ ρ₂)} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ⦅ ρ ⦆ oρ ─ ((φ <$> τ))} {_} {_} nsr refl = ⊥-elim (noNeutrals τ)
noComplements {ρ₁ = ((ρ₃ ─ ρ₂) {nsr'}) ─ _} {_} {_} nsr refl = noComplements {ρ₂ = ρ₂} {ρ₃} nsr' refl
noComplements {ρ₁ = (l ▹ₙ ρ₃) ─ _} {_} {_} nsr refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ((φ <$> τ)) ─ _} nsr refl = ⊥-elim (noNeutrals τ)

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
row-canonicity (ρ₂ ─ ρ₁) = tt

row-canonicity-∅ : (ρ : NormalType (∅ {ι}) R[ κ ]) → 
                    ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
                    (ρ ≡ ⦅ xs ⦆ oxs)
row-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
row-canonicity-∅ (⦅ ρ ⦆ oρ) = ρ , oρ , refl
row-canonicity-∅ ((ρ ─ ρ₁) {nsr}) = ⊥-elim (noComplements nsr refl)
row-canonicity-∅ (l ▹ₙ ρ) = ⊥-elim (noNeutrals l)
row-canonicity-∅ ((φ <$> ρ)) = ⊥-elim (noNeutrals ρ)

--------------------------------------------------------------------------------
-- arrow-canonicity

arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl

--------------------------------------------------------------------------------
-- label canonicity

label-canonicity : (l : NormalType Δ (L {ι})) → ⊤ 
label-canonicity (ne x) = tt
label-canonicity (lab l) = tt

label-canonicity-∅ : ∀ (l : NormalType (∅ {ι₁}) (L {ι₂})) → ∃[ s ] (l ≡ lab s)
label-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
label-canonicity-∅ (lab s) = s , refl


--------------------------------------------------------------------------------
-- row "constructors"

εNF : NormalType Δ R[ κ ]
εNF = ⦅ [] ⦆ tt
_▹'_ : Label → NormalType Δ κ → NormalType Δ R[ κ ] 
x ▹' τ = ⦅ [ (x , τ) ] ⦆ tt

--------------------------------------------------------------------------------
-- Admissable constants

UnitNF : NormalType Δ (★ {ι})
UnitNF = Π (⦅ [] ⦆ tt)
