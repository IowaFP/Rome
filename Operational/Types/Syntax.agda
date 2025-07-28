{-# OPTIONS --safe #-}
module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Data.String using (_<_; _<?_)

--------------------------------------------------------------------------------
-- Types

infixl 5 _·_
infixr 5 _≲_
data Pred (Ty : KEnv → Kind → Set) Δ : Kind → Set
data Type Δ : Kind → Set 

SimpleRow : (Ty : KEnv → Kind → Set) → KEnv → Kind → Set 
SimpleRow Ty Δ ★        = ⊥
SimpleRow Ty Δ L        = ⊥
SimpleRow Ty Δ (_ `→ _) = ⊥
SimpleRow Ty Δ R[ κ ]   = List (Label × Ty Δ κ)

Ordered : SimpleRow Type Δ R[ κ ] → Set 
ordered? : ∀ (xs : SimpleRow Type Δ R[ κ ]) → Dec (Ordered xs)

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
      (α : TVar Δ κ) →
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

  -- Row formation
  _▹_ :
         (l : Type Δ L) → (τ : Type Δ κ) → 
         -------------------
         Type Δ R[ κ ]

  _<$>_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :
          {notLabel : True (notLabel? κ)} →
          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          {notLabel : True (notLabel? κ)} →
          ----------------
          Type Δ (R[ κ ] `→ κ)

  _─_ : 
      
        Type Δ R[ κ ] → Type Δ R[ κ ] → 
        ---------------------------------
        Type Δ R[ κ ]

--------------------------------------------------------------------------------
-- Simple row well-formedness

Ordered [] = ⊤
Ordered (x ∷ []) = ⊤
Ordered ((l₁ , _) ∷ (l₂ , τ) ∷ xs) = l₁ < l₂ × Ordered ((l₂ , τ) ∷ xs)

ordered? [] = yes tt
ordered? (x ∷ []) = yes tt
ordered? ((l₁ , _) ∷ (l₂ , _) ∷ xs) with l₁ <? l₂ | ordered? ((l₂ , _) ∷ xs)
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})

cong-SimpleRow : {sr₁ sr₂ : SimpleRow Type Δ R[ κ ]} {wf₁ : True (ordered? sr₁)} {wf₂ : True (ordered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                ⦅ sr₁ ⦆ wf₁ ≡ ⦅ sr₂ ⦆ wf₂
cong-SimpleRow {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite Dec→Irrelevant (Ordered sr₁) (ordered? sr₁) wf₁ wf₂ = refl

--------------------------------------------------------------------------------
-- Syntactic row complement

infix 0 _∈L_

data _∈L_ : (l : Label) → SimpleRow Type Δ R[ κ ] → Set  where
  Here : ∀ {τ : Type Δ κ} {xs : SimpleRow Type Δ R[ κ ]} {l : Label} → 
         l ∈L (l , τ) ∷ xs
  There : ∀ {τ : Type Δ κ} {xs : SimpleRow Type Δ R[ κ ]} {l l' : Label} → 
          l ∈L xs → l ∈L (l' , τ) ∷ xs

_∈L?_ : ∀ (l : Label) (xs : SimpleRow Type Δ R[ κ ]) → Dec (l ∈L xs)
l ∈L? [] = no (λ { () })
l ∈L? ((l' , _) ∷ xs) with l ≟ l' 
... | yes refl = yes Here
... | no  p with l ∈L? xs 
...         | yes p = yes (There p)
...         | no  q = no λ { Here → p refl ; (There x) → q x }


_─s_ : ∀ (xs ys : SimpleRow Type Δ R[ κ ]) → SimpleRow Type Δ R[ κ ]
[] ─s ys = []
((l , τ) ∷ xs) ─s ys with l ∈L? ys 
... | yes _ = xs ─s ys
... | no  _ = (l , τ) ∷ (xs ─s ys)

--------------------------------------------------------------------------------
-- Ordered lemmas 

open import Relation.Binary.Structures using (IsStrictPartialOrder)
open import Data.String.Properties renaming (<-isStrictPartialOrder-≈ to SPO)
open IsStrictPartialOrder (SPO) renaming (trans to <-trans)

private
  variable
    l : Label
    τ : Type Δ κ 
    xs ys : SimpleRow Type Δ R[ κ ]

ordered-cons : ∀ (x : Label × Type Δ κ) (ρ : SimpleRow Type Δ R[ κ ]) → 
               Ordered (x ∷ ρ) → 
               Ordered ρ 
ordered-cons x [] oxρ = tt
ordered-cons (l , snd₁) ((l₁ , snd₂) ∷ ρ) (_ , oxρ) = oxρ 

ordered-swap : ∀ {l l' : Label} {τ τ' : Type Δ κ} {xs : SimpleRow Type Δ R[ κ ]} → 
                l < l' → 
                Ordered ((l' , τ') ∷ xs) → 
                Ordered ((l , τ) ∷ xs)
ordered-swap {xs = []} l<l' oxs = tt
ordered-swap {l = l} {l'} {xs = (l'' , τ'') ∷ xs} l<l' (l'<l'' , oxs) = <-trans {i = l} {j = l'} {k = l''} l<l' l'<l'' , oxs 
                
map-map₂ : ∀ (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) (f : Type Δ₁ κ₁ → Type Δ₁ κ₂) → 
              Ordered ρ → Ordered (map (map₂ f) ρ)
map-map₂ [] f oρ = tt
map-map₂ (x ∷ []) f oρ = tt
map-map₂ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (map-map₂ ((l₂ , _) ∷ ρ) f oρ)

ordered-─s-cons : Ordered ((l , τ) ∷ xs) → 
        Ordered ((l , τ) ∷ (xs ─s ys))
ordered-─s-cons {xs = []} oxs = tt
ordered-─s-cons {l = l} {τ = τ} {xs = (l' , τ') ∷ xs} {ys = ys} (l<l' , oxs') with l' ∈L? ys 
...| yes p = ordered-─s-cons (ordered-swap {l = l} {l'} {τ} {τ'} l<l' oxs')
...| no  p = l<l' , ordered-─s-cons oxs'
                   
ordered-─s : Ordered xs →
             Ordered (xs ─s ys)
ordered-─s {xs = []} {ys} oxs = tt
ordered-─s {xs = ((l , τ) ∷ xs)} {ys} oxs with l ∈L? ys
... | yes _  = ordered-─s (ordered-cons (l , τ) xs oxs)
ordered-─s  {xs = (l , τ) ∷ []} {ys} oxs | no p = tt
ordered-─s {xs = (l , τ) ∷ (l' , τ') ∷ xs} {ys} (l<l' , oxs) | no p with l' ∈L? ys | ordered-─s {ys = ys} oxs
... | no q | ih = l<l' , ih
... | yes q | ih = ordered-─s-cons (ordered-swap l<l' oxs)

--------------------------------------------------------------------------------
-- The empty row is the empty simple row

ε : Type Δ R[ κ ]
ε = ⦅ [] ⦆ tt

--------------------------------------------------------------------------------
-- Admissable constants

-- for partial application of infix fmap.
`↑ : Type Δ ((κ₁ `→ κ₂) `→ R[ κ₁ ] `→ R[ κ₂ ])
`↑ = `λ (`λ (` (S Z) <$> ` Z))

-- Flapping. See https://hoogle.haskell.org/?hoogle=f%20(a%20-%3E%20b)%20-%3E%20a%20-%3E%20f%20b%20
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a

Unit : Type Δ ★
Unit = Π · ε

Empty : Type Δ ★ 
Empty = Σ · ε 

-- Example simple row
sr : Type Δ R[ ★ ] 
sr = ⦅ ("a" , Unit) ∷ ("b" , Empty) ∷ ("c" , ((`λ (` Z)) · Unit)) ∷ ("d" , Unit) ∷ [] ⦆ tt
