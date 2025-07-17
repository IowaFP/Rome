-- {-# OPTIONS --safe #-}
module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Data.String using (_<_; _<?_)

--------------------------------------------------------------------------------
-- Types

infixl 5 _·_
infixr 5 _≲_
data Pred (Ty : Set) : Set
data Type {ι₁} (Δ : KEnv ι₁) : ∀ {ι₂} → Kind ι₂ → Set 

SimpleRow : (Ty : Set) → Set 
SimpleRow Ty   = List (Label × Ty)

Ordered : SimpleRow (Type Δ κ) → Set 
ordered? : ∀ (xs : SimpleRow (Type Δ κ)) → Dec (Ordered xs)

--------------------------------------------------------------------------------
-- Predicates

data Pred Ty where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Ty) → 
       --------------------- 
       Pred Ty

  _≲_ : 

       (ρ₁ ρ₂ : Ty) →
       ----------
       Pred Ty  
       
data Type Δ where

  ` : 
      (α : KVar Δ κ) →
      --------
      Type Δ κ

  `λ : {κ₁ : Kind ι₁} {κ₂ : Kind ι₂} → 
      
      (τ : Type (Δ ,, κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ (★ {ι₁})) →
         (τ₂ : Type Δ (★ {ι₂})) → 
         --------
         Type Δ (★ {ι₁ ⊔ ι₂})

  `∀    :
      
         {κ : Kind ικ} → (τ : Type (Δ ,, κ) (★ {ι})) →
         -------------
         Type Δ (★ {ι ⊔ (lsuc ικ)})

  μ     :
      
         (φ : Type Δ ((★ {ι}) `→ (★ {ι}))) → 
         -------------
         Type Δ (★ {ι})

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : Pred (Type Δ R[ κ₁ ])) → (τ : Type Δ (★ {ι})) → 
         ---------------------
         Type Δ (★ {ι})       


  ------------------------------------------------------------------
  -- Rω business

  ⦅_⦆ : (xs : SimpleRow (Type Δ κ)) (ordered : True (ordered? xs)) →
        ----------------------
        Type Δ R[ κ ]

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ (L {ι})

  -- label constant formation
  ⌊_⌋ :
        (τ : Type Δ (L {ι})) →
        ----------
        Type Δ (★ {ι})

  -- Row formation
  _▹_ :
         (l : Type Δ (L {ι})) → (τ : Type Δ κ) → 
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

cong-SimpleRow : {sr₁ sr₂ : SimpleRow (Type Δ κ)} {wf₁ : True (ordered? sr₁)} {wf₂ : True (ordered? sr₂)} → 
                 sr₁ ≡ sr₂ → 
                ⦅ sr₁ ⦆ wf₁ ≡ ⦅ sr₂ ⦆ wf₂
cong-SimpleRow {sr₁ = sr₁} {_} {wf₁} {wf₂} refl rewrite Dec→Irrelevant (Ordered sr₁) (ordered? sr₁) wf₁ wf₂ = refl

--------------------------------------------------------------------------------
-- Syntactic row complement

infix 0 _∈L_

data _∈L_ : (l : Label) → SimpleRow (Type Δ κ) → Set  where
  Here : ∀ {τ : Type Δ κ} {xs : SimpleRow (Type Δ κ)} {l : Label} → 
         l ∈L (l , τ) ∷ xs
  There : ∀ {τ : Type Δ κ} {xs : SimpleRow (Type Δ κ)} {l l' : Label} → 
          l ∈L xs → l ∈L (l' , τ) ∷ xs

_∈L?_ : ∀ (l : Label) (xs : SimpleRow (Type Δ κ)) → Dec (l ∈L xs)
l ∈L? [] = no (λ { () })
l ∈L? ((l' , _) ∷ xs) with l ≟ l' 
... | yes refl = yes Here
... | no  p with l ∈L? xs 
...         | yes p = yes (There p)
...         | no  q = no λ { Here → p refl ; (There x) → q x }


_─s_ : ∀ (xs ys : SimpleRow (Type Δ κ)) → SimpleRow (Type Δ κ)
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
    xs ys : SimpleRow (Type Δ κ)

ordered-cons : ∀ (x : Label × Type Δ κ) (ρ : SimpleRow (Type Δ κ)) → 
               Ordered (x ∷ ρ) → 
               Ordered ρ 
ordered-cons x [] oxρ = tt
ordered-cons (l , snd₁) ((l₁ , snd₂) ∷ ρ) (_ , oxρ) = oxρ 

ordered-swap : ∀ {l l' : Label} {τ τ' : Type Δ κ} {xs : SimpleRow (Type Δ κ)} → 
                l < l' → 
                Ordered ((l' , τ') ∷ xs) → 
                Ordered ((l , τ) ∷ xs)
ordered-swap {xs = []} l<l' oxs = tt
ordered-swap {l = l} {l'} {xs = (l'' , τ'') ∷ xs} l<l' (l'<l'' , oxs) = <-trans {i = l} {j = l'} {k = l''} l<l' l'<l'' , oxs 
                
map-overᵣ : ∀ (ρ : SimpleRow (Type Δ₁ κ₁)) (f : Type Δ₁ κ₁ → Type Δ₁ κ₂) → 
              Ordered ρ → Ordered (map (overᵣ f) ρ)
map-overᵣ [] f oρ = tt
map-overᵣ (x ∷ []) f oρ = tt
map-overᵣ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (map-overᵣ ((l₂ , _) ∷ ρ) f oρ)

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

-- Unit : Type Δ (★ {ι})
-- Unit = Π · ε

-- Empty : Type Δ (★ {ι}) 
-- Empty = Σ · ε 


--------------------------------------------------------------------------------
-- Denotation

open import Rome.IndexCalculus using (Row)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤') 
 
⟦_⟧k : Kind ι → Set (lsuc ι)
⟦ ★ {ι} ⟧k = Set ι
⟦ κ₁ `→ κ₂ ⟧k = ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
⟦ L {ι} ⟧k = ⊤' {lsuc ι}
⟦ R[ k ] ⟧k = Row ⟦ k ⟧k

⟦_⟧ke : KEnv ι → Set (lsuc ι)
⟦ (∅ {ι = ι}) ⟧ke = ⊤' {lsuc ι}
⟦ Δ ,, κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k


⟦_⟧tv : KVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

⟦_⟧t : Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k 
⟦ ` α ⟧t η = ⟦ α ⟧tv η
⟦ `λ {κ₁ = κ₁} τ ⟧t η = λ (x : ⟦ κ₁ ⟧k ) → ⟦ τ ⟧t (η , x)
⟦ τ₁ · τ₂ ⟧t η = {! (⟦ τ₁ ⟧t η) (⟦ τ₂ ⟧t η)  !}
⟦ τ₁ `→ τ₂ ⟧t η = ⟦ τ₁ ⟧t η  → ⟦ τ₂ ⟧t η
⟦ `∀ τ ⟧t η = {!   !}
⟦ μ τ ⟧t η = {!   !}
⟦ π ⇒ τ ⟧t η = {!   !}
⟦ ⦅ xs ⦆ ordered ⟧t η = {!   !}
⟦ lab l ⟧t η = {!   !}
⟦ ⌊ τ ⌋ ⟧t η = {!   !}
⟦ τ ▹ τ₁ ⟧t η = {!   !}
⟦ τ <$> τ₁ ⟧t η = {!   !}
⟦ Π ⟧t η = {!   !}
⟦ Σ ⟧t η = {!   !}
⟦ τ₂ ─ τ₁ ⟧t η = {!   !} 

-- wts that 
--  - ⟦ τ ⟧t ≡ ⟦ ⇓ τ ⟧NF (would need functional extensionality)
--  - if Δ ⊢ τ ≡t υ : κ then ⟦ τ ⟧t ≡ ⟦ υ ⟧t 
-- I'm not sure if I want to let define ⟦_⟧t as the first line. Then 
-- the second line follows from completeness. Is this a cop out?
-- A counter---I only define term reduction on normal types. So 
-- my goal is:
--   soundness : ∀ {τ : NormalType ∅ ★} {M N : NormalTerm ∅ τ} → 
--               M —→ N → ⟦ M ⟧ ≡ ⟦ N ⟧
-- Where ⟦_⟧, the meaning of terms, is typed by
--              ⟦_⟧ : NormalTerm Γ τ → ⟦ Γ ⟧ →  ⟦ τ ⟧. 
-- so in this case we do not need a meaning of `Type`, just of `NormalType`.
-- Pros of independnent definitions of ⟦_⟧ : Type and ⟦_⟧ : NormalType:
--   - Shows that ⟦_⟧ on `Type`s obeys definitional equality
--   - cooler?
-- Pros of defining as ⟦ τ ⟧t ≡ ⟦ ⇓ τ ⟧NF:
--   - metatheory for free
--   - No need to relate two differing implementations
--   - Don't actually need the meaning of non-normal types
--   - I said I would deliver the soundness claim above, 
--     who is going to quibble? Just get the Ph.D.