{-# OPTIONS --safe #-}
module R2Mu.Kinds.Syntax where

--------------------------------------------------------------------------------
-- Kinds.

-- Second order kinds, i.e.
--   System F₂
-- where
--  F₁   = { ★ , L, R[ F₁ ] }
--  F₂ ::= F₁ → F₂
--
-- In other words, no nesting on LHS of arrow:
--   ★ → (★ → (★ → ★))     | Good
--   (★ → ★) → ★            | Bad

-- In Rω, we must also worry about LHS-nested *rows of type constructors*, i.e.
--   R[ ★ → ★ → ★ ]         | Good
--   R[ ★ ] → (R[ ★ ] → ★)  | Good
--   R [★ → ★] → ★          | Bad
-- 
data Kind₂  :  Set
data Kind₁ : Kind₂ → Set


data Kind₂ where
  ★ : Kind₂
  L : Kind₂
  R[_] : Kind₂ → Kind₂
  _`→_ : ∀ {κ} → Kind₁ κ → Kind₂ → Kind₂

data Kind₁ where
  `★ :
 
       -----------
       Kind₁ ★

  `L :
 
       -----------
       Kind₁ L

  `R : 
       (κ : Kind₂) → Kind₁ κ → 
       ---------------------
       Kind₁ (R[ κ ])


Kind = Kind₂

bad : Kind₂
bad = (`R {!!} {!!}) `→ {!!}

--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _,_  : KEnv → Kind → KEnv
