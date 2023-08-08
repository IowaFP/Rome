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

--   κ : Kind₂    is a second order kind;
-- (`κ : Kind¹ κ) is a predicate stating κ is first order.
data Kind₂  :  Set
data Kind¹ : Kind₂ → Set


data Kind₂ where
  ★ : Kind₂
  L : Kind₂
  R[_] : Kind₂ → Kind₂
  _`→_ : ∀ {κ} → Kind¹ κ → Kind₂ → Kind₂

data Kind¹ where
  ★₁ :
 
       -----------
       Kind¹ ★

  L₁ :
 
       -----------
       Kind¹ L

  R₁[_] : 
       {κ : Kind₂} → Kind¹ κ → 
       ---------------------
       Kind¹ (R[ κ ])


Kind = Kind₂


--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _,_  : KEnv → Kind → KEnv
