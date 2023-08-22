{-# OPTIONS --safe #-}
module Rome.Kinds.Syntax where

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

--   κ : Kind    is a second order kind;
-- (`κ : Kind¹ κ) is a predicate stating κ is first order.
data Kind  :  Set
data Kind¹ : Kind → Set


data Kind where
  ★ : Kind
  L : Kind
  R[_] : Kind → Kind
  _`→_ : ∀ {κ} → Kind¹ κ → Kind → Kind

data Kind¹ where
  ★¹ :
 
       -----------
       Kind¹ ★

  L¹ :
 
       -----------
       Kind¹ L

  R₁[_] : 
       {κ : Kind} → Kind¹ κ → 
       ---------------------
       Kind¹ (R[ κ ])

--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _,_  : KEnv → Kind → KEnv
