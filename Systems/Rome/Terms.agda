{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Terms where
--------------------------------------------------------------------------------
-- Re-export Syntax & Semantics

open import Rome.Terms.Syntax hiding (S² ; S³ ; S⁴ ; S⁵) public
open import Rome.Terms.Admissible public
open import Rome.Terms.Semantics public -- extensionality
