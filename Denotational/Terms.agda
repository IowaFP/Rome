module Rome.Denotational.Terms where
--------------------------------------------------------------------------------
-- Re-export Syntax & Semantics

open import Rome.Denotational.Terms.Syntax hiding (S² ; S³ ; S⁴ ; S⁵) public
open import Rome.Denotational.Terms.Admissible public
open import Rome.Denotational.Terms.Semantics public -- extensionality
