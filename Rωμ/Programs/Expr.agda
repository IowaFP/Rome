module Rωμ.Programs.Expr where

open import Preludes.Level
open import Rωμ
open import Rωμ.GVars

--------------------------------------------------------------------------------
--
-- LamP 
ArithP : Type Δ (★ `→ ★)
ArithP = `λ _ ({!(lab "Const") R▹ Nat)!} ⇒ {!!})

-- eval : Term Δ Φ Γ ?
-- eval = ?

