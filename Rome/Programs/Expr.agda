module Rome.Programs.Expr where

open import Preludes.Level
open import Rome
open import Rome.GVars

--------------------------------------------------------------------------------
--
-- LamP 
ArithP : Type Δ (★ ℓ `→ ★ ℓ)
ArithP = `λ _ ({!(lab "Const") R▹ Nat)!} ⇒ {!!})

-- eval : Term Δ Φ Γ ?
-- eval = ?

