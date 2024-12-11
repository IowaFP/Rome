module Rome.Denotational.Programs.Expr where

open import Rome.Preludes.Level
open import Rome
open import Rome.Denotational.GVars

--------------------------------------------------------------------------------
--
-- LamP 
ArithP : Type Δ (★ ℓ `→ ★ ℓ)
ArithP = `λ _ ({!(lab "Const") R▹ Nat)!} ⇒ {!!})

-- eval : Term Δ Φ Γ ?
-- eval = ?

