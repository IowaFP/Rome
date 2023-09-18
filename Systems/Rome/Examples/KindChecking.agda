module Rome.Examples.KindChecking where

open import Rome.Kinds.Syntax
open import Rome.Types.Syntax
import Rome.Pre.Types as Pre
open import Rome.Types.Checking
open import Data.Product

open Pre.Type
open import Shared.Monads.Fuck
--------------------------------------------------------------------------------
--

open import Data.Nat using (ℕ ; zero ; suc)

-- inference
t₁ :  Fuck? (∃[ κ ] (Type ε κ))
t₁ = ε ⊢? (((`λ ★ (tvar zero)) ·[ U ]))


-- Checking.
t₁' :  Fuck? (Type ε ★)
t₁' = ε ⊢ (((`λ ★ (tvar zero)) ·[ U ])) ⦂? ★ 


pl = Pre.lab "l"
pu = Pre.lab "u"
t₂ = ε ⊢? (`∀ R[ ★ ] (((pl R▹ U) Pre.· (pl R▹ U) ~ (tvar zero)) ⦂ ★ ⇒ (Π (tvar 0) `→ U)))
t₃ = ε ⊢? (`λ R[ ★ ] (`λ (★ `→ ★) (⌈ tvar 0 ⌉· (tvar 1))))

butts = ε ⊢ (`∀ R[ ★ ] (((pl R▹ U) Pre.· (pl R▹ U) ~ (tvar zero)) ⦂ ★ ⇒ (Π (tvar 0) `→ U))) ⦂? ★

