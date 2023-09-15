module Rome.Examples.KindChecking where

open import Rome.Kinds.Syntax
open import Rome.Types.Syntax
import Rome.Types.Pre as Pre
open import Rome.Types.Checking
open import Data.Maybe

open Pre.Type

--------------------------------------------------------------------------------
--

open import Data.Nat using (ℕ ; zero ; suc)

t₁ = ε ⊢ₖ? (((`λ ★ (tvar zero)) ·[ U ]))

pl = Pre.lab "l"
pu = Pre.lab "u"
t₂ = ε ⊢ₖ? (`∀ R[ ★ ] (((pl R▹ U) Pre.· (pl R▹ U) ~ (tvar zero)) ⦂ ★ ⇒ (Π (tvar 0) `→ U)))
t₃ = ε ⊢ₖ? (`λ R[ ★ ] (`λ (★ `→ ★) (⌈ tvar 0 ⌉· (tvar 1))))



-- x : Maybe (Type ε ((`λ ★ (tvar zero) ⦂ (★ `→ ★) ·[ U ])) ★)
-- x = ⊢ₖ? ε (((`λ ★ (tvar zero)) ⦂ (★ `→ ★) ·[ U ])) ★
 
-- r : Maybe (Type ε (Π (Σ U)) ★)
-- r = ⊢ₖ? ε (Π (Σ U)) ★ 

-- open import Data.String


-- l : Maybe (Type ε (lab "l") L)
-- l = ⊢ₖ? ε (lab "l") L

-- pu = Pre.lab "u"
-- u : Type ε (lab "u") L
-- u = (lab "u")



-- butts = ⊢ₖ? ε (`∀ R[ ★ ] (((pl R▹ U) Pre.· (pl R▹ U) ~ (tvar zero)) ⦂ ★ ⇒ (Π (tvar 0) `→ U))) ★

-- _ = butts
