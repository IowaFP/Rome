module R2Mu.Examples.KindChecking where

open import R2Mu.Kinds.Syntax
open import R2Mu.Types.Syntax
import R2Mu.Types.Pre as Pre
open import R2Mu.Types.Checking
open import Data.Maybe

open Pre.Type

--------------------------------------------------------------------------------
--

_ : Maybe (Type ε U ★)
_ = ⊢ₖ? ε U ★


open import Data.Nat using (ℕ ; zero ; suc)

x : Maybe (Type ε ((`λ ★ (tvar zero) ·[ U ]) (★¹ `→ ★)) ★)
x = ⊢ₖ? ε (((`λ ★ (tvar zero)) ·[ U ]) (★¹ `→ ★)) ★
 
r : Maybe (Type ε (Π (Σ U)) ★)
r = ⊢ₖ? ε (Π (Σ U)) ★ 

open import Data.String

pl = Pre.lab "l"
l : Maybe (Type ε (lab "l") L)
l = ⊢ₖ? ε (lab "l") L

pu = Pre.lab "u"
u : Type ε (lab "u") L
u = (lab "u")



butts = ⊢ₖ? ε (`∀ R[ ★ ] (((pl R▹ U) Pre.· (pl R▹ U) ~ (tvar zero)) ⦂ ★ ⇒ (Π (tvar 0) `→ U))) ★

_ = butts
