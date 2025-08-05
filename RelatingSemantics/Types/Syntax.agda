module Rome.RelatingSemantics.Types.Syntax where 

open import Rome.RelatingSemantics.Prelude
open import Rome.RelatingSemantics.Kinds.Syntax
open import Rome.RelatingSemantics.Kinds.GVars

data NormalType (Δ : KEnv ι₁) : Kind ι₂ → Set

