module Rome.Operational.Types.Properties.Stability where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
--

stability   : ∀ (τ : NormalType Δ κ) → ⇓ (embed τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → reflect (embedNE τ) idEnv ≡ reflectNE τ

stability   = {!!}
stabilityNE = {!!}

