module F where

--------------------------------------------------------------------------------
-- Load & typecheck *all* modules.

-- Types.
open import F.Types public
open import F.Types.Substitution as FSub public

-- Terms.
open import F.Terms public -- extensionality

