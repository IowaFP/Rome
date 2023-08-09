module R2Mu.Types.Decidability where
--------------------------------------------------------------------------------
-- Agda stuffs.
open import Agda.Primitive

--------------------------------------------------------------------------------
-- Relation stuffs. (prune unused.)

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

open R2Mu.Kinds
open R2Mu.Types.Syntax

