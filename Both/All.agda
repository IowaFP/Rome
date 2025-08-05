module Rome.Both.All where 

--------------------------------------------------------------------------------
-- This dir 

open import Rome.Both.Containment
open import Rome.Both.Prelude 

--------------------------------------------------------------------------------
-- Kinds 

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars 

--------------------------------------------------------------------------------
-- Types  

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.SynAna
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.Substitution

--------------------------------------------------------------------------------
-- Types.Equivalence

open import Rome.Both.Types.Equivalence.Relation
open import Rome.Both.Types.Equivalence.Admissable
open import Rome.Both.Types.Equivalence.Properties

--------------------------------------------------------------------------------
-- Types.Normal

open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Syntax

open import Rome.Both.Types.Normal.Properties.Renaming
open import Rome.Both.Types.Normal.Properties.Substitution

--------------------------------------------------------------------------------
-- Types.Properties

open import Rome.Both.Types.Properties.Renaming
open import Rome.Both.Types.Properties.Substitution

--------------------------------------------------------------------------------
-- Types.Semantic

open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming
open import Rome.Both.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Types.Theorems

open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Terms 

open import Rome.Both.Terms.Normal.GVars 
open import Rome.Both.Terms.Normal.Reduction 
open import Rome.Both.Terms.Normal.Renaming
open import Rome.Both.Terms.Normal.Substitution 
open import Rome.Both.Terms.Normal.SynAna
open import Rome.Both.Terms.Normal.Syntax 

open import Rome.Both.Terms.Normal.Entailment.Properties 

open import Rome.Both.Terms.Theorems.Progress
