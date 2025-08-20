{-# OPTIONS --safe #-}
module Rome.Operational.All where 

--------------------------------------------------------------------------------
-- This dir 

open import Rome.Operational.Containment
open import Rome.Operational.Prelude 

--------------------------------------------------------------------------------
-- Kinds 

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.Decidability
open import Rome.Operational.Kinds.GVars 

--------------------------------------------------------------------------------
-- Types  

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution

--------------------------------------------------------------------------------
-- Types.Equivalence

open import Rome.Operational.Types.Equivalence.Relation
open import Rome.Operational.Types.Equivalence.Admissable
open import Rome.Operational.Types.Equivalence.Properties

--------------------------------------------------------------------------------
-- Types.Normal

open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Syntax

open import Rome.Operational.Types.Normal.Properties.Decidability
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

--------------------------------------------------------------------------------
-- Types.Properties

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution

--------------------------------------------------------------------------------
-- Types.Semantic

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Types.Theorems

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Consistency
open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Terms 

open import Rome.Operational.Terms.Normal.GVars 
open import Rome.Operational.Terms.Normal.Reduction 
open import Rome.Operational.Terms.Normal.Renaming
open import Rome.Operational.Terms.Normal.Substitution 
open import Rome.Operational.Terms.Normal.SynAna
open import Rome.Operational.Terms.Normal.Syntax 

open import Rome.Operational.Terms.Normal.Entailment.Properties 

open import Rome.Operational.Terms.Theorems.Progress
