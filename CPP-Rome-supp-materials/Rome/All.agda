{-# OPTIONS --safe #-}
module Rome.All where 

--------------------------------------------------------------------------------
-- This dir 

open import Rome.Containment
open import Rome.Prelude 

--------------------------------------------------------------------------------
-- Kinds 

open import Rome.Kinds.Syntax
open import Rome.Kinds.Decidability
open import Rome.Kinds.GVars 

--------------------------------------------------------------------------------
-- Types  

open import Rome.Types.Syntax
open import Rome.Types.Renaming
open import Rome.Types.Substitution

--------------------------------------------------------------------------------
-- Types.Equivalence

open import Rome.Types.Equivalence.Relation
open import Rome.Types.Equivalence.Properties

--------------------------------------------------------------------------------
-- Types.Normal

open import Rome.Types.Normal.Renaming
open import Rome.Types.Normal.Substitution
open import Rome.Types.Normal.Syntax

open import Rome.Types.Normal.Properties.Decidability
open import Rome.Types.Normal.Properties.Renaming
open import Rome.Types.Normal.Properties.Substitution

--------------------------------------------------------------------------------
-- Types.Properties

open import Rome.Types.Properties.Renaming
open import Rome.Types.Properties.Substitution

--------------------------------------------------------------------------------
-- Types.Semantic

open import Rome.Types.Semantic.Syntax
open import Rome.Types.Semantic.Renaming
open import Rome.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Types.Theorems

open import Rome.Types.Theorems.Soundness
open import Rome.Types.Theorems.Consistency
open import Rome.Types.Theorems.Stability
