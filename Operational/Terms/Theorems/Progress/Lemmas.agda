{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Theorems.Progress.Lemmas where

open import Rome.Operational.Prelude
open import Rome.Operational.Containment

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Properties.Substitution

open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.SynAna
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Types.Equivalence.Relation
open import Rome.Operational.Types.Equivalence.Properties

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Soundness


open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Substitution
open import Rome.Operational.Terms.Normal.Reduction

open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.Renaming
open import Rome.Operational.Terms.Normal.Entailment.Properties
