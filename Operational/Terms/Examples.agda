module Rome.Operational.Terms.Examples where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax

open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Terms.Syntax
-- open import Rome.Operational.Terms.Theorems.Consistency
open import Rome.Operational.Terms.Theorems.Soundness

open import Rome.Operational.Terms.Normal.Syntax

open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- Selection

selT : Type ∅ ★
selT = `∀          -- t
          (`∀       -- z
            ((((lab "l") ▹ t) ≲ z) ⇒ ((Π · z) `→ t))) 
      where 
        t = ` (S Z)
        z = ` Z

sel : Term ∅ selT
sel = Λ (Λ (`ƛ (`λ ((prj d (n-var (T Z))) Π/ # (lab "l")))))
    where
      d = ` Z

⇓selT : NormalType ∅ ★
⇓selT = `∀
          (`∀
          ((⦅ ne (` (S Z)) ∷ [] ⦆ ≲ ne (` Z)) ⇒ (Π (ne (` Z)) `→ ne (` (S Z)))))

_ : ⇓ selT ≡ ⇓selT 
_ = refl

⇓sel : NormalTerm ∅ (⇓ selT)
⇓sel = ⇓Term sel

_ : ⇓sel ≡ Λ (Λ (`ƛ (`λ (prj (` Z) (n-var (T Z)) Π/ # (lab "l")))))
_ = refl
