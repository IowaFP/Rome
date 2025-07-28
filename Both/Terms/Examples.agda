module Rome.Both.Terms.Examples where

open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Renaming

open import Rome.Both.Types.Normal.Syntax

open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Types.Semantic.NBE

open import Rome.Both.Terms.Syntax
-- open import Rome.Both.Terms.Theorems.Soundness
open import Rome.Both.Terms.Theorems.Completeness

open import Rome.Both.Terms.Normal.Syntax

open import Rome.Both.Containment

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
