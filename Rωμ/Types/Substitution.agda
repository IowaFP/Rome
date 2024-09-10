
module Rωμ.Types.Substitution where

open import Preludes.Level
open import Preludes.Relation
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.String  using (_≟_)

open import Rωμ.Kinds
open import Rωμ.Types.Syntax

--------------------------------------------------------------------------------
-- Defs.

-- A Δ-map (renaming) maps type vars in environment Δ₁ to environment Δ₂.
Δ-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
Δ-map Δ₁ Δ₂ =
  (∀ {κ : Kind} → TVar Δ₁ κ → TVar Δ₂ κ)

-- A mapping from types to types.
τ-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
τ-map Δ₁ Δ₂ = (∀ {κ : Kind} → Type Δ₁ κ → Type Δ₂ κ)

Row-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
Row-map Δ₁ Δ₂ = (∀ {κ : Kind} → Row Δ₁ κ → Row Δ₂ κ)

-- A mapping from preds to preds.
π-map : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
π-map Δ₁ Δ₂ = ∀ {κ : Kind} → Pred Δ₁ κ → Pred Δ₂ κ

-- A Context maps type vars to types.
Context : ∀ (Δ₁ : KEnv) (Δ₂ : KEnv) → Set
Context Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → Type Δ₂ κ

--------------------------------------------------------------------------------
-- Extension.
--
-- Given a map from variables in one Context to variables in another, extension
-- yields a map from the first Context extended to the second Context similarly
-- extended.

ext : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {ι : Kind} →
         Δ-map Δ₁ Δ₂ →
         Δ-map (Δ₁ ، ι) (Δ₂ ، ι)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming.
--
-- Renaming is a necessary prelude to substitution، enabling us to “rebase” a
-- type from one Context to another.

rename : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Δ-map Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂
renamePred : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Δ-map Δ₁ Δ₂ →
           π-map Δ₁ Δ₂
renameRow : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Δ-map Δ₁ Δ₂ →
           Row-map Δ₁ Δ₂

rename δ (tvar v) = tvar (δ v)
rename δ (τ `→ υ) = rename δ τ `→ rename δ υ
rename δ (`∀ κ τ) = `∀ κ (rename (ext δ) τ)
rename δ (`λ s τ) = `λ s (rename (ext δ) τ)
rename δ (τ ·[ υ ]) = rename δ τ ·[ rename δ υ ]
rename δ (lab l) = lab l
rename δ (t ▹ v) = (rename δ t) ▹ (rename δ v)
rename δ (⌊ t ⌋) = ⌊ rename δ t ⌋
rename δ (t R▹ v) = rename δ t R▹ rename δ v
rename δ (Π r) = Π (rename δ r)
rename δ (Type.Σ r) = Type.Σ (rename δ r)
rename δ (π ⇒ τ) = renamePred δ π ⇒ rename δ τ
rename δ (↑ f) = ↑ rename δ f
rename δ (f ↑) = rename δ f ↑
rename δ ε = ε
rename δ (⦃- ρ -⦄) = ⦃- renameRow δ ρ -⦄
rename δ (μ X) = μ (rename δ X)

∉?-≈-renameRow : ∀ {κ : Kind} {Δ₁ : KEnv} {Δ₂ : KEnv}  → 
       (l : Label) (m : Row Δ₁ κ) (δ : Δ-map Δ₁ Δ₂) →
       l ∉ m → l ∉ renameRow δ m

renameRow δ (l ▹ τ) = (l ▹ rename δ τ)
renameRow δ ((l ▹ τ ， m) {ev}) = (l ▹ rename δ τ ， (renameRow δ m)) {∉?-≈-renameRow l m δ ev}

∉?-≈-renameRow l₁ (l₂ ▹ τ) δ ev with l₁ ≟ l₂ 
... | yes refl = ⊥-elim ev
... | no  p = tt
∉?-≈-renameRow l₁ (l₂ ▹ τ ， m) δ ev with l₁ ≟ l₂ 
... | yes refl = ⊥-elim ev
... | no  p = ∉?-≈-renameRow l₁ m δ ev 

renamePred ρ (ρ₁ ≲ ρ₂) = rename ρ ρ₁ ≲ rename ρ ρ₂
renamePred ρ (ρ₁ · ρ₂ ~ ρ₃) = rename ρ ρ₁ ·  rename ρ ρ₂ ~ rename ρ ρ₃

--------------------------------------------------------------------------------
-- Weakening (of a typing derivation.)

weaken : ∀ {Δ : KEnv} {κ : Kind} →
           τ-map Δ (Δ ، κ)
weaken = rename S

--------------------------------------------------------------------------------
-- Repeated weakening (helpers)
K = weaken
K¹ = weaken
K² : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} →
           τ-map Δ (Δ ، κ₁ ، κ₂)
K² = λ x → weaken (weaken x)

K³ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {κ₃ : Kind} →
           τ-map Δ (Δ ، κ₁ ، κ₂ ، κ₃)
K³ = λ x → K¹ (K² x)

K⁴ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {κ₃ : Kind} {κ₄ : Kind} →
           τ-map Δ (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄)
K⁴ = λ x → K² (K² x)

--------------------------------------------------------------------------------
-- Simultaneous Substitution.
--
-- Instead of substituting a closed term for a single variable, we provide a
-- map that takes each free variable of the original type to another
-- tye. Further, the substituted terms are over an arbitrary Context, and need
-- not be closed.

exts : ∀
         {Δ₁ : KEnv} {Δ₂ : KEnv}
         {ι : Kind} →
         Context Δ₁ Δ₂ →
         Context (Δ₁ ، ι) (Δ₂ ، ι)
exts θ Z = tvar Z
exts θ (S x) = rename S (θ x)

--------------------------------------------------------------------------------
-- Substitution.
--

subst : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Context Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂

substPred : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} →
          Context Δ₁ Δ₂ →
          π-map Δ₁ Δ₂
substRow : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} →
           Context Δ₁ Δ₂ →
           Row-map Δ₁ Δ₂


subst θ (tvar x) = θ x
subst θ (τ `→ υ) = subst θ τ `→ subst θ υ
subst θ (`∀ κ τ) = `∀ κ (subst (exts θ) τ)
subst θ (`λ s τ) = `λ s (subst (exts θ) τ)
subst θ (τ ·[ υ ]) = subst θ τ ·[ subst θ υ ]
subst θ (lab l) = lab l
subst θ (t ▹ v) = (subst θ t) ▹ (subst θ v)
subst θ (⌊ t ⌋) = ⌊ subst θ t ⌋
subst θ (t R▹ v) = subst θ t R▹ subst θ v
subst θ (Π r) = Π (subst θ r)
subst θ (Type.Σ r) = Type.Σ (subst θ r)
subst θ (π ⇒ τ) = substPred θ π ⇒ subst θ τ
subst θ (↑ f) = ↑ subst θ f
subst θ (f ↑) = subst θ f ↑
subst θ ε = ε
subst θ (μ X) = μ (subst θ X)
subst θ ⦃- ρ -⦄ = ⦃- substRow θ ρ -⦄

∉?-≈-substRow : ∀ {κ : Kind} {Δ₁ : KEnv} {Δ₂ : KEnv}  → 
       (l : Label) (m : Row Δ₁ κ) (θ : Context Δ₁ Δ₂) →
       l ∉ m → l ∉ substRow θ m

substRow θ (l ▹ τ) = (l ▹ subst θ τ)
substRow θ ((l ▹ τ ， m) {ev}) = (l ▹ subst θ τ ， (substRow θ m)) {∉?-≈-substRow l m θ ev}

∉?-≈-substRow l₁ (l₂ ▹ τ) θ ev with l₁ ≟ l₂ 
... | yes refl = ⊥-elim ev
... | no  p = tt
∉?-≈-substRow l₁ (l₂ ▹ τ ， m) θ ev with l₁ ≟ l₂ 
... | yes refl = ⊥-elim ev
... | no  p = ∉?-≈-substRow l₁ m θ ev 

substPred θ (ρ₁ ≲ ρ₂)      = subst θ ρ₁ ≲ subst θ ρ₂
substPred θ (ρ₁ · ρ₂ ~ ρ₃) = subst θ ρ₁ ·  subst θ ρ₂ ~ subst θ ρ₃

--------------------------------------------------------------------------------
-- Single substitution.

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {Δ : KEnv} {κ : Kind} →
        Type Δ κ → Context (Δ ، κ) Δ
Z↦ τ Z = τ
Z↦ τ (S x) = tvar x

-- Regular ol' substitution.
_β[_] : {Δ : KEnv} {κ : Kind}{ι : Kind}
         → Type (Δ ، ι) κ → Type Δ ι → Type Δ κ
τ β[ υ ] = subst (Z↦ υ) τ
