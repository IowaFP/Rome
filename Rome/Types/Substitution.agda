
module Rome.Types.Substitution where

open import Preludes.Level
open import Preludes.Relation
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.String  using (_≟_)

open import Rome.Kinds
open import Rome.Types.Syntax

--------------------------------------------------------------------------------
-- Defs.

-- A Δ-map (renaming) maps type vars in environment Δ₁ to environment Δ₂.
Δ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Δ-map Δ₁ Δ₂ =
  (∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → TVar Δ₂ κ)

-- A mapping from types to types.
τ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
τ-map Δ₁ Δ₂ = (∀ {ℓ₃} {κ : Kind ℓ₃} → Type Δ₁ κ → Type Δ₂ κ)

Row-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Row-map Δ₁ Δ₂ = (∀ {ℓ₃} {κ : Kind ℓ₃} → MultiRow Δ₁ κ → MultiRow Δ₂ κ)

-- A mapping from preds to preds.
π-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
π-map Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} → Pred Δ₁ κ → Pred Δ₂ κ

-- A Context maps type vars to types.
Context : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Context Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → Type Δ₂ κ

--------------------------------------------------------------------------------
-- Extension.
--
-- Given a map from variables in one Context to variables in another, extension
-- yields a map from the first Context extended to the second Context similarly
-- extended.

ext : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} {ι : Kind ℓ₃} →
         Δ-map Δ₁ Δ₂ →
         Δ-map (Δ₁ ، ι) (Δ₂ ، ι)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming.
--
-- Renaming is a necessary prelude to substitution، enabling us to “rebase” a
-- type from one Context to another.

rename : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Δ-map Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂
renamePred : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Δ-map Δ₁ Δ₂ →
           π-map Δ₁ Δ₂
renameRow : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
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
rename δ (Row ρ) = Row (renameRow δ ρ)
rename δ (μ X) = μ (rename δ X)

pfftR : ∀ {ℓ ℓ₁ ℓ₂} {κ : Kind ℓ} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂}  → 
       (l : Label) (m : MultiRow Δ₁ κ) (δ : Δ-map Δ₁ Δ₂) →
       True (l ∉? m) → True (l ∉? renameRow δ m)

renameRow δ (l ▹I τ) = (l ▹I rename δ τ)
renameRow δ ((l ▹ τ ， m) {ev}) = (l ▹ rename δ τ ， (renameRow δ m)) {pfftR l m δ ev}

pfftR l₁ (l₂ ▹I τ) δ ev = ev
pfftR l₁ (l₂ ▹ τ ， m) δ ev with l₁ ≟ l₂ 
... | yes refl = ⊥-elim ev
... | no  p = pfftR l₁ m δ ev 

renamePred ρ (ρ₁ ≲ ρ₂) = rename ρ ρ₁ ≲ rename ρ ρ₂
renamePred ρ (ρ₁ · ρ₂ ~ ρ₃) = rename ρ ρ₁ ·  rename ρ ρ₂ ~ rename ρ ρ₃

--------------------------------------------------------------------------------
-- Weakening (of a typing derivation.)

weaken : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
           τ-map Δ (Δ ، κ)
weaken = rename S

--------------------------------------------------------------------------------
-- Repeated weakening (helpers)
K = weaken
K¹ = weaken
K² : ∀ {ℓΔ ℓ₁ ℓ₂} {Δ : KEnv ℓΔ} {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
           τ-map Δ (Δ ، κ₁ ، κ₂)
K² = λ x → weaken (weaken x)

K³ : ∀ {ℓΔ ℓ₁ ℓ₂ ℓ₃} {Δ : KEnv ℓΔ} {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} {κ₃ : Kind ℓ₃} →
           τ-map Δ (Δ ، κ₁ ، κ₂ ، κ₃)
K³ = λ x → K¹ (K² x)

K⁴ : ∀ {ℓΔ ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Δ : KEnv ℓΔ} {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} {κ₃ : Kind ℓ₃} {κ₄ : Kind ℓ₄} →
           τ-map Δ (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄)
K⁴ = λ x → K² (K² x)

--------------------------------------------------------------------------------
-- Simultaneous Substitution.
--
-- Instead of substituting a closed term for a single variable, we provide a
-- map that takes each free variable of the original type to another
-- tye. Further, the substituted terms are over an arbitrary Context, and need
-- not be closed.


exts : ∀ {ℓ₁ ℓ₂ ℓ₃}
         {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂}
         {ι : Kind ℓ₃} →
         Context Δ₁ Δ₂ →
         Context (Δ₁ ، ι) (Δ₂ ، ι)
exts θ Z = tvar Z
exts θ (S x) = rename S (θ x)

--------------------------------------------------------------------------------
-- Substitution.
--

subst : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Context Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂

substPred : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
          Context Δ₁ Δ₂ →
          π-map Δ₁ Δ₂
substRow : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
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
subst θ (Row ρ) = Row (substRow θ ρ)

pfft : ∀ {ℓ ℓ₁ ℓ₂} {κ : Kind ℓ} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂}  → 
       (l : Label) (m : MultiRow Δ₁ κ) (θ : Context Δ₁ Δ₂) →
       True (l ∉? m) → True (l ∉? substRow θ m)

substRow θ (l ▹I τ) = (l ▹I subst θ τ)
substRow θ ((l ▹ τ ， m) {ev}) = (l ▹ subst θ τ ， (substRow θ m)) {pfft l m θ ev}

pfft l₁ (l₂ ▹I τ) θ ev = ev
pfft l₁ (l₂ ▹ τ ， m) θ ev with l₁ ≟ l₂ 
... | yes refl = ⊥-elim ev
... | no  p = pfft l₁ m θ ev 

substPred θ (ρ₁ ≲ ρ₂)      = subst θ ρ₁ ≲ subst θ ρ₂
substPred θ (ρ₁ · ρ₂ ~ ρ₃) = subst θ ρ₁ ·  subst θ ρ₂ ~ subst θ ρ₃

--------------------------------------------------------------------------------
-- Single substitution.

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
        Type Δ κ → Context (Δ ، κ) Δ
Z↦ τ Z = τ
Z↦ τ (S x) = tvar x

-- Regular ol' substitution.
_β[_] : ∀ {ℓΔ ℓκ ℓι} {Δ : KEnv ℓΔ} {κ : Kind ℓκ}{ι : Kind ℓι}
         → Type (Δ ، ι) κ → Type Δ ι → Type Δ κ
τ β[ υ ] = subst (Z↦ υ) τ
