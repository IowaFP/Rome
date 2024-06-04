module Rome.Types.Substitution.Properties where

open import Preludes.Level
open import Prelude

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Shared.Postulates.FunExt

--------------------------------------------------------------------------------
-- Preservation of meaning across type-var maps, predicate maps, type maps, and
-- contexts.

Δ-map-preservation : ∀ {ℓ₁ ℓ₂}
                     (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂)
                     (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                     (f : Δ-map Δ₁ Δ₂) → Setω
Δ-map-preservation  {ℓ₁} {ℓ₂} Δ₁ Δ₂ H₁ H₂ f =
  ∀ {ℓ₃} {κ : Kind ℓ₃} →
  (x : TVar Δ₁ κ) → _≡_ {a = lsuc ℓ₃} (⟦ x ⟧tv H₁) (⟦ f x ⟧tv H₂)

τ-map-preservation : ∀ {ℓ₁ ℓ₂}
                     (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                     (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                     (f : τ-map Δ₁ Δ₂) →
                     (n : Potatoes) → Setω
τ-map-preservation {ℓ₁}  Δ₁ Δ₂ H₁ H₂ f n =
  ∀ {ℓ₃} {κ : Kind ℓ₃} →
  (τ : Type Δ₁ κ) → _≡_ {a = lsuc ℓ₃} (⟦ τ ⟧t H₁ n) (⟦ f τ ⟧t H₂ n)

π-map-preservation : ∀ {ℓ₁ ℓ₂}
                     (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                     (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                     (f : π-map Δ₁ Δ₂) →
                     (n : Potatoes) → Setω
π-map-preservation  {ℓ₁} Δ₁ Δ₂ H₁ H₂ f n =
  ∀ {ℓ₃}{κ : Kind ℓ₃}
    (π : Pred Δ₁ κ) → _≡_ {a = (lsuc (lsuc ℓ₃))}  (⟦ π ⟧p H₁ n) (⟦ f π ⟧p H₂ n)

Context-preservation : ∀ {ℓ₁ ℓ₂}
                     (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂)
                     (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                     (f : Context Δ₁ Δ₂) →
                     (n : Potatoes) → Setω
Context-preservation  {ℓ₁} {ℓ₂} Δ₁ Δ₂ H₁ H₂ f n =
  ∀ {ℓ₃} {κ : Kind ℓ₃} →
  (x : TVar Δ₁ κ) → _≡_ {a = lsuc ℓ₃} (⟦ x ⟧tv H₁) (⟦ f x ⟧t H₂ n)



--------------------------------------------------------------------------------
-- demo on id.

id : ∀ {ℓ}{X : Set ℓ} → X → X
id x = x

id-pres : ∀ {ℓ₁} (Δ₁ : KEnv ℓ₁) (H : ⟦ Δ₁ ⟧ke) →
          Δ-map-preservation  Δ₁ Δ₁ H H id
id-pres Δ₁ H  x = refl

--------------------------------------------------------------------------------
-- if `f` is a *meaning preserving* Δ-map, then so is its extension.

ext-pres : ∀ {ℓ₁ ℓ₂ ℓ₃}
           (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂)
           (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
           {κ : Kind ℓ₃} →
           (f : Δ-map Δ₁ Δ₂) →
           (Δ-pres : Δ-map-preservation Δ₁ Δ₂ H₁ H₂ f) →
           ∀ (X : ⟦ κ ⟧k) → Δ-map-preservation (Δ₁ ، κ) (Δ₂ ، κ) (H₁ , X) (H₂ , X) (ext f)

ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres X Z = refl
ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres X (S v) = Δ-pres v

--------------------------------------------------------------------------------
--  if `f` is a *meaning preserving* Δ-map, then so is the promotion of `f` to a
-- τ-map.

τ-preservation : ∀ {ℓ₁ ℓ₂}
                 (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                 (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                 (f : Δ-map Δ₁ Δ₂) →
                 (n : Potatoes)
                 (Δ-pres : Δ-map-preservation Δ₁ Δ₂ H₁ H₂ f) →
                 τ-map-preservation Δ₁ Δ₂ H₁ H₂ (rename f) n

π-preservation : ∀ {ℓ₁ ℓ₂}
                 (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                 (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                 (f : Δ-map Δ₁ Δ₂) →
                 (n : Potatoes) →
                 (Δ-pres : Δ-map-preservation Δ₁ Δ₂ H₁ H₂ f) →
                 π-map-preservation Δ₁ Δ₂ H₁ H₂ (renamePred f) n

-- Interesting cases.
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (tvar x) = Δ-pres x -- Δ-pres x' -- Δ-pres H H' x
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (`∀ κ τ) =
  ∀-extensionality
    extensionality
    (λ z → ⟦ τ ⟧t (H₁ , z) n)
    (λ z → ⟦ rename (ext f) τ ⟧t (H₂ , z) n)
    τ-pres
    where
      τ-pres : (x : ⟦ κ ⟧k) → ⟦ τ ⟧t (H₁ , x) n ≡ ⟦ rename (ext f) τ ⟧t (H₂ , x) n
      τ-pres x = τ-preservation
                 (Δ₁ ، κ) (Δ₂ ، κ)
                 (H₁ , x) (H₂ , x)
                 (ext f)
                 n
                 (ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres x)
                 τ
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (`λ κ τ) = extensionality τ-pres
    where
      τ-pres : (x : ⟦ κ ⟧k) → ⟦ τ ⟧t (H₁ , x) n ≡ ⟦ rename (ext f) τ ⟧t (H₂ , x) n
      τ-pres x = τ-preservation
                 (Δ₁ ، κ) (Δ₂ ، κ)
                 (H₁ , x) (H₂ , x)
                 (ext f)
                 n
                 (ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres x)
                 τ
-- -- Uninteresting Cases.
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (lab x) = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (τ₁ `→ τ₂)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ₁
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ₂ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (τ ·[ υ ])
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres υ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (τ ▹ υ)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres υ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (τ R▹ υ)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres υ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ⌊ τ ⌋
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (Π τ)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (Type.Σ τ)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (⌈ τ ⌉· ρ)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (ρ ·⌈ τ ⌉)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (π ⇒ τ)
  rewrite π-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres π
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres τ = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ε = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (μ F)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres F = refl

π-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (ρ₁ ≲ ρ₂)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ₁
  | τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ₂ = refl
π-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres (ρ₁ · ρ₂ ~ ρ₃)
    rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ₁
  |         τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ₂
  |         τ-preservation Δ₁ Δ₂ H₁ H₂ f n Δ-pres ρ₃ = refl

-- --------------------------------------------------------------------------------
-- -- If f is a *meaning preserving* Context, then so is its extension and
-- -- simultaneous substitution.

exts-pres : ∀ {ℓ₁ ℓ₂ ℓ₃}
           (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂)
           (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
           {κ : Kind ℓ₃} →
           (f : Context Δ₁ Δ₂) →
           (n : Potatoes) →
           (Δ-pres : Context-preservation Δ₁ Δ₂ H₁ H₂ f n) →
           ∀ (X : ⟦ κ ⟧k) → Context-preservation (Δ₁ ، κ) (Δ₂ ، κ) (H₁ , X) (H₂ , X) (exts f) n
exts-pres Δ₁ Δ₂ H₁ H₂ f n σ-pres X Z = refl
exts-pres Δ₁ Δ₂ H₁ H₂ {κ} f n σ-pres X (S c)
  rewrite sym (τ-preservation Δ₂ (Δ₂ ، κ) H₂ (H₂ , X)  S n (λ _ → refl) (f c))
  |       sym (σ-pres c) = refl

--------------------------------------------------------------------------------
-- if f is a meaning preserving Context, then so is the the substitution of f
-- (Or: lifting f to a τ-map).

σ/τ-preservation : ∀ {ℓ₁ ℓ₂}
                   (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                   (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                   (f : Context Δ₁ Δ₂) →
                   (n : Potatoes) →
                   (σ-pres : Context-preservation Δ₁ Δ₂ H₁ H₂ f n) →
                   τ-map-preservation Δ₁ Δ₂ H₁ H₂ (subst f) n
σ/π-preservation : ∀ {ℓ₁ ℓ₂}
                   (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                   (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                   (f : Context Δ₁ Δ₂) →
                   (n : Potatoes) →
                   (σ-pres : Context-preservation Δ₁ Δ₂ H₁ H₂ f n) →
                   π-map-preservation Δ₁ Δ₂ H₁ H₂ (substPred f) n

σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (tvar x) = σ-pres x 
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (`∀ κ τ) =
  ∀-extensionality
    extensionality
    (λ z → ⟦ τ ⟧t (H₁ , z) n)
    (λ z → ⟦ subst (exts f) τ ⟧t (H₂ , z) n)
    τ-pres
    where
      τ-pres : (x : ⟦ κ ⟧k) → ⟦ τ ⟧t (H₁ , x) n ≡ ⟦ subst (exts f) τ ⟧t (H₂ , x) n
      τ-pres x = σ/τ-preservation
                 (Δ₁ ، κ) (Δ₂ ، κ)
                 (H₁ , x) (H₂ , x)
                 (exts f)
                 n
                 (exts-pres Δ₁ Δ₂ H₁ H₂ f n σ-pres x)
                 τ
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (`λ κ τ) = extensionality τ-pres
    where
      τ-pres : (x : ⟦ κ ⟧k) → ⟦ τ ⟧t (H₁ , x) n ≡ ⟦ subst (exts f) τ ⟧t (H₂ , x) n
      τ-pres x = σ/τ-preservation
                 (Δ₁ ، κ) (Δ₂ ، κ)
                 (H₁ , x) (H₂ , x)
                 (exts f)
                 n
                 (exts-pres Δ₁ Δ₂ H₁ H₂ f n σ-pres x)
                 τ
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (π ⇒ τ)
  rewrite σ/π-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres π
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ = refl
-- -- Uninteresting Cases.
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (lab x) = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (τ₁ `→ τ₂)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₁
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₂ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (τ ·[ υ ])
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres υ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (τ ▹ υ)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres υ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (τ R▹ υ)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres υ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres ⌊ τ ⌋
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (Π τ)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (Type.Σ τ)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (⌈ τ ⌉· ρ)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres ρ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres ( ρ ·⌈ τ ⌉)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ |
          σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres ρ = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres ε = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (μ F)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres F = refl

σ/π-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (τ₁ ≲ τ₂)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₁
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₂ = refl
σ/π-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres (τ₁ · τ₂ ~ τ₃)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₁
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₂
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f n σ-pres τ₃ = refl

-- --------------------------------------------------------------------------------
-- -- Substitution Lemma.

Substitution : ∀ {ℓΔ ℓκ ℓκ'} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {κ' : Kind ℓκ'}
               (τ : Type (Δ ، κ') κ) (υ : Type Δ κ') (H : _) (n : Potatoes) →
               ⟦ τ ⟧t (H , ⟦ υ ⟧t H n) n ≡ ⟦ subst (Z↦ υ) τ ⟧t H n
Substitution {ℓΔ} {ℓκ} {ℓκ'} {Δ = Δ} {κ' = κ'} τ υ H n = 
  σ/τ-preservation (Δ ، κ') Δ ((H , ⟦ υ ⟧t H n)) H (Z↦ υ) n ctx-pres τ
    where
      ctx-pres : Context-preservation (Δ ، κ') Δ (H , ⟦ υ ⟧t H n) H  (Z↦ υ) n
      ctx-pres Z  = refl -- refl
      ctx-pres (S x) = refl -- refl

-- --------------------------------------------------------------------------------
-- -- Weakening of typing judgments preserves meaning.

Weakening : ∀ {ℓΔ ℓκ ℓκ'} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {κ' : Kind ℓκ'} →
             (τ : Type Δ κ) (H : ⟦ Δ ⟧ke) (X : ⟦ κ' ⟧k) →
             (n : Potatoes) →
             ⟦ τ ⟧t H n ≡ ⟦ weaken τ ⟧t (H , X) n
Weakening {Δ = Δ} {κ' = κ'} τ H X n = 
  τ-preservation Δ (Δ ، κ') H (H , X) S n (λ _ → refl) τ

Weakening₂ : ∀ {ℓΔ ℓκ ℓκA ℓκB} {Δ : KEnv ℓΔ}
               {κ : Kind ℓκ} {κA : Kind ℓκA} {κB : Kind ℓκB} →
             (τ : Type Δ κ) (H : ⟦ Δ ⟧ke) (A : ⟦ κA ⟧k) (B : ⟦ κB ⟧k) →
             (n : Potatoes) →
             ⟦ τ ⟧t H n ≡ ⟦ weaken (weaken τ) ⟧t ((H , A) , B) n
Weakening₂ τ H A B n =  trans (Weakening τ H A n) (Weakening (weaken τ) (H , A) B n)

Weakening₃ : ∀ {ℓΔ ℓκ ℓκA ℓκB ℓκC} {Δ : KEnv ℓΔ}
               {κ : Kind ℓκ} {κA : Kind ℓκA} {κB : Kind ℓκB}  {κC : Kind ℓκC} →
             (τ : Type Δ κ) (H : ⟦ Δ ⟧ke) (A : ⟦ κA ⟧k) (B : ⟦ κB ⟧k) (C : ⟦ κC ⟧k)  →
             (n : Potatoes) →
             ⟦ τ ⟧t H n ≡ ⟦ weaken (weaken (weaken τ)) ⟧t (((H , A) , B) , C) n
Weakening₃ τ H A B C n =  trans (Weakening₂ τ H A B n) (Weakening (weaken (weaken τ)) ((H , A) , B) C n) 
