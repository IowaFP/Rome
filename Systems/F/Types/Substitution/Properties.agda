module F.Types.Substitution.Properties where


open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app)

open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)

open import F.Kinds
open import F.Types
open import F.Types.Substitution
open import Shared.Postulates.FunExt

--------------------------------------------------------------------------------
-- Preservation of meaning across type-var maps, type maps, and
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
                     (f : τ-map Δ₁ Δ₂) → Setω
τ-map-preservation {ℓ₁}  Δ₁ Δ₂ H₁ H₂ f =
  ∀ {ℓ₃} {κ : Kind ℓ₃} →
  (τ : Type Δ₁ κ) → _≡_ {a = lsuc ℓ₃} (⟦ τ ⟧t H₁) (⟦ f τ ⟧t H₂)

Context-preservation : ∀ {ℓ₁ ℓ₂}
                     (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂)
                     (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                     (f : Context Δ₁ Δ₂) → Setω
Context-preservation  {ℓ₁} {ℓ₂} Δ₁ Δ₂ H₁ H₂ f =
  ∀ {ℓ₃} {κ : Kind ℓ₃} →
  (x : TVar Δ₁ κ) → _≡_ {a = lsuc ℓ₃} (⟦ x ⟧tv H₁) (⟦ f x ⟧t H₂)



-- --------------------------------------------------------------------------------
-- -- demo on id.

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
           ∀ (X : ⟦ κ ⟧k) → Δ-map-preservation (Δ₁ , κ) (Δ₂ , κ) (H₁ , X) (H₂ , X) (ext f)

ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres X Z = refl
ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres X (S v) = Δ-pres v

--------------------------------------------------------------------------------
--  if `f` is a *meaning preserving* Δ-map, then so is the promotion of `f` to a
-- τ-map.

τ-preservation : ∀ {ℓ₁ ℓ₂}
                 (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                 (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                 (f : Δ-map Δ₁ Δ₂) →
                 (Δ-pres : Δ-map-preservation Δ₁ Δ₂ H₁ H₂ f) →
                 τ-map-preservation Δ₁ Δ₂ H₁ H₂ (rename f)

-- Interesting cases.
τ-preservation Δ₁ Δ₂ H₁ H₂ f Δ-pres (tvar x') = Δ-pres x' -- Δ-pres H H' x
τ-preservation Δ₁ Δ₂ H₁ H₂ f Δ-pres (`∀ κ τ) =
  ∀-extensionality
    extensionality
    (λ z → ⟦ τ ⟧t (H₁ , z))
    (λ z → ⟦ rename (ext f) τ ⟧t (H₂ , z))
    τ-pres
    where
      τ-pres : (x : ⟦ κ ⟧k) → ⟦ τ ⟧t (H₁ , x) ≡ ⟦ rename (ext f) τ ⟧t (H₂ , x)
      τ-pres x = τ-preservation
                 (Δ₁ , κ) (Δ₂ , κ)
                 (H₁ , x) (H₂ , x)
                 (ext f)
                 (ext-pres Δ₁ Δ₂ H₁ H₂ f Δ-pres x)
                 τ
-- -- Uninteresting Cases.
τ-preservation Δ₁ Δ₂ H₁ H₂ f Δ-pres U = refl
τ-preservation Δ₁ Δ₂ H₁ H₂ f Δ-pres (τ₁ `→ τ₂)
  rewrite τ-preservation Δ₁ Δ₂ H₁ H₂ f Δ-pres τ₁
  |       τ-preservation Δ₁ Δ₂ H₁ H₂ f Δ-pres τ₂ = refl

--------------------------------------------------------------------------------
-- If f is a *meaning preserving* Context, then so is its extension and
-- simultaneous substitution.

exts-pres : ∀ {ℓ₁ ℓ₂ ℓ₃}
           (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂)
           (H₁ : ⟦ Δ₁ ⟧ke) (H₂ : ⟦ Δ₂ ⟧ke)
           {κ : Kind ℓ₃} →
           (f : Context Δ₁ Δ₂) →
           (Δ-pres : Context-preservation Δ₁ Δ₂ H₁ H₂ f) →
           ∀ (X : ⟦ κ ⟧k) → Context-preservation (Δ₁ , κ) (Δ₂ , κ) (H₁ , X) (H₂ , X) (exts f)
exts-pres Δ₁ Δ₂ H₁ H₂ f σ-pres X Z = refl
exts-pres Δ₁ Δ₂ H₁ H₂ {κ} f σ-pres X (S c)
  rewrite sym (τ-preservation Δ₂ (Δ₂ , κ) H₂ (H₂ , X)  S (λ _ → refl) (f c))
  |       sym (σ-pres c) = refl

--------------------------------------------------------------------------------
-- if f is a meaning preserving Context, then so is the the substitution of f
-- (Or: lifting f to a τ-map).

σ/τ-preservation : ∀ {ℓ₁ ℓ₂}
                   (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) →
                   (H₁ : ⟦ Δ₁ ⟧ke)(H₂ : ⟦ Δ₂ ⟧ke) →
                   (f : Context Δ₁ Δ₂) →
                   (σ-pres : Context-preservation Δ₁ Δ₂ H₁ H₂ f) →
                   τ-map-preservation Δ₁ Δ₂ H₁ H₂ (subst f)


σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f σ-pres (tvar x) = σ-pres x
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f σ-pres (`∀ κ τ) =
  ∀-extensionality
    extensionality
    (λ z → ⟦ τ ⟧t (H₁ , z))
    (λ z → ⟦ subst (exts f) τ ⟧t (H₂ , z))
    τ-pres
    where
      τ-pres : (x : ⟦ κ ⟧k) → ⟦ τ ⟧t (H₁ , x) ≡ ⟦ subst (exts f) τ ⟧t (H₂ , x)
      τ-pres x = σ/τ-preservation
                 (Δ₁ , κ) (Δ₂ , κ)
                 (H₁ , x) (H₂ , x)
                 (exts f)
                 (exts-pres Δ₁ Δ₂ H₁ H₂ f σ-pres x)
                 τ
-- -- Uninteresting Cases.
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f σ-pres U = refl
σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f σ-pres (τ₁ `→ τ₂)
  rewrite σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f σ-pres τ₁
  |       σ/τ-preservation Δ₁ Δ₂ H₁ H₂ f σ-pres τ₂ = refl

-- --------------------------------------------------------------------------------
-- -- Substitution Lemma.

Substitution : ∀ {ℓΔ ℓκ ℓκ'} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {κ' : Kind ℓκ'}
               (τ : Type (Δ , κ') κ) (υ : Type Δ κ') H →
               ⟦ τ ⟧t (H , ⟦ υ ⟧t H) ≡ ⟦ subst (Z↦ υ) τ ⟧t H
Substitution {ℓΔ} {ℓκ} {ℓκ'} {Δ = Δ} {κ' = κ'} τ υ H = σ/τ-preservation
  (Δ , κ') Δ ((H , ⟦ υ ⟧t H)) H (Z↦ υ) ctx-pres τ
    where
      ctx-pres : Context-preservation (Δ , κ') Δ (H , ⟦ υ ⟧t H) H (Z↦ υ)
      ctx-pres Z = refl
      ctx-pres (S x) = refl

-- --------------------------------------------------------------------------------
-- -- Weakening of typing judgments preserves meaning.

Weakening : ∀ {ℓΔ ℓκ ℓκ'} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {κ' : Kind ℓκ'} →
             (τ : Type Δ κ) (H : ⟦ Δ ⟧ke) (X : ⟦ κ' ⟧k)  →
             ⟦ τ ⟧t H ≡ ⟦ weaken τ ⟧t (H , X)
Weakening {Δ = Δ} {κ' = κ'} τ H X = 
  τ-preservation Δ (Δ , κ') H (H , X) S (λ _ → refl) τ

Weakening₂ : ∀ {ℓΔ ℓκ ℓκA ℓκB} {Δ : KEnv ℓΔ}
               {κ : Kind ℓκ} {κA : Kind ℓκA} {κB : Kind ℓκB} →
             (τ : Type Δ κ) (H : ⟦ Δ ⟧ke) (A : ⟦ κA ⟧k) (B : ⟦ κB ⟧k)  →
             ⟦ τ ⟧t H ≡ ⟦ weaken (weaken τ) ⟧t ((H , A) , B)
Weakening₂ τ H A B =  trans (Weakening τ H A) (Weakening (weaken τ) (H , A) B)

Weakening₃ : ∀ {ℓΔ ℓκ ℓκA ℓκB ℓκC} {Δ : KEnv ℓΔ}
               {κ : Kind ℓκ} {κA : Kind ℓκA} {κB : Kind ℓκB}  {κC : Kind ℓκC} →
             (τ : Type Δ κ) (H : ⟦ Δ ⟧ke) (A : ⟦ κA ⟧k) (B : ⟦ κB ⟧k) (C : ⟦ κC ⟧k)  →
             ⟦ τ ⟧t H ≡ ⟦ weaken (weaken (weaken τ)) ⟧t (((H , A) , B) , C)
Weakening₃ τ H A B C =  trans (Weakening₂ τ H A B) (Weakening (weaken (weaken τ)) ((H , A) , B) C) 
