{-# OPTIONS --allow-unsolved-metas --guardedness --copatterns #-}
module Rome.Terms.Semantics where
 
open import Preludes.Level
open import Prelude
 
open import Preludes.Partiality
open import Shared.Lib.Equality

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Types.Substitution.Properties -- extensionality
open import Rome.Terms.Syntax
open import Rome.Equivalence -- extensionality
open import Rome.Entailment -- extensionality

open import IndexCalculus
open import IndexCalculus.Properties
import IndexCalculus as Ix


--------------------------------------------------------------------------------
-- The meaning of environments.


private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ι : Level
    ℓΔ ℓΓ ℓΦ ℓκ ℓκ₁ ℓκ₂ ℓκ₃ : Level
    κ κ' : Kind ℓκ
    κ₁ : Kind ℓκ₁
    κ₂ : Kind ℓκ₂
    κ₃ : Kind ℓκ₃
    Δ : KEnv ℓΔ

⟦_⟧e : Env Δ ℓΓ → ⟦ Δ ⟧ke → Potatoes → Set ℓΓ
⟦ ε ⟧e H n = ⊤
⟦ Γ ، τ ⟧e H n = ⟦ Γ ⟧e H n × ⟦ τ ⟧t H n

--------------------------------------------------------------------------------
-- The meaning of variables.

⟦_⟧v : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
       Var Γ τ → (H : ⟦ Δ ⟧ke) → (n : Potatoes) → ⟦ Γ ⟧e H n → ⟦ τ ⟧t H n
⟦ Z ⟧v H n (η , x) = x
⟦ S v ⟧v H n (η , x) = ⟦ v ⟧v H n η

--------------------------------------------------------------------------------
-- Denotational Weakening Lemma.

weaken⟦_⟧e : ∀ {ℓΔ ℓΓ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Γ : Env Δ ℓΓ) → (H : ⟦ Δ ⟧ke) → (n : Potatoes) → (⟦Γ⟧ : ⟦ Γ ⟧e H n) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΓ Γ ⟧e (H , X) n
weaken⟦ ε ⟧e H ⟦Γ⟧ X n = tt
weaken⟦_⟧e {Δ = Δ} {κ = κ}  (Γ ، τ) H n (⟦Γ⟧ , ⟦τ⟧) X
  rewrite τ-preservation Δ (Δ ، κ) H (H , X) S n (λ _ → refl) τ = weaken⟦ Γ ⟧e H n ⟦Γ⟧ X , ⟦τ⟧

weaken⟦_⟧pe : ∀ {ℓΔ ℓΦ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Φ : PEnv Δ ℓΦ) → (H : ⟦ Δ ⟧ke) → (n : Potatoes) → (⟦Φ⟧ : ⟦ Φ ⟧pe H n) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΦ Φ ⟧pe (H , X) n
weaken⟦ ε ⟧pe H ⟦Φ⟧ X n = tt
weaken⟦_⟧pe {Δ = Δ} {κ} (Φ , π) H n (⟦Φ⟧ , ⟦π⟧) X
  rewrite π-preservation Δ (Δ ، κ) H (H , X) S n (λ _ → refl) π = weaken⟦ Φ ⟧pe H n ⟦Φ⟧ X , ⟦π⟧

--------------------------------------------------------------------------------
-- -- The meaning of terms.

-- open _↔_
-- open _≃_

postulate
  pfftΦ : {Φ : PEnv Δ ℓΦ} → (H : ⟦ Δ ⟧ke) → (n : Potatoes) →  ⟦ Φ ⟧pe H (ℕ.suc n) → ⟦ Φ ⟧pe H n
  pfftΓ : {Γ : Env Δ ℓΓ} → (H : ⟦ Δ ⟧ke) → (n : Potatoes) → ⟦ Γ ⟧e H (ℕ.suc n) → ⟦ Γ ⟧e H n

⟦_⟧ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓ)} →
        Term Δ Φ Γ τ →
        (H : ⟦ Δ ⟧ke) → 
        (n₁ n₂ n₃ : Potatoes) →
        ⟦ Φ ⟧pe H n₁ → ⟦ Γ ⟧e H n₂ → ⟦ τ ⟧t H n₃
⟦ var x ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ `λ τ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ c · c₁ ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ `Λ κ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ c ·[ υ ] ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ `ƛ π c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ c ·⟨ x ⟩ ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ lab l ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ c ▹ c₁ ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ c / c₁ ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ (c Term.⊹ c₁) π ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Term.prj c π ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Term.Π c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Π⁻¹ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ t-≡ c x ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Term.inj c x ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Term.Σ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Σ⁻¹ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ (c Term.▿ c₁) x ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ syn ρ φ₁ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ ana ρ φ₁ τ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ Term.fold c c₁ c₂ c₃ ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ In c ⟧ H n₁ n₂ Prelude.zero φ η = tt
⟦ In c ⟧ H n₁ n₂ (Prelude.suc n₃) φ η = {!⟦ c ⟧ H n₁ n₂ n₃ φ η!}
⟦ recΣ c ⟧ H n₁ n₂ n₃ φ η = {!!}
⟦ ▿μ c c₁ x ⟧ H n₁ n₂ n₃ φ η = {!!}
-- ⟦ var x ⟧ H n φ η = ⟦ x ⟧v H n η
-- ⟦ `λ _ M ⟧ H n φ η = λ x → ⟦ M ⟧ H n φ (η , x)
-- ⟦ M · N ⟧ H n φ η = ⟦ M ⟧ H n φ η (⟦ N ⟧ H n φ η)
-- ⟦ (`Λ κ M) ⟧ H n φ η = λ (X : ⟦ κ ⟧k) → ⟦ M ⟧ (H , X) n (weaken⟦ _ ⟧pe H n φ X) (weaken⟦ _ ⟧e H n η X)
-- ⟦ _·[_] {τ = τ} M υ ⟧ H n φ η
--   rewrite (sym (Substitution τ υ H n)) = ⟦ M ⟧ H n φ η (⟦ υ ⟧t H n)
-- ⟦ `ƛ _ M ⟧ H n φ η = λ x → ⟦ M ⟧ H n (φ , x) η
-- ⟦ M ·⟨ D ⟩ ⟧ H n φ η = ⟦ M ⟧ H n φ η (⟦ D ⟧n H n φ)
-- ⟦ (r₁ ⊹ r₂) π ⟧ H n φ η i
--   with ⟦ π ⟧n H n φ | ⟦ r₁ ⟧ H n φ η | ⟦ r₂ ⟧ H n φ η
-- ... | c , _ | r | r' with c i
-- ... | left (n , eq) rewrite (sym eq) = r n
-- ... | right (n , eq) rewrite (sym eq) = r' n
-- ⟦ lab s ⟧ H n φ η  = tt
-- ⟦ prj r π ⟧ H n φ η i with ⟦ r ⟧ H n φ η | ⟦ π ⟧n H n φ i
-- ... | r' | n , eq rewrite eq = r' n
-- ⟦ M ▹ N ⟧ H n φ η = ⟦ N ⟧ H n φ η
-- ⟦ M / N ⟧ H n φ η = ⟦ M ⟧ H n φ η
-- ⟦ t-≡ {τ = τ}{υ = υ} M τ≡υ ⟧ H n φ η rewrite sym (⟦ τ≡υ ⟧eq H n) = ⟦ M ⟧ H n φ η
-- ⟦ inj M π ⟧ H n φ η with ⟦ M ⟧ H n φ η 
-- ... | i , τ with ⟦ π ⟧n H n φ i
-- ...   | m , eq rewrite eq = m , τ
-- ⟦ (M ▿ N) π ⟧ H n φ η (p₃-i , P) with ⟦ M ⟧ H n φ η | ⟦ N ⟧ H n φ η | ⟦ π ⟧n H n φ
-- ... | ρ₁-elim | ρ₂-elim | (l , r)  with l p₃-i
-- ... | left  s@(ρ₁-i , eq) rewrite (sym eq) = ρ₁-elim (ρ₁-i , P)
-- ... | right s@(ρ₂-i , eq) rewrite (sym eq) = ρ₂-elim (ρ₂-i , P)
-- ⟦ syn {Δ = Δ} {κ = κ} ρ f M ⟧ H₀ n φ η i = 
--   ≡-elim (sym (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd ⟦ρ⟧ i)))
--   (⟦ M ⟧ H₀ n φ η tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) evidence tt)
--     where
--       ⟦ρ⟧ = ⟦ ρ ⟧t H₀ n
--       ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) n
--       ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) n
--       evidence : sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
--                  ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i)) n
--       evidence rewrite sym ⟦ρ⟧≡⟦weaken³ρ⟧ =  recombine ⟦ρ⟧ i

-- ⟦ ana {Δ = Δ} {κ = κ} ρ f τ M ⟧ H₀ n φ η (i , X) =
--   ≡-elim (sym ⟦τ⟧≡⟦weaken³τ⟧)
--   (⟦ M ⟧ H₀ n φ η tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) evidence tt (≡-elim (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd (⟦ ρ ⟧t H₀ n) i)) X))
--     where
--       ⟦ρ⟧ = ⟦ ρ ⟧t H₀ n
--       ⟦τ⟧≡⟦weaken³τ⟧ = Weakening₃ τ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) n
--       ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) n
--       ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) n
--       evidence : sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
--                  ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i)) n
--       evidence rewrite sym ⟦ρ⟧≡⟦weaken³ρ⟧ =  recombine ⟦ρ⟧ i
-- ⟦ Term.Π s ⟧ H n φ η fzero = ⟦ s ⟧ H n φ η
-- ⟦ Term.Π s ⟧ H n φ η (fsuc ())
-- ⟦ Π⁻¹ r ⟧ H n φ η = ⟦ r ⟧ H n φ η fzero
-- ⟦ Term.Σ s ⟧ H n φ η = fzero , (⟦ s ⟧ H n φ η)
-- ⟦ Σ⁻¹ v ⟧ H n φ η with ⟦ v ⟧ H n φ η
-- ... | fzero , M = M

-- ⟦ fold {ℓ₁ = ℓ₁} {ρ = ρ} {υ = υ} M₁ M₂ M₃ N ⟧ H n φ η with 
--   ⟦ M₁ ⟧ H n φ η | ⟦ M₂ ⟧ H n φ η | ⟦ M₃ ⟧ H n φ η | ⟦ N ⟧ H n φ η
-- ... | op | _+_ | e | r = Ix.fold ⟦ρ⟧ f _+_ e r
--   where
--     ⟦ρ⟧ = ⟦ ρ ⟧t H n
--     ⟦υ⟧ = ⟦ υ ⟧t H n
--     f : ∀ (τ : Set ℓ₁) (y : Row {lsuc ℓ₁} (Set ℓ₁)) →
--                  (Ix._·_~_ (sing τ) y ⟦ρ⟧) → τ → ⟦υ⟧
--     f τ y ev t rewrite Weakening₃ υ H tt τ y n =
--       op tt τ y (≡-elim weak-ev≡ev ev) tt t 
--         where
--           weak-ev≡ev :
--             Ix._·_~_ (sing τ) y ⟦ρ⟧
--             ≡
--             Ix._·_~_ (sing τ) y (⟦ K³ ρ ⟧t (((H , tt) , τ) , y) n)
--           weak-ev≡ev rewrite Weakening₃ ρ H tt τ y n = refl
-- ⟦ In M ⟧ H n φ η = {!⟦ M ⟧ H n φ η!}
-- ⟦ recΣ f ⟧ H n φ η    = {!⟦ f ⟧ H n φ η!}
-- ⟦ ▿μ d d₁ x ⟧ H n φ η = {!!}
