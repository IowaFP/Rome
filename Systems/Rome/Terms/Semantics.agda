{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Terms.Semantics where
 
open import Preludes.Level
open import Prelude
 
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

⟦_⟧e : Env Δ ℓΓ → ⟦ Δ ⟧ke → Set ℓΓ
⟦ ε ⟧e H = ⊤
⟦ Γ ، τ ⟧e H = ⟦ Γ ⟧e H × ⟦ τ ⟧t H

--------------------------------------------------------------------------------
-- The meaning of variables.

⟦_⟧v : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
       Var Γ τ → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → ⟦ τ ⟧t H
⟦ Z ⟧v H (η , x) = x
⟦ S v ⟧v H (η , x) = ⟦ v ⟧v H η


--------------------------------------------------------------------------------
-- Denotational Weakening Lemma.

weaken⟦_⟧e : ∀ {ℓΔ ℓΓ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Γ : Env Δ ℓΓ) → (H : ⟦ Δ ⟧ke) → (⟦Γ⟧ : ⟦ Γ ⟧e H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΓ Γ ⟧e (H , X)
weaken⟦ ε ⟧e H ⟦Γ⟧ X = tt
weaken⟦_⟧e {Δ = Δ} {κ = κ}  (Γ ، τ) H (⟦Γ⟧ , ⟦τ⟧) X
  rewrite τ-preservation Δ (Δ ، κ) H (H , X) S (λ _ → refl) τ = weaken⟦ Γ ⟧e H ⟦Γ⟧ X , ⟦τ⟧

weaken⟦_⟧pe : ∀ {ℓΔ ℓΦ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Φ : PEnv Δ ℓΦ) → (H : ⟦ Δ ⟧ke) → (⟦Φ⟧ : ⟦ Φ ⟧pe H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΦ Φ ⟧pe (H , X)
weaken⟦ ε ⟧pe H ⟦Φ⟧ X = tt
weaken⟦_⟧pe {Δ = Δ} {κ} (Φ , π) H (⟦Φ⟧ , ⟦π⟧) X
  rewrite π-preservation Δ (Δ ، κ) H (H , X) S (λ _ → refl) π = weaken⟦ Φ ⟧pe H ⟦Φ⟧ X , ⟦π⟧

--------------------------------------------------------------------------------
-- -- The meaning of terms.

-- open _↔_
-- open _≃_
-- open import Data.Maybe using (Maybe ; just ; nothing ; _>>=_) 

join-Maybe : {A : Set ℓ} → Maybe (Maybe A) → Maybe A
join-Maybe (just m) = m
join-Maybe nothing = nothing

join' : {τ : Type Δ (★ ℓ)} {H : ⟦ Δ ⟧ke} → Maybe (⟦ τ ⟧t H) → ⟦ τ ⟧t H
join' {τ = tvar x} m = {!!}
join' {τ = τ `→ τ₁} m = {!!}
join' {τ = `∀ κ τ} m = {!!}
join' {τ = τ ·[ τ₁ ]} m = {!!}
join' {τ = π ⇒ τ} m = {!!}
join' {τ = τ ▹ τ₁} m = {!!}
join' {τ = ⌊ τ ⌋} m = tt
join' {τ = Type.Π τ} m = {!!}
join' {τ = Type.Σ τ} m = {!!}
join' {τ = μ τ} m = {!!}


return : ∀ {ℓ} {A : Set ℓ} → A → Maybe A
return = just

⟦_⟧ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓ)} →
        Term Δ Φ Γ τ →
        (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ Γ ⟧e H → 
        Potatoes → (⟦ τ ⟧t H)
⟦ var x ⟧ H φ η n = ⟦ x ⟧v H η
⟦ `λ _ M ⟧ H φ η n = {!!} -- just (λ x → {!⟦ M ⟧ H φ (η , x) n!}) -- λ x →  
⟦ M · N ⟧ H φ η n = {!!} -- with (⟦ M ⟧ H φ η n)
-- ... | just x = {!!}
-- ... | nothing = {!join !}
-- ⟦ (`Λ κ M) ⟧ H φ η n = 
--   λ (X : ⟦ κ ⟧k) → ⟦ M ⟧ (H , X) (weaken⟦ _ ⟧pe H φ X) (weaken⟦ _ ⟧e H η X) n
-- ⟦ _·[_] {τ = τ} M υ ⟧ H φ η n
--   rewrite (sym (Substitution τ υ H)) = ⟦ M ⟧ H φ η n (⟦ υ ⟧t H)
-- ⟦ `ƛ _ M ⟧ H φ η n = λ x → ⟦ M ⟧ H (φ , x) η n
-- ⟦ M ·⟨ D ⟩ ⟧ H φ η n = ⟦ M ⟧ H φ η n (⟦ D ⟧n H φ)
-- ⟦ (r₁ ⊹ r₂) π ⟧ H φ η n = (⟦ r₁ ⟧ H φ η n) Ix.⊹ (⟦ r₂ ⟧ H φ η n) Using (⟦ π ⟧n H φ)
-- ⟦ lab s ⟧ H φ η n  = tt
-- ⟦ prj r π ⟧ H φ η n i with ⟦ r ⟧ H φ η n | ⟦ π ⟧n H φ i
-- ... | r' | n , eq rewrite eq = r' n
-- ⟦ M ▹ N ⟧ H φ η n = ⟦ N ⟧ H φ η n
-- ⟦ M / N ⟧ H φ η n = ⟦ M ⟧ H φ η n
-- ⟦ t-≡ {τ = τ}{υ = υ} M τ≡υ ⟧ H φ η n 
--   rewrite sym (⟦ τ≡υ ⟧eq H) = ⟦ M ⟧ H φ η n
-- ⟦ inj M π ⟧ H φ η n = Ix.inj (⟦ π ⟧n H φ) (⟦ M ⟧ H φ η n)
-- ⟦ (M ▿ N) π ⟧ H φ η n with ⟦ M ⟧ H φ η n | ⟦ N ⟧ H φ η n | ⟦ π ⟧n H φ
-- ... | ρ₁-elim | ρ₂-elim | ev = ρ₁-elim ▿ ρ₂-elim Using ev
-- -- This logic should be moved to IndexCalculus.Records
-- ⟦ syn {Δ = Δ} {κ = κ} ρ f M ⟧ H₀ φ η n i = 
--   ≡-elim (sym (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd ⟦ρ⟧ i)))
--   (⟦ M ⟧ H₀ φ η n tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) evidence tt)
--     where
--       ⟦ρ⟧ = ⟦ ρ ⟧t H₀
--       ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
--       ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
--       evidence : sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
--                  ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
--       evidence rewrite sym ⟦ρ⟧≡⟦weaken³ρ⟧ =  recombine ⟦ρ⟧ i
-- -- This logic should be moved to IndexCalculus.Variants
-- ⟦ ana {Δ = Δ} {κ = κ} ρ f τ M ⟧ H₀ φ η n (i , X) =
--   ≡-elim (sym ⟦τ⟧≡⟦weaken³τ⟧)
--   (⟦ M ⟧ H₀ φ η n tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i) evidence tt (≡-elim (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd (⟦ ρ ⟧t H₀) i)) X))
--     where
--       ⟦ρ⟧ = ⟦ ρ ⟧t H₀
--       ⟦τ⟧≡⟦weaken³τ⟧ = Weakening₃ τ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
--       ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
--       ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
--       evidence : sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
--                  ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
--       evidence rewrite sym ⟦ρ⟧≡⟦weaken³ρ⟧ =  recombine ⟦ρ⟧ i
-- ⟦ Term.Π s ⟧ H φ η n fzero = ⟦ s ⟧ H φ η n
-- ⟦ Term.Π s ⟧ H φ η n (fsuc ())
-- ⟦ Π⁻¹ r ⟧ H φ η n = ⟦ r ⟧ H φ η n fzero
-- ⟦ Term.Σ s ⟧ H φ η n = fzero , (⟦ s ⟧ H φ η n)
-- ⟦ Σ⁻¹ v ⟧ H φ η n with ⟦ v ⟧ H φ η n
-- ... | fzero , M = M
-- ⟦ fold {ℓ₁ = ℓ₁} {ρ = ρ} {υ = υ} M₁ M₂ M₃ N ⟧ H φ η n with 
--   ⟦ M₁ ⟧ H φ η n | ⟦ M₂ ⟧ H φ η n | ⟦ M₃ ⟧ H φ η n | ⟦ N ⟧ H φ η n
-- ... | op | _+_ | e | r = Ix.fold ⟦ρ⟧ f _+_ e r
--   where
--     ⟦ρ⟧ = ⟦ ρ ⟧t H
--     ⟦υ⟧ = ⟦ υ ⟧t H
--     f : ∀ (τ : Set ℓ₁) (y : Row {lsuc ℓ₁} (Set ℓ₁)) →
--                  (Ix._·_~_ (sing τ) y ⟦ρ⟧) → τ → ⟦υ⟧
--     f τ y ev t rewrite Weakening₃ υ H tt τ y =
--       op tt τ y (≡-elim weak-ev≡ev ev) tt t 
--         where
--           weak-ev≡ev :
--             Ix._·_~_ (sing τ) y ⟦ρ⟧
--             ≡
--             Ix._·_~_ (sing τ) y (⟦ K³ ρ ⟧t (((H , tt) , τ) , y))
--           weak-ev≡ev rewrite Weakening₃ ρ H tt τ y = refl
-- -- Recursive Terms.
-- ------------------
-- ⟦ In M fmap ⟧ H φ η n = In (⟦ M ⟧ H φ η n)
-- ⟦ recΣ {ℓ = ℓ} {ρ = ρ} {τ = τ} f fmap ⟧ H φ η n (In e) with
--   ⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H | ⟦ f ⟧ H φ η n (⟦ ρ ⟧t H) (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H) 
-- ... | ⟦ε⟧ | ⟦f⟧ rewrite 
--   sym (Weakening₂ τ H (⟦ ρ ⟧t H) ⟦ε⟧) | 
--   (sym (Weakening₂ ρ H (⟦ ρ ⟧t H) ⟦ε⟧)) = ⟦f⟧ ε-id-R e (⟦ recΣ f fmap ⟧ H φ η n)

-- Have:
--   w , y , ρ : R[ ★ → ★ ]
--   ev        : ρ · y ~ w
--   M         : μ (Σ ρ) → τ
--   r         : μ (Σ w) → τ
--   v         : Σ ρ (μ (Σ w)) 
-- Want:
--   τ
--
-- If it were possible to write
--   f : μ (Σ w) → μ (Σ ρ)
-- then
--   M  (In (fmap f v))
-- would work. (But this is not possible.)
-- I wonder if ana can come to the rescue?
-- ⟦ unrec {ρ = ρ} {τ = τ} M fmap ⟧ H φ η n w y π v r
--   rewrite sym (Weakening₂ τ H w y)
--   | sym (Weakening₂ ρ H w y) = {!!}
⟦ c ⟧ H φ η n = {!!}
-- ⟦ (f ▿μ g) π fmap gmap ⟧ H φ η n (In v) with ⟦ f ⟧ H φ η n | ⟦ g ⟧ H φ η n | ⟦ π ⟧n H φ
-- ... | ρ₁-elim | ρ₂-elim | ev@(l , r) = {!!}
