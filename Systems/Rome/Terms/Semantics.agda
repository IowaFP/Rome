{-# OPTIONS --allow-unsolved-metas #-}
open import Preludes.Level
open import Prelude

module Rome.Terms.Semantics (g : Potatoes) where
 
open import Shared.Lib.Equality
open import Shared.Postulates.FunExt

open import Rome.Kinds
open import Rome.Types.Syntax
open import Rome.Types.Semantics g
open import Rome.Types.Substitution
open import Rome.Types.Substitution.Properties g -- extensionality
open import Rome.Terms.Syntax
open import Rome.Equivalence.Syntax 
open import Rome.Equivalence.Semantics g 
open import Rome.Entailment.Syntax 
open import Rome.Entailment.Semantics g

open import IndexCalculus
open import IndexCalculus.Properties
import IndexCalculus as Ix

--------------------------------------------------------------------------------
-- These shenanigans should be moved to the top level export module of each folder.

-- ⟦_⟧t : ∀ {ℓ ℓκ} {Δ : KEnv ℓ} {κ : Kind ℓκ} → Type Δ κ → Potatoes → ⟦ Δ ⟧ke → ⟦ κ ⟧k
-- ⟦_⟧t τ n H = TypeSem.⟦_⟧t n τ H

-- ⟦_⟧p : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} → Pred Δ κ → Potatoes → ⟦ Δ ⟧ke → Set (lsuc ℓκ)
-- ⟦_⟧p π n H = TypeSem.⟦_⟧p n π H


-- ⟦_⟧pe : ∀ {ℓ ℓΦ} {Δ : KEnv ℓ} → PEnv Δ ℓΦ → Potatoes → ⟦ Δ ⟧ke → Set (lsuc ℓΦ)
-- ⟦ Φ ⟧pe g H = EntSem.⟦_⟧pe g Φ H

-- ⟦_⟧n : ∀ {ℓΔ ℓκ ℓΦ} {κ : Kind ℓκ} {Δ : KEnv ℓΔ} {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
--          Ent Δ Φ π → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe g H → ⟦ π ⟧p g H
-- ⟦ π ⟧n g H η = EntSem.⟦_⟧n g π H η

-- ⟦_⟧eq-π : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {π₁ π₂ : Pred Δ κ} →
--          π₁ ≡p π₂ → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ π₁ ⟧p g H ≡ ⟦ π₂ ⟧p g H
-- ⟦_⟧eq-π eq g H = EqSem.⟦_⟧eq-π g eq H
        
-- ⟦_⟧eq : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {τ υ : Type Δ κ} →
--        τ ≡t υ → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ τ ⟧t g H ≡ ⟦ υ ⟧t g H
-- ⟦_⟧eq eq g H = EqSem.⟦_⟧eq g eq H

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
⟦ Γ ، τ ⟧e H = ⟦ Γ ⟧e H × (Maybe (⟦ τ ⟧t H))

--------------------------------------------------------------------------------
-- The meaning of variables.

⟦_⟧v : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
       Var Γ τ → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → Maybe (⟦ τ ⟧t H)
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

⟦_⟧ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓ)} →
        Term Δ Φ Γ τ →
        (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ Γ ⟧e H → 
        Maybe (⟦ τ ⟧t H)
⟦ var x ⟧ H φ η = ⟦ x ⟧v H η
⟦ `λ _ M ⟧ H φ η = just (λ x → ⟦ M ⟧ H φ (η , x)) 
⟦ M · N ⟧ H φ η = do
  m ← (⟦ M ⟧ H φ η)
  m (⟦ N ⟧ H φ η) 
⟦ (`Λ κ M) ⟧ H φ η = just (λ s → ⟦ M ⟧ (H , s) (weaken⟦ _ ⟧pe H φ s) (weaken⟦ _ ⟧e H η s))
⟦ _·[_] {τ = τ} M υ ⟧ H φ η 
  rewrite (sym (Substitution τ υ H)) = do
  m ← ⟦ M ⟧ H φ η
  m (⟦ υ ⟧t H)
⟦ `ƛ _ M ⟧ H φ η = just (λ x → ⟦ M ⟧ H (φ , x) η)
⟦ M ·⟨ D ⟩ ⟧ H φ η = do
  m ← (⟦ M ⟧ H φ η)
  m (⟦ D ⟧n H φ)
⟦ (r₁ ⊹ r₂) π ⟧ H φ η = do
  r₁ ← (⟦ r₁ ⟧ H φ η) 
  r₂ ← (⟦ r₂ ⟧ H φ η) 
  just (r₁ Ix.⊹ r₂ Using (⟦ π ⟧n H φ))
⟦ lab s ⟧ H φ η  = just tt
⟦ prj r π ⟧ H φ η  = (⟦ r ⟧ H φ η) >>= 
  (λ r' → 
    just (λ i → let n  = (fst (⟦ π ⟧n H φ i)) in
                 let eq = (snd (⟦ π ⟧n H φ i)) in ≡-elim (sym (cong Maybe eq)) (r' n))) 
⟦ M ▹ N ⟧ H φ η = ⟦ N ⟧ H φ η
⟦ M / N ⟧ H φ η = ⟦ M ⟧ H φ η
⟦ t-≡ {τ = τ}{υ = υ} τ≡υ M ⟧ H φ η 
  rewrite sym (⟦ τ≡υ ⟧eq H) = ⟦ M ⟧ H φ η
⟦ inj M π ⟧ H φ η = do 
  m ← (⟦ M ⟧ H φ η)
  return (Ix.inj (⟦ π ⟧n H φ) m)
⟦ (M ▿ N) π ⟧ H φ η = do
    let ev = ⟦ π ⟧n H φ
    ρ₁-elim ← ⟦ M ⟧ H φ η 
    ρ₂-elim ← ⟦ N ⟧ H φ η
    just (λ { 
      (just (i , P)) → 
        [ (λ (j , eq) → ρ₁-elim (just (j , (≡-elim (sym eq) P)))) , 
          (λ (j , eq) → ρ₂-elim (just (j , (≡-elim (sym eq) P)))) ]′ (fst ev i) ; 
      nothing → nothing })      
⟦ syn {Δ = Δ} {κ = κ} ρ f M ⟧ H₀ φ η = just (λ i → do
  let ⟦ρ⟧ = ⟦ ρ ⟧t H₀
  let ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
  let ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ {ℓκA = lzero} f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
  ⟦M⟧ ← ⟦ M ⟧ H₀ φ η
  ⟦M⟧ ← ⟦M⟧ tt
  ⟦M⟧ ← ⟦M⟧ (snd ⟦ρ⟧ i)
  ⟦M⟧ ← ⟦M⟧ (⟦ρ⟧ delete i)
  ⟦M⟧ ← ⟦M⟧ (evidence i)
  ⟦M⟧ ← ⟦M⟧ (just tt)
  just (≡-elim (sym (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd ⟦ρ⟧ i))) ⟦M⟧)
  )
  where
    ⟦ρ⟧ = ⟦ ρ ⟧t H₀
    evidence : ∀ i → sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
               ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
    evidence i rewrite sym (Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)) =  recombine ⟦ρ⟧ i

⟦ ana {Δ = Δ} {κ = κ} ρ f τ M ⟧ H₀ φ η = just 
  (λ { (just (i , P)) → do
    let ⟦ρ⟧ = (⟦ ρ ⟧t H₀)
    let ⟦τ⟧≡⟦weaken³τ⟧ = Weakening₃ {ℓκA = lzero} τ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
    let ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
    let ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ {ℓκA = lzero} f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
    ⟦M⟧ ← ⟦ M ⟧ H₀ φ η
    ⟦M⟧ ← ⟦M⟧ tt
    ⟦M⟧ ← ⟦M⟧ (snd ⟦ρ⟧ i)
    ⟦M⟧ ← ⟦M⟧ (⟦ρ⟧ delete i)
    ⟦M⟧ ← ⟦M⟧ (evidence i)
    ⟦M⟧ ← ⟦M⟧ (just tt)
    ⟦M⟧ ← ⟦M⟧ (just (≡-elim (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd (⟦ ρ ⟧t H₀) i)) P))
    just (≡-elim (sym ⟦τ⟧≡⟦weaken³τ⟧) ⟦M⟧)
  ; nothing → nothing})
    where
      ⟦ρ⟧ = ⟦ ρ ⟧t H₀
      evidence : ∀ i → sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
                 ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
      evidence i rewrite sym (Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)) =  recombine ⟦ρ⟧ i
⟦ Term.Π s ⟧ H φ η = just (λ { fzero → ⟦ s ⟧ H φ η })
⟦ Π⁻¹ r ⟧ H φ η = do
  ⟦r⟧ ←  ⟦ r ⟧ H φ η
  ⟦r⟧ fzero
⟦ Term.Σ s ⟧ H φ η = do
  ⟦s⟧ ← (⟦ s ⟧ H φ η)
  just (fzero , ⟦s⟧)
⟦ Σ⁻¹ v ⟧ H φ η with ⟦ v ⟧ H φ η
... | just (fzero , M) = just M
... | nothing = nothing
⟦ fold {ℓ₁ = ℓ₁} {ρ = ρ} {υ = υ} M₁ M₂ M₃ N ⟧ H φ η = do
     op ← ⟦ M₁ ⟧ H φ η 
     _+_ ← ⟦ M₂ ⟧ H φ η 
     e ← ⟦ M₃ ⟧ H φ η
     r ← ⟦ N ⟧ H φ η
     Ix.fold (⟦ ρ ⟧t H) 
       (λ τ y ev t → 
         op tt       >>= λ f → 
         f τ         >>= λ f → 
         f y         >>= λ f → 
         f (≡-elim 
             (cong 
               (Ix._·_~_ (sing τ) y) 
               (Weakening₃ ρ H tt τ y)) 
               ev)   >>= λ f → 
         f (just tt) >>= λ f → 
         f t         >>= λ d →
         just (≡-elim (sym (Weakening₃ υ H tt τ y)) d) ) 
       (λ x y → do 
         cur ← _+_ x
         cur y) 
       (just e) r

-- Recursive Terms.
------------------
⟦ In M fmap ⟧ H φ η = do
  m    ← ⟦ M ⟧ H φ η 
  fmap ← ⟦ fmap ⟧ H φ η 
  In-Maybe (Ix.ungarbage fmap) g (just m)
⟦ Term.Out {F = F} M fmap ⟧ H φ η = do
  m    ← ⟦ M ⟧ H φ η 
  fmap ← ⟦ fmap ⟧ H φ η 
  Out-Maybe g (Ix.ungarbage fmap) (λ _ → nothing) (just m)
⟦ tie f ⟧ H φ η = nothing
-- ⟦ tie {ℓ = ℓ} {ρ = ρ} {τ = τ} f ⟧ H φ η = do
--   let ⟦ε⟧ = ⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H 
--   ⟦f⟧ ← ⟦ f ⟧ (ℕ.suc g) H φ η 
--   ⟦f⟧ ← ⟦f⟧ (⟦ ρ ⟧t (ℕ.suc g) H) 
--   ⟦f⟧ ← ⟦f⟧ (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H)
--   ⟦f⟧ ← ⟦f⟧ ε-id-R
--   {!!}
  -- just 
  --   (λ { (just e) → do
  --        ⟦f⟧ ← ⟦f⟧ (just (IndexCalculus.Out {F = {!⟦ (Type.Σ ρ) ⟧t H !}} e))
  --        ⟦f⟧ (⟦ tie f ⟧ (ℕ.suc g) H φ η)
  --        ; nothing → nothing })
⟦ recΣ {ℓ = ℓ} {ρ = ρ} {τ} f ⟧ H φ η = ⟦ f ⟧ H φ η
-- This rule is admissable.
⟦ _▿μ_ {τ = τ} M N π ⟧ H φ η = {!!} 
  -- just λ w → 
  -- just (λ y → 
  -- just (λ ev → 
  -- just (λ v → 
  -- just (λ r → do
  --   f ← ⟦ M ⟧ H φ η
  --   f ← f w  -- Yes.
  --   f ← f y  -- Should be (ρ₂ · y)
  --   f ← f {!!}
  --   g ← ⟦ M ⟧ H φ η
  --   g ← w
  --   g ← y  -- Should be (ρ₁ · y)
  --   g ← {!!}
  --   -- want to write (f Ix.▿ g) v r
  --   -- but:
  --   --  1. I suspect issues with evidence. We have in context
  --   --       - _ : ρ₁ · ρ₂ ~ ρ₃
  --   --       - _ : ρ₃ · y  ~ w
  --   --       - v : Maybe (Σ ρ₃ (μ (Σ w)))
  --   --       - r : Maybe (Maybe (μ (Σ w))) → Maybe τ
  --   --     Which means
  --   --       - f w (ρ₂ · y) : ρ₁ · (ρ₂ · y) ~ w ⇒ Maybe (Σ ρ₁ (μ (Σ w))) → (Maybe (Maybe (μ (Σ w))) → Maybe τ) → Maybe τ
  --   --       - w (ρ₁ · y) : ρ₂ · (ρ₁ · y) ~ w ⇒ Maybe (Σ ρ₂ (μ (Σ w))) → (Maybe (Maybe (μ (Σ w))) → Maybe τ) → Maybe τ
  --   --       - (f w _ ▿ w _) : (ρ₁ ⌈ (μ (Σ w)) ⌉) · (ρ₂ ⌈ (μ (Σ w)) ⌉) ~ (ρ₃ ⌈ (μ (Σ w)) ⌉) ⇒ 
  --   --                            Σ ρ₃ (μ (Σ w)) → (Maybe (Maybe (μ (Σ w))) → Maybe τ) → Maybe τ
  --   --     Need to derive
  --   --       - ρ₁ · (ρ₂ · y) ~ w
  --   --       - ρ₂ · (ρ₁ · y) ~ w
  --   --  2. Maybes make writing Ix.▿ a nightmare
  --   {!Ix._▿_!} 
  -- ))))

-- foo : Term ε ε ε (Mu (`λ (★ ℓ) (tvar Z)))
-- foo = In 

--------------------------------------------------------------------------------
-- May need again:

--   where
--     eff : (⟦ K² ρ ⟧t ((H , ⟦ ρ ⟧t H) , (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H)) IndexCalculus.·
--       (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H) ~ ⟦ ρ ⟧t H →
--       Maybe
--       (Maybe
--        (IndexCalculus.Σ
--         (fst (⟦ K² ρ ⟧t ((H , ⟦ ρ ⟧t H) , (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H))) ,
--          (λ i →
--             snd (⟦ K² ρ ⟧t ((H , ⟦ ρ ⟧t H) , (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H))) i
--             (Mu
--              (λ X →
--                 IndexCalculus.Σ
--                 (fst (⟦ ρ ⟧t H) , (λ i₁ → snd (⟦ ρ ⟧t H) i₁ X))))))) →
--        Maybe
--        (Maybe
--         (Maybe
--          (Mu
--           (λ X →
--              IndexCalculus.Σ (fst (⟦ ρ ⟧t H) , (λ i → snd (⟦ ρ ⟧t H) i X)))) →
--          Maybe (⟦ K² τ ⟧t ((H , ⟦ ρ ⟧t H) , (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H)))) →
--         Maybe (⟦ K² τ ⟧t ((H , ⟦ ρ ⟧t H) , (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H)))))) →
-- --      Output:
--         ⟦ ρ ⟧t H IndexCalculus.·
--       emptyRow ~ ⟦ ρ ⟧t H →
--       Maybe
--       (Maybe
--        (IndexCalculus.Σ
--         (fst (⟦ ρ ⟧t H) ,
--          (λ i →
--             snd (⟦ ρ ⟧t H) i
--             (Mu
--              (λ X →
--                 IndexCalculus.Σ
--                 (fst (⟦ ρ ⟧t H) , (λ i₁ → snd (⟦ ρ ⟧t H) i₁ X))))))) →
--        Maybe
--        (Maybe
--         (Maybe
--          (Mu
--           (λ X →
--              IndexCalculus.Σ (fst (⟦ ρ ⟧t H) , (λ i → snd (⟦ ρ ⟧t H) i X)))) →
--          Maybe (⟦ τ ⟧t H)) →
--         Maybe (⟦ τ ⟧t H)))

--     eff f rewrite (sym (Weakening₂ ρ H (⟦ ρ ⟧t H) (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H)))
--           |       (sym (Weakening₂ τ H (⟦ ρ ⟧t H) (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t H))) = f
