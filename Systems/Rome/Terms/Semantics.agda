{-# OPTIONS --allow-unsolved-metas #-}
open import Preludes.Level
open import Prelude

module Rome.Terms.Semantics where
 
open import Shared.Lib.Equality
open import Shared.Postulates.FunExt

open import Rome.Kinds
open import Rome.Types.Syntax
import Rome.Types.Semantics as TypeSem
open TypeSem hiding (⟦_⟧t ; ⟦_⟧p)
open import Rome.Types.Substitution
open import Rome.Types.Substitution.Properties -- extensionality
open import Rome.Terms.Syntax
open import Rome.Equivalence.Syntax 
import Rome.Equivalence.Semantics as EqSem
open EqSem hiding (⟦_⟧eq ; ⟦_⟧eq-π) -- extensionality
open import Rome.Entailment.Syntax 
import Rome.Entailment.Semantics as EntSem
open EntSem hiding (⟦_⟧pe ; ⟦_⟧n)

open import IndexCalculus
open import IndexCalculus.Properties
import IndexCalculus as Ix

--------------------------------------------------------------------------------
-- These shenanigans should be moved to the top level export module of each folder.

⟦_⟧t : ∀ {ℓ ℓκ} {Δ : KEnv ℓ} {κ : Kind ℓκ} → Type Δ κ → Potatoes → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦_⟧t τ n H = TypeSem.⟦_⟧t n τ H

⟦_⟧p : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} → Pred Δ κ → Potatoes → ⟦ Δ ⟧ke → Set (lsuc ℓκ)
⟦_⟧p π n H = TypeSem.⟦_⟧p n π H


⟦_⟧pe : ∀ {ℓ ℓΦ} {Δ : KEnv ℓ} → PEnv Δ ℓΦ → Potatoes → ⟦ Δ ⟧ke → Set (lsuc ℓΦ)
⟦ Φ ⟧pe g H = EntSem.⟦_⟧pe g Φ H

⟦_⟧n : ∀ {ℓΔ ℓκ ℓΦ} {κ : Kind ℓκ} {Δ : KEnv ℓΔ} {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
         Ent Δ Φ π → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe g H → ⟦ π ⟧p g H
⟦ π ⟧n g H η = EntSem.⟦_⟧n g π H η

⟦_⟧eq-π : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {π₁ π₂ : Pred Δ κ} →
         π₁ ≡p π₂ → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ π₁ ⟧p g H ≡ ⟦ π₂ ⟧p g H
⟦_⟧eq-π eq g H = EqSem.⟦_⟧eq-π g eq H
        
⟦_⟧eq : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} {τ υ : Type Δ κ} →
       τ ≡t υ → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ τ ⟧t g H ≡ ⟦ υ ⟧t g H
⟦_⟧eq eq g H = EqSem.⟦_⟧eq g eq H

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

⟦_⟧e : Env Δ ℓΓ → Potatoes → ⟦ Δ ⟧ke → Set ℓΓ
⟦ ε ⟧e g H = ⊤
⟦ Γ ، τ ⟧e g H = ⟦ Γ ⟧e g H × (Maybe (⟦ τ ⟧t g H))

--------------------------------------------------------------------------------
-- The meaning of variables.

⟦_⟧v : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
       Var Γ τ → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e g H → Maybe (⟦ τ ⟧t g H)
⟦ Z ⟧v n H (η , x) = x
⟦ S v ⟧v n H (η , x) = ⟦ v ⟧v n H η


--------------------------------------------------------------------------------
-- Denotational Weakening Lemma.

weaken⟦_⟧e : ∀ {ℓΔ ℓΓ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Γ : Env Δ ℓΓ) → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → (⟦Γ⟧ : ⟦ Γ ⟧e g H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΓ Γ ⟧e g (H , X)
weaken⟦ ε ⟧e g H ⟦Γ⟧ X = tt
weaken⟦_⟧e {Δ = Δ} {κ = κ}  (Γ ، τ) g H (⟦Γ⟧ , ⟦τ⟧) X
  rewrite τ-preservation g Δ (Δ ، κ) H (H , X) S (λ _ → refl) τ = weaken⟦ Γ ⟧e g H ⟦Γ⟧ X , ⟦τ⟧

weaken⟦_⟧pe : ∀ {ℓΔ ℓΦ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Φ : PEnv Δ ℓΦ) → (g : Potatoes) → (H : ⟦ Δ ⟧ke) → (⟦Φ⟧ : ⟦ Φ ⟧pe g H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΦ Φ ⟧pe g (H , X)
weaken⟦ ε ⟧pe g H ⟦Φ⟧ X = tt
weaken⟦_⟧pe {Δ = Δ} {κ} (Φ , π) g H (⟦Φ⟧ , ⟦π⟧) X
  rewrite π-preservation g Δ (Δ ، κ) H (H , X) S (λ _ → refl) π = weaken⟦ Φ ⟧pe g H ⟦Φ⟧ X , ⟦π⟧

--------------------------------------------------------------------------------
-- -- The meaning of terms.

-- open _↔_
-- open _≃_

⟦_⟧ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓ)} →
        Term Δ Φ Γ τ →
        (g : Potatoes) →  -- Type gas
        (h : Potatoes) →  -- Term Gas
        (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe g H → ⟦ Γ ⟧e g H → 
        Maybe (⟦ τ ⟧t g H)
⟦ var x ⟧ g h H φ η = ⟦ x ⟧v g H η
⟦ `λ _ M ⟧ g h H φ η = just (λ x → ⟦ M ⟧ g h H φ (η , x)) 
⟦ M · N ⟧ g h H φ η = do
  m ← (⟦ M ⟧ g h H φ η)
  m (⟦ N ⟧ g h H φ η) 
⟦ (`Λ κ M) ⟧ g h H φ η = just (λ s → ⟦ M ⟧ g h (H , s) (weaken⟦ _ ⟧pe g H φ s) (weaken⟦ _ ⟧e g H η s))
⟦ _·[_] {τ = τ} M υ ⟧ g h H φ η 
  rewrite (sym (Substitution g τ υ H)) = do
  m ← ⟦ M ⟧ g h H φ η
  m (⟦ υ ⟧t g H)
⟦ `ƛ _ M ⟧ g h H φ η = just (λ x → ⟦ M ⟧ g h H (φ , x) η)
⟦ M ·⟨ D ⟩ ⟧ g h H φ η = do
  m ← (⟦ M ⟧ g h H φ η)
  m (⟦ D ⟧n g H φ)
⟦ (r₁ ⊹ r₂) π ⟧ g h H φ η = do
  r₁ ← (⟦ r₁ ⟧ g h H φ η) 
  r₂ ← (⟦ r₂ ⟧ g h H φ η) 
  just (r₁ Ix.⊹ r₂ Using (⟦ π ⟧n g H φ))
⟦ lab s ⟧ g h H φ η  = just tt
⟦ prj r π ⟧ g h H φ η  = (⟦ r ⟧ g h H φ η) >>= 
  (λ r' → 
    just (λ i → let n  = (fst (⟦ π ⟧n g H φ i)) in
                 let eq = (snd (⟦ π ⟧n g H φ i)) in ≡-elim (sym (cong Maybe eq)) (r' n))) 
⟦ M ▹ N ⟧ g h H φ η = ⟦ N ⟧ g h H φ η
⟦ M / N ⟧ g h H φ η = ⟦ M ⟧ g h H φ η
⟦ t-≡ {τ = τ}{υ = υ} τ≡υ M ⟧ g h H φ η 
  rewrite sym (⟦ τ≡υ ⟧eq g H) = ⟦ M ⟧ g h H φ η
⟦ inj M π ⟧ g h H φ η = do 
  m ← (⟦ M ⟧ g h H φ η)
  return (Ix.inj (⟦ π ⟧n g H φ) m)
⟦ (M ▿ N) π ⟧ g h H φ η = do
    let ev = ⟦ π ⟧n g H φ
    ρ₁-elim ← ⟦ M ⟧ g h H φ η 
    ρ₂-elim ← ⟦ N ⟧ g h H φ η
    just (λ { 
      (just (i , P)) → 
        [ (λ (j , eq) → ρ₁-elim (just (j , (≡-elim (sym eq) P)))) , 
          (λ (j , eq) → ρ₂-elim (just (j , (≡-elim (sym eq) P)))) ]′ (fst ev i) ; 
      nothing → nothing })      
⟦ syn {Δ = Δ} {κ = κ} ρ f M ⟧ g h H₀ φ η = just (λ i → do
  let ⟦ρ⟧ = ⟦ ρ ⟧t g H₀
  let ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ g {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
  let ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ g {ℓκA = lzero} f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
  ⟦M⟧ ← ⟦ M ⟧ g h H₀ φ η
  ⟦M⟧ ← ⟦M⟧ tt
  ⟦M⟧ ← ⟦M⟧ (snd ⟦ρ⟧ i)
  ⟦M⟧ ← ⟦M⟧ (⟦ρ⟧ delete i)
  ⟦M⟧ ← ⟦M⟧ (evidence i)
  ⟦M⟧ ← ⟦M⟧ (just tt)
  just (≡-elim (sym (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd ⟦ρ⟧ i))) ⟦M⟧)
  )
  where
    ⟦ρ⟧ = ⟦ ρ ⟧t g H₀
    evidence : ∀ i → sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
               ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t g (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
    evidence i rewrite sym (Weakening₃ g {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)) =  recombine ⟦ρ⟧ i

⟦ ana {Δ = Δ} {κ = κ} ρ f τ M ⟧ g h H₀ φ η = just 
  (λ { (just (i , P)) → do
    let ⟦ρ⟧ = (⟦ ρ ⟧t g H₀)
    let ⟦τ⟧≡⟦weaken³τ⟧ = Weakening₃ g {ℓκA = lzero} τ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
    let ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ g {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
    let ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ g {ℓκA = lzero} f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
    ⟦M⟧ ← ⟦ M ⟧ g h H₀ φ η
    ⟦M⟧ ← ⟦M⟧ tt
    ⟦M⟧ ← ⟦M⟧ (snd ⟦ρ⟧ i)
    ⟦M⟧ ← ⟦M⟧ (⟦ρ⟧ delete i)
    ⟦M⟧ ← ⟦M⟧ (evidence i)
    ⟦M⟧ ← ⟦M⟧ (just tt)
    ⟦M⟧ ← ⟦M⟧ (just (≡-elim (cong-app ⟦f⟧≡⟦weaken³f⟧ (snd (⟦ ρ ⟧t g H₀) i)) P))
    just (≡-elim (sym ⟦τ⟧≡⟦weaken³τ⟧) ⟦M⟧)
  ; nothing → nothing})
    where
      ⟦ρ⟧ = ⟦ ρ ⟧t g H₀
      evidence : ∀ i → sing (snd ⟦ρ⟧ i) Ix.· ⟦ρ⟧ delete i ~
                 ⟦ weaken (weaken (weaken {ℓκ = lzero} ρ)) ⟧t g (((H₀ , tt) , (snd ⟦ρ⟧ i)) , (⟦ρ⟧ delete i))
      evidence i rewrite sym (Weakening₃ g {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)) =  recombine ⟦ρ⟧ i
⟦ Term.Π s ⟧ g h H φ η = just (λ { fzero → ⟦ s ⟧ g h H φ η })
⟦ Π⁻¹ r ⟧ g h H φ η = do
  ⟦r⟧ ←  ⟦ r ⟧ g h H φ η
  ⟦r⟧ fzero
⟦ Term.Σ s ⟧ g h H φ η = do
  ⟦s⟧ ← (⟦ s ⟧ g h H φ η)
  just (fzero , ⟦s⟧)
⟦ Σ⁻¹ v ⟧ g h H φ η with ⟦ v ⟧ g h H φ η
... | just (fzero , M) = just M
... | nothing = nothing
⟦ fold {ℓ₁ = ℓ₁} {ρ = ρ} {υ = υ} M₁ M₂ M₃ N ⟧ g h H φ η = do
     op ← ⟦ M₁ ⟧ g h H φ η 
     _+_ ← ⟦ M₂ ⟧ g h H φ η 
     e ← ⟦ M₃ ⟧ g h H φ η
     r ← ⟦ N ⟧ g h H φ η
     Ix.fold (⟦ ρ ⟧t g H) 
       (λ τ y ev t → 
         op tt       >>= λ f → 
         f τ         >>= λ f → 
         f y         >>= λ f → 
         f (≡-elim 
             (cong 
               (Ix._·_~_ (sing τ) y) 
               (Weakening₃ g ρ H tt τ y)) 
               ev)   >>= λ f → 
         f (just tt) >>= λ f → 
         f t         >>= λ d →
         just (≡-elim (sym (Weakening₃ g υ H tt τ y)) d) ) 
       (λ x y → do 
         cur ← _+_ x
         cur y) 
       (just e) r

-- Recursive Terms.
------------------
⟦ In M fmap ⟧ g h H φ η = do
  m    ← ⟦ M ⟧ g h H φ η 
  fmap ← ⟦ fmap ⟧ g h H φ η 
  In-Maybe (Ix.ungarbage fmap) g (just m)
⟦ Term.Out {F = F} M fmap ⟧ g h H φ η = do
  m    ← ⟦ M ⟧ g h H φ η 
  fmap ← ⟦ fmap ⟧ g h H φ η 
  Out-Maybe g (Ix.ungarbage fmap) (λ _ → nothing) (just m)
⟦ tie f ⟧ g h H φ η = nothing
-- ⟦ tie {ℓ = ℓ} {ρ = ρ} {τ = τ} f ⟧ g h H φ η = do
--   let ⟦ε⟧ = ⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t g H 
--   ⟦f⟧ ← ⟦ f ⟧ (ℕ.suc g) H φ η 
--   ⟦f⟧ ← ⟦f⟧ (⟦ ρ ⟧t (ℕ.suc g) H) 
--   ⟦f⟧ ← ⟦f⟧ (⟦ ε {κ = (★ ℓ `→ ★ ℓ)} ⟧t g H)
--   ⟦f⟧ ← ⟦f⟧ ε-id-R
--   {!!}
  -- just 
  --   (λ { (just e) → do
  --        ⟦f⟧ ← ⟦f⟧ (just (IndexCalculus.Out {F = {!⟦ (Type.Σ ρ) ⟧t g H !}} g e))
  --        ⟦f⟧ (⟦ tie f ⟧ (ℕ.suc g) H φ η)
  --        ; nothing → nothing })
⟦ recΣ {ℓ = ℓ} {ρ = ρ} {τ} f ⟧ g h H φ η = ⟦ f ⟧ g h H φ η
-- This rule is admissable.
⟦ _▿μ_ {τ = τ} M N π ⟧ g h H φ η = 
  just λ w → 
  just (λ y → 
  just (λ ev → 
  just (λ v → 
  just (λ r → do
    f ← ⟦ M ⟧ g h H φ η
    f ← f w  -- Yes.
    f ← f y  -- Should be (ρ₂ · y)
    f ← f {!!}
    g ← ⟦ M ⟧ g h H φ η
    g ← g w
    g ← g y  -- Should be (ρ₁ · y)
    g ← g {!!}
    -- want to write (f Ix.▿ g) v r
    -- but:
    --  1. I suspect issues with evidence. We have in context
    --       - _ : ρ₁ · ρ₂ ~ ρ₃
    --       - _ : ρ₃ · y  ~ w
    --       - v : Maybe (Σ ρ₃ (μ (Σ w)))
    --       - r : Maybe (Maybe (μ (Σ w))) → Maybe τ
    --     Which means
    --       - f w (ρ₂ · y) : ρ₁ · (ρ₂ · y) ~ w ⇒ Maybe (Σ ρ₁ (μ (Σ w))) → (Maybe (Maybe (μ (Σ w))) → Maybe τ) → Maybe τ
    --       - g w (ρ₁ · y) : ρ₂ · (ρ₁ · y) ~ w ⇒ Maybe (Σ ρ₂ (μ (Σ w))) → (Maybe (Maybe (μ (Σ w))) → Maybe τ) → Maybe τ
    --       - (f w _ ▿ g w _) : (ρ₁ ⌈ (μ (Σ w)) ⌉) · (ρ₂ ⌈ (μ (Σ w)) ⌉) ~ (ρ₃ ⌈ (μ (Σ w)) ⌉) ⇒ 
    --                            Σ ρ₃ (μ (Σ w)) → (Maybe (Maybe (μ (Σ w))) → Maybe τ) → Maybe τ
    --     Need to derive
    --       - ρ₁ · (ρ₂ · y) ~ w
    --       - ρ₂ · (ρ₁ · y) ~ w
    --  2. Maybes make writing Ix.▿ a nightmare
    {!Ix._▿_!} 
  ))))

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
