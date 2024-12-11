open import Rome.Preludes.Level
open import Rome.Prelude

module Rome.Denotational.Terms.Semantics (tytatos : Potatoes) where
 
open import Rome.Shared.Lib.Equality
open import Rome.Shared.Postulates.FunExt

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types.Syntax
open import Rome.Denotational.Types.Semantics tytatos
open import Rome.Denotational.Types.Substitution
open import Rome.Denotational.Types.Substitution.Properties tytatos -- extensionality
open import Rome.Denotational.Terms.Syntax
open import Rome.Denotational.Equivalence.Syntax 
open import Rome.Denotational.Equivalence.Semantics tytatos 
open import Rome.Denotational.Entailment.Syntax 
open import Rome.Denotational.Entailment.Semantics tytatos

open import Rome.IndexCalculus
open import Rome.IndexCalculus.Properties
import Rome.IndexCalculus as Ix

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

⟦_⟧ : ∀ {Φ : PEnv Δ ℓΦ} {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓ)} →
        Term Δ Φ Γ τ →
        (g : Potatoes) → 
        (H : ⟦ Δ ⟧ke) → ⟦ Φ ⟧pe H → ⟦ Γ ⟧e H → 
        Maybe (⟦ τ ⟧t H)
⟦ var x ⟧ g H φ η = ⟦ x ⟧v H η
⟦ `λ _ M ⟧ g H φ η = just (λ x → ⟦ M ⟧ g H φ (η , x)) 
⟦ M · N ⟧ g H φ η = do
  m ← (⟦ M ⟧ g H φ η)
  m (⟦ N ⟧ g H φ η) 
⟦ (`Λ κ M) ⟧ g H φ η = just (λ s → ⟦ M ⟧ g (H , s) (weaken⟦ _ ⟧pe H φ s) (weaken⟦ _ ⟧e H η s))
⟦ _·[_] {τ = τ} M υ ⟧ g H φ η 
  rewrite (sym (Substitution τ υ H)) = do
  m ← ⟦ M ⟧ g H φ η
  m (⟦ υ ⟧t H)
⟦ `ƛ _ M ⟧ g H φ η = just (λ x → ⟦ M ⟧ g H (φ , x) η)
⟦ M ·⟨ D ⟩ ⟧ g H φ η = do
  m ← (⟦ M ⟧ g H φ η)
  m (⟦ D ⟧n H φ)
⟦ rowCompl {ρ₁ = ρ₁} {ρ₂ = ρ₂} {τ = τ} ev M ⟧ g H φ η = do
  m ← ⟦ M ⟧ g H φ η
  m ← m y
  m ← m P'
  just (≡-elim (sym (Weakening τ H y)) m)
  where
    C = Ix.complement (⟦ ev ⟧n H φ)
    y = fst C
    P = snd C
    P' : ⟦ K ρ₁ ⟧t (H , y) Rome.IndexCalculus.· fst C ~ ⟦ K ρ₂ ⟧t (H , y)
    P' rewrite sym (Weakening ρ₁ H y) | sym (Weakening ρ₂ H y)  = P 
    
⟦ (r₁ ⊹ r₂) π ⟧ g H φ η = do
  r₁ ← (⟦ r₁ ⟧ g H φ η) 
  r₂ ← (⟦ r₂ ⟧ g H φ η) 
  just (r₁ Ix.⊹ r₂ Using (⟦ π ⟧n H φ))
⟦ lab s ⟧ g H φ η  = just tt
⟦ prj r π ⟧ g H φ η  = (⟦ r ⟧ g H φ η) >>= 
  (λ r' → 
    just (λ i → let n  = (fst (⟦ π ⟧n H φ i)) in
                 let eq = (snd (⟦ π ⟧n H φ i)) in ≡-elim (sym (cong Maybe eq)) (r' n))) 
⟦ M ▹ N ⟧ g H φ η = ⟦ N ⟧ g H φ η
⟦ M / N ⟧ g H φ η = ⟦ M ⟧ g H φ η
⟦ t-≡ {τ = τ}{υ = υ} τ≡υ M ⟧ g H φ η 
  rewrite sym (⟦ τ≡υ ⟧eq H) = ⟦ M ⟧ g H φ η
⟦ inj M π ⟧ g H φ η = do 
  m ← (⟦ M ⟧ g H φ η)
  return (Ix.inj (⟦ π ⟧n H φ) m)
⟦ (M ▿ N) π ⟧ g H φ η = do
    let ev = ⟦ π ⟧n H φ
    ρ₁-elim ← ⟦ M ⟧ g H φ η 
    ρ₂-elim ← ⟦ N ⟧ g H φ η
    just (λ { 
      (just (i , P)) → 
        [ (λ (j , eq) → ρ₁-elim (just (j , (≡-elim (sym eq) P)))) , 
          (λ (j , eq) → ρ₂-elim (just (j , (≡-elim (sym eq) P)))) ]′ (fst ev i) ; 
      nothing → nothing })      
⟦ syn {Δ = Δ} {κ = κ} ρ f M ⟧ g H₀ φ η = just (λ i → do
  let ⟦ρ⟧ = ⟦ ρ ⟧t H₀
  let ⟦ρ⟧≡⟦weaken³ρ⟧ = Weakening₃ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
  let ⟦f⟧≡⟦weaken³f⟧ = Weakening₃ {ℓκA = lzero} f H₀ tt (snd ⟦ρ⟧ i) (⟦ρ⟧ delete i)
  ⟦M⟧ ← ⟦ M ⟧ g H₀ φ η
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

⟦ ana {Δ = Δ} {κ = κ} ρ f τ M ⟧ g H₀ φ η = just 
  (λ { (just (i , P)) → do
    let ⟦ρ⟧ = (⟦ ρ ⟧t H₀)
    let ⟦τ⟧≡⟦weaken₂τ⟧ = Weakening₂ {ℓκA = lzero} τ H₀ tt (snd ⟦ρ⟧ i)
    let ⟦ρ⟧≡⟦weaken₂ρ⟧ = Weakening₂ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i)
    let ⟦f⟧≡⟦weaken₂f⟧ = Weakening₂ {ℓκA = lzero} f H₀ tt (snd ⟦ρ⟧ i)
    ⟦M⟧ ← ⟦ M ⟧ g H₀ φ η
    ⟦M⟧ ← ⟦M⟧ tt
    ⟦M⟧ ← ⟦M⟧ (snd ⟦ρ⟧ i)
    ⟦M⟧ ← ⟦M⟧ (evidence i)
    ⟦M⟧ ← ⟦M⟧ (just tt)
    ⟦M⟧ ← ⟦M⟧ (just (≡-elim (cong-app ⟦f⟧≡⟦weaken₂f⟧ (snd (⟦ ρ ⟧t H₀) i)) P))
    just (≡-elim (sym ⟦τ⟧≡⟦weaken₂τ⟧) ⟦M⟧)
  ; nothing → nothing})
    where
      ⟦ρ⟧ = ⟦ ρ ⟧t H₀
      evidence : ∀ i → sing (snd ⟦ρ⟧ i) Ix.≲ ⟦ (weaken (weaken {ℓκ = lzero} ρ)) ⟧t (((H₀ , tt) , (snd ⟦ρ⟧ i)))
      evidence i rewrite sym (Weakening₂ {ℓκA = lzero} ρ H₀ tt (snd ⟦ρ⟧ i)) = λ { fzero → i , refl }
⟦ Term.Π s ⟧ g H φ η = just (λ { fzero → ⟦ s ⟧ g H φ η })
⟦ Π⁻¹ r ⟧ g H φ η = do
  ⟦r⟧ ←  ⟦ r ⟧ g H φ η
  ⟦r⟧ fzero
⟦ Term.Σ s ⟧ g H φ η = do
  ⟦s⟧ ← (⟦ s ⟧ g H φ η)
  just (fzero , ⟦s⟧)
⟦ Σ⁻¹ v ⟧ g H φ η with ⟦ v ⟧ g H φ η
... | just (fzero , M) = just M
... | nothing = nothing
⟦ fold {ℓ₁ = ℓ₁} {ρ = ρ} {υ = υ} M₁ M₂ M₃ N ⟧ g H φ η = do
     op ← ⟦ M₁ ⟧ g H φ η 
     _+_ ← ⟦ M₂ ⟧ g H φ η 
     e ← ⟦ M₃ ⟧ g H φ η
     r ← ⟦ N ⟧ g H φ η
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

-- Recursive Terms (novel to Rωμ).
------------------
⟦ In M fmap ⟧ g H φ η = do
  m    ← ⟦ M ⟧ g H φ η 
  fmap ← ⟦ fmap ⟧ g H φ η 
  Ix.In tytatos (Ix.ungarbage fmap) (just m)
⟦ Out {F = F} M fmap ⟧ g H φ η = do
  m    ← ⟦ M ⟧ g H φ η 
  fmap ← ⟦ fmap ⟧ g H φ η 
  Ix.Out tytatos (Ix.ungarbage fmap) (just m)
⟦ fix ⟧ zero H φ η = nothing
⟦ fix {τ = τ} ⟧ (ℕ.suc g) H φ η = do
  Fix ← (⟦ fix {τ = τ} ⟧ g H φ η)
  just (λ f → join→ f (Fix f))

