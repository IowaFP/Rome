module Rome.Operational.Types.Properties.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence
open import Rome.Operational.Types.Properties.Renaming


-------------------------------------------------------------------------------
-- Functor laws for lifting

lifts-cong : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (x : KVar (Δ₁ ,, κ₁) κ₂) → lifts σ₁ x ≡ lifts σ₂ x
lifts-cong e Z = refl
lifts-cong e (S x) = cong (ren S) (e x)              

lifts-id    : ∀ (x : KVar (Δ ,, κ₁) κ₂) → lifts ` x ≡ ` x 
lifts-id Z = refl
lifts-id (S x) = refl

-- Fusion for lifts and lift
lifts-lift      : ∀ {ρ : Renaming Δ₁ Δ₂}{σ : Substitution Δ₂ Δ₃} 
                    (x : KVar (Δ₁ ,, κ₁) κ₂) → 
                    lifts (σ ∘ ρ) x ≡ lifts σ (lift ρ x)
lifts-lift Z = refl
lifts-lift (S x) = refl

ren-lift-lifts : ∀ {σ : Substitution Δ₁ Δ₂}{ρ : Renaming Δ₂ Δ₃}(x : KVar (Δ₁ ,, κ₁) κ₂) → 
                    lifts (ren ρ ∘ σ) x ≡ ren (lift ρ) (lifts σ x)
ren-lift-lifts Z = refl
ren-lift-lifts {σ = σ} {ρ} (S x) = trans (sym (ren-comp ρ S (σ x))) (ren-comp S (lift ρ) (σ x))                    

-------------------------------------------------------------------------------
-- Functor laws for substitution

sub-cong : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : Type Δ₁ κ) → sub σ₁ τ ≡ sub σ₂ τ
sub-cong e Unit = refl
sub-cong e ε = refl
sub-cong e (` α) = e α
sub-cong e (`λ τ) = cong `λ (sub-cong (lifts-cong e) τ)
sub-cong e (τ₁ · τ₂) = cong₂ _·_ (sub-cong e τ₁) (sub-cong e τ₂)
sub-cong e (τ₁ `→ τ₂) = cong₂ _`→_ (sub-cong e τ₁) (sub-cong e τ₂)
sub-cong e (`∀ κ τ) = cong (`∀ κ) (sub-cong (lifts-cong e) τ)
sub-cong e (μ τ) = cong μ (sub-cong e τ)
sub-cong e ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
  sub-cong e ρ₁ | sub-cong e ρ₂ | sub-cong e ρ₃ | sub-cong e τ = refl
sub-cong e ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite
  sub-cong e ρ₁ | sub-cong e ρ₂ | sub-cong e τ = refl
sub-cong e (lab l) = refl
sub-cong e (τ₁ ▹ τ₂) = cong₂ _▹_ (sub-cong e τ₁) (sub-cong e τ₂)
sub-cong e ⌊ τ ⌋ = cong ⌊_⌋ (sub-cong e τ)
sub-cong e Π = refl
sub-cong e Σ = refl
sub-cong e (τ <$> τ₁) = cong₂ _<$>_ (sub-cong e τ) (sub-cong e τ₁)

sub-id : ∀ (τ : Type Δ κ) → sub ` τ ≡ τ
sub-id Unit = refl
sub-id ε = refl
sub-id (` α) = refl
sub-id (`λ τ) = cong `λ (trans (sub-cong  {σ₁ = lifts `} {σ₂ = `} lifts-id τ) (sub-id τ))
sub-id (τ₁ · τ₂) = cong₂ _·_ (sub-id τ₁) (sub-id τ₂)
sub-id (τ₁ `→ τ₂) = cong₂ _`→_ (sub-id τ₁) (sub-id τ₂)
sub-id (`∀ κ τ) = cong (`∀ κ) (trans (sub-cong lifts-id τ) (sub-id τ))
sub-id (μ τ) = cong μ (sub-id τ)
sub-id ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
  sub-id ρ₁ | sub-id ρ₂ | sub-id ρ₃ | sub-id τ = refl
sub-id ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite
  sub-id ρ₁ | sub-id ρ₂ | sub-id τ = refl
sub-id (lab l) = refl
sub-id (τ₁ ▹ τ₂) = cong₂ _▹_ (sub-id τ₁) (sub-id τ₂)
sub-id ⌊ τ ⌋ = cong ⌊_⌋ (sub-id τ)
sub-id Π = refl
sub-id Σ = refl
sub-id (τ₁ <$> τ₂) = cong₂ _<$>_ (sub-id τ₁) (sub-id τ₂)



-------------------------------------------------------------------------------
-- substitution and renaming commute

↻-sub-ren : ∀ {ρ : Renaming Δ₁ Δ₂}{σ : Substitution Δ₂ Δ₃}  
                (τ : Type Δ₁ κ) → sub (σ ∘ ρ) τ ≡ sub σ (ren ρ τ)
↻-sub-ren {ρ = ρ} {σ} Unit = refl
↻-sub-ren {ρ = ρ} {σ} ε = refl
↻-sub-ren {ρ = ρ} {σ} (` α) = refl
↻-sub-ren {ρ = ρ} {σ} (`λ τ) = cong `λ (trans (sub-cong lifts-lift τ) (↻-sub-ren τ))
↻-sub-ren {ρ = ρ} {σ} (τ₁ · τ₂) = cong₂ _·_ (↻-sub-ren τ₁) (↻-sub-ren τ₂)
↻-sub-ren {ρ = ρ} {σ} (τ₁ `→ τ₂) = cong₂ _`→_ (↻-sub-ren τ₁) (↻-sub-ren τ₂) 
↻-sub-ren {ρ = ρ} {σ} (`∀ κ τ) = cong (`∀ κ) (trans (sub-cong lifts-lift τ) (↻-sub-ren τ))
↻-sub-ren {ρ = ρ} {σ} (μ τ) = cong μ (↻-sub-ren τ)
↻-sub-ren {ρ = ρ} {σ} ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
    ↻-sub-ren {ρ = ρ} {σ} ρ₁ 
  | ↻-sub-ren {ρ = ρ} {σ} ρ₂ 
  | ↻-sub-ren {ρ = ρ} {σ} ρ₃ 
  | ↻-sub-ren {ρ = ρ} {σ} τ = refl
↻-sub-ren {ρ = ρ} {σ} ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite 
    ↻-sub-ren {ρ = ρ} {σ} ρ₁ 
  | ↻-sub-ren {ρ = ρ} {σ} ρ₂ 
  | ↻-sub-ren {ρ = ρ} {σ} τ = refl
↻-sub-ren {ρ = ρ} {σ} (lab l) = refl
↻-sub-ren {ρ = ρ} {σ} (τ₁ ▹ τ₂) = cong₂ _▹_ (↻-sub-ren τ₁) (↻-sub-ren τ₂) 
↻-sub-ren {ρ = ρ} {σ} ⌊ τ ⌋ = cong ⌊_⌋ (↻-sub-ren τ)
↻-sub-ren {ρ = ρ} {σ} Π = refl
↻-sub-ren {ρ = ρ} {σ} Σ = refl
↻-sub-ren {ρ = ρ} {σ} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-sub-ren τ₁) (↻-sub-ren τ₂) 

↻-ren-sub         : ∀ {σ : Substitution Δ₁ Δ₂}{ρ : Renaming Δ₂ Δ₃}(τ : Type Δ₁ κ) →
                    sub (ren ρ ∘ σ) τ ≡ ren ρ (sub σ τ)
↻-ren-sub {σ = σ} {ρ} Unit = refl
↻-ren-sub {σ = σ} {ρ} ε = refl
↻-ren-sub {σ = σ} {ρ} (` α) = refl
↻-ren-sub {σ = σ} {ρ} (`λ τ) = cong `λ (trans (sub-cong ren-lift-lifts τ) (↻-ren-sub τ))
↻-ren-sub {σ = σ} {ρ} (τ₁ · τ₂) = cong₂ _·_ (↻-ren-sub τ₁) (↻-ren-sub τ₂)
↻-ren-sub {σ = σ} {ρ} (τ₁ `→ τ₂) = cong₂ _`→_ (↻-ren-sub τ₁) (↻-ren-sub τ₂)
↻-ren-sub {σ = σ} {ρ} (`∀ κ τ) = cong (`∀ κ) (trans (sub-cong ren-lift-lifts τ) (↻-ren-sub τ))
↻-ren-sub {σ = σ} {ρ} (μ τ) = cong μ (↻-ren-sub τ)
↻-ren-sub {σ = σ} {ρ} ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
    ↻-ren-sub {σ = σ} {ρ} ρ₁ 
  | ↻-ren-sub {σ = σ} {ρ} ρ₂ 
  | ↻-ren-sub {σ = σ} {ρ} ρ₃ 
  | ↻-ren-sub {σ = σ} {ρ} τ = refl
↻-ren-sub {σ = σ} {ρ} ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite 
    ↻-ren-sub {σ = σ} {ρ} ρ₁ 
  | ↻-ren-sub {σ = σ} {ρ} ρ₂ 
  | ↻-ren-sub {σ = σ} {ρ} τ = refl
↻-ren-sub {σ = σ} {ρ} (lab l) = refl
↻-ren-sub {σ = σ} {ρ} (τ₁ ▹ τ₂) = cong₂ _▹_ (↻-ren-sub τ₁) (↻-ren-sub τ₂)
↻-ren-sub {σ = σ} {ρ} ⌊ τ ⌋ = cong ⌊_⌋ (↻-ren-sub τ)
↻-ren-sub {σ = σ} {ρ} Π = refl
↻-ren-sub {σ = σ} {ρ} Σ = refl
↻-ren-sub {σ = σ} {ρ} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-ren-sub τ₁) (↻-ren-sub τ₂)

sub-weaken : ∀ (τ : Type Δ κ₁) (v : Type Δ κ₂) → 
             sub (extend ` v) (ren S τ) ≡ τ 
sub-weaken τ v = trans (sym (↻-sub-ren {ρ = S} {σ = extend ` v} τ)) (sub-id τ)

-------------------------------------------------------------------------------
-- Arrow functor law for lifts & sub (needs commutativity of sub and ren)

lifts-comp : ∀ (σ₁ : Substitution Δ₁ Δ₂)(σ₂ : Substitution Δ₂ Δ₃)
                (x : KVar (Δ₁ ,, κ₁) κ₂) → lifts (sub σ₂ ∘ σ₁) x ≡ sub (lifts σ₂) (lifts σ₁ x)
lifts-comp σ₁ σ₂ Z = refl
lifts-comp σ₁ σ₂ (S x) = trans (sym (↻-ren-sub (σ₁ x))) (↻-sub-ren (σ₁ x)) 

sub-comp : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → sub (sub σ₂ ∘ σ₁) τ ≡ sub σ₂ (sub σ₁ τ)
sub-comp Unit = refl
sub-comp ε = refl
sub-comp (` α) = refl
sub-comp {σ₁ = σ₁} {σ₂ = σ₂} (`λ τ) = 
  cong `λ ((trans 
    (sub-cong (lifts-comp σ₁ σ₂) τ) 
    (sub-comp {σ₁ = lifts σ₁} {σ₂ = lifts σ₂} τ)))
sub-comp (τ₁ · τ₂) = cong₂ _·_ (sub-comp τ₁) (sub-comp τ₂)
sub-comp (τ₁ `→ τ₂) = cong₂ _`→_ (sub-comp τ₁) (sub-comp τ₂)
sub-comp {σ₁ = σ₁} {σ₂ = σ₂} (`∀ κ τ) =   
  cong (`∀ κ) ((trans 
    (sub-cong (lifts-comp σ₁ σ₂) τ) 
    (sub-comp {σ₁ = lifts σ₁} {σ₂ = lifts σ₂} τ)))
sub-comp (μ τ) = cong μ (sub-comp τ)
sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
    sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₁ 
  | sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₂ 
  | sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₃ 
  | sub-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite 
    sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₁ 
  | sub-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₂ 
  | sub-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
sub-comp (lab l) = refl
sub-comp (τ₁ ▹ τ₂) = cong₂ _▹_ (sub-comp τ₁) (sub-comp τ₂)
sub-comp ⌊ τ ⌋ = cong ⌊_⌋ (sub-comp τ)
sub-comp Π = refl
sub-comp Σ = refl
sub-comp (τ₁ <$> τ₂) = cong₂ _<$>_ (sub-comp τ₁) (sub-comp τ₂)

-------------------------------------------------------------------------------
-- 

ren-sub-id : ∀ (σ : Substitution Δ₁ Δ₂) (ρ : Renaming Δ₂ Δ₃) 
                (τ :  Type Δ₂ κ) → ren ρ τ ≡ sub (` ∘ ρ) τ
ren-sub-id σ ρ τ = trans (cong (ren ρ) (sym (sub-id τ))) (trans (sym (↻-ren-sub τ)) refl )

-------------------------------------------------------------------------------
-- Renaming commutes with β-reduction

↻-ren-β      : (ρ : Renaming Δ₁ Δ₂) (τ₁ : Type (Δ₁ ,, κ₁) κ₂) (τ₂ : Type Δ₁ κ₁) → 
                ren ρ (τ₁ β[ τ₂ ]) ≡ (ren (lift ρ) τ₁) β[ (ren ρ τ₂) ]  
↻-ren-β ρ τ₁ τ₂ = 
  trans 
    (sym (↻-ren-sub τ₁)) 
    (trans 
      (sub-cong (λ { Z → refl ; (S x) → refl }) τ₁) 
      (↻-sub-ren {ρ = lift ρ} {extend ` (ren ρ τ₂)} τ₁))                  


--------------------------------------------------------------------------------
-- renaming respects type equivalence

cong-ren-≡t : ∀ {τ υ : Type Δ₁ κ} (ρ : Renaming Δ₁ Δ₂) → 
                τ ≡t υ → ren ρ τ ≡t ren ρ υ 
cong-ren-≡p : ∀ {π₁ π₂ : Pred Δ₁ R[ κ ]} (ρ : Renaming Δ₁ Δ₂) → 
                π₁ ≡p π₂ → renPred ρ π₁ ≡p renPred ρ π₂

cong-ren-≡t {τ = τ} {υ} ρ eq-refl = eq-refl
cong-ren-≡t {τ = τ} {υ} ρ (eq-sym e) = eq-sym (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-trans e e₁) = eq-trans (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-→ e e₁) = eq-→ (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-∀ e) = eq-∀ (cong-ren-≡t (lift ρ) e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-μ e) = eq-μ (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-λ e) = eq-λ (cong-ren-≡t (lift ρ) e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-· e e₁) = eq-· (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-⌊⌋ e) = eq-⌊⌋ (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-▹ e e₁) = eq-▹ (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-⇒ x e) = eq-⇒ (cong-ren-≡p ρ x) (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {.(`λ (weaken τ · ` Z))} ρ eq-η = 
    eq-trans 
        (eq-η {f = ren ρ τ}) 
        (eq-λ (eq-· 
            (inst (sym (↻-lift-weaken ρ τ) )) 
            eq-refl))
cong-ren-≡t {τ = `λ τ₁ · τ₂} {.(τ₁ β[ τ₂ ])} ρ (eq-β {τ₁ = τ₁} {τ₂}) = 
    eq-trans 
        (eq-β {τ₁ = ren (lift ρ) τ₁} {ren ρ τ₂}) 
        (eq-sym (inst (↻-ren-β ρ τ₁ τ₂)))
cong-ren-≡t {τ = τ} {υ} ρ eq-Π▹ = eq-Π▹ 
cong-ren-≡t {τ = τ} {υ} ρ eq-Σ▹ = eq-Σ▹
cong-ren-≡t {τ = (Π · (l ▹ `λ τ))} {υ} ρ (eq-Πλ {l = l} {τ}) = 
    eq-trans 
    (eq-Πλ {l = ren ρ l} {ren (lift ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-lift-weaken ρ l))) eq-refl)))
cong-ren-≡t {τ = (Σ · (l ▹ `λ τ))} {υ} ρ (eq-Σλ {l = l} {τ}) = 
    eq-trans 
    (eq-Σλ {l = ren ρ l} {ren (lift ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-lift-weaken ρ l))) eq-refl)))
cong-ren-≡t {τ = τ} {υ} ρ eq-▹$ = eq-▹$
cong-ren-≡t {τ = τ} {υ} ρ eq-Π-assoc = eq-Π-assoc
cong-ren-≡t {τ = τ} {υ} ρ eq-Σ-assoc = eq-Σ-assoc
cong-ren-≡t {τ = τ} {υ} ρ eq-Π = eq-Π
cong-ren-≡t {τ = τ} {υ} ρ eq-Σ = eq-Σ
cong-ren-≡t {τ = τ} {υ} ρ (eq-<$> t u) = eq-<$> (cong-ren-≡t ρ t) (cong-ren-≡t ρ u)
cong-ren-≡t {τ = τ} {υ} ρ eq-<$>ε = eq-trans eq-<$>ε eq-refl

cong-ren-≡p {π₁} {π₂} ρ (eq₁ eq-≲ eq₂) = cong-ren-≡t ρ eq₁ eq-≲ cong-ren-≡t ρ eq₂
cong-ren-≡p {π₁} {π₂} ρ (eq₁ eq-· eq₂ ~ eq₃) = (cong-ren-≡t ρ eq₁) eq-· (cong-ren-≡t ρ eq₂) ~ (cong-ren-≡t ρ eq₃)
  
