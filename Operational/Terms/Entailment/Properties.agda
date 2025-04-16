{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Entailment.Properties where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Substitution
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.GVars



-- --------------------------------------------------------------------------------
-- List inclusion forms a pre-order

⊆-refl : ∀ {xs : SimpleRow NormalType Δ R[ κ ]} → 
         xs ⊆ xs 
⊆-refl x x∈xs = x∈xs

⊆-trans : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]} → 
          xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans i₁ i₂ = λ x → i₂ x ∘ i₁ x

-- --------------------------------------------------------------------------------
-- related elements are mapped


map-∈ :  ∀ {A B : Set}{xs : List A} {x : A} → 
             (f : A → B) → 
             x ∈ xs → 
             f x ∈ map f xs
map-∈ f (here refl) = here refl
map-∈ f (there x∈xs) = there (map-∈ f x∈xs)

-- --------------------------------------------------------------------------------
-- map f is monomorphic over _⊆_


⊆-map-mono : ∀ {A B : Set} {xs ys : List A} → 
             (f : A → B) → 
             xs ⊆ ys → 
             map f xs ⊆ map f ys 

⊆-map-mono {xs = []} {[]} f i = λ { x () }
⊆-map-mono {xs = []} {x ∷ ys} f i = λ { x () }
⊆-map-mono {xs = x ∷ xs} {[]} f i with i x (here refl)
... | ()
⊆-map-mono {xs = x ∷ xs} {y ∷ ys} f i z (here refl) = map-∈ f (i x (here refl)) 
⊆-map-mono {xs = x ∷ xs} {y ∷ ys} f i z (there z∈fxs) = ⊆-map-mono f (λ x₁ z₁ → i x₁ (there z₁)) z z∈fxs

absurd-left-elim : ∀ {A B : Set}{x : A} → x ∈ [] or B → B 
absurd-left-elim (right y) = y

absurd-right-elim : ∀ {A B : Set}{x : B} → A or x ∈ [] → A
absurd-right-elim (left x) = x

⊆-map-mono-or : ∀ {A B : Set} {xs ys zs : List A} → 
             (f : A → B) → 
             (∀ x → x ∈ xs → x ∈ ys or x ∈ zs) → 
             (∀ fx → fx ∈ map f xs → fx ∈ map f ys or fx ∈ map f zs)
⊆-map-mono-or {xs = x ∷ xs} {[]} {zs} f i fx fx∈ with i x (here refl) 
... | right y = right (⊆-map-mono f (λ x x∈xs → absurd-left-elim (i x x∈xs)) fx fx∈)
⊆-map-mono-or {xs = x ∷ xs} {y ∷ ys} {[]} f i fx fx∈ with i x (here refl) 
... | left h = left (⊆-map-mono f (λ x x∈xs → absurd-right-elim (i x x∈xs)) fx fx∈)
⊆-map-mono-or {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} f i fx (here refl) with i x (here refl) 
... | left x∈yys  = left (map-∈ f x∈yys)
... | right x∈zzs = right (map-∈ f x∈zzs)
⊆-map-mono-or {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} f i fx (there fx∈) = ⊆-map-mono-or f (λ x₁ z₁ → i x₁ (there z₁)) fx fx∈

-- --------------------------------------------------------------------------------
-- Containment is preserved under embedding 

⊆-⇑Row : ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]} → 
             xs ⊆ ys → 
             ⇑Row xs ⊆ ⇑Row ys
⊆-⇑Row {xs = xs} {ys} i rewrite 
    ⇑Row-isMap xs 
  | ⇑Row-isMap ys = ⊆-map-mono ⇑ i   

-- --------------------------------------------------------------------------------
-- Constructive reflexivity of row inclusion

≲-refl : ∀ {ρ₁ : SimpleRow NormalType ∅ R[ κ ]} → 
         Ent ∅ (⦅ ρ₁ ⦆ ≲ ⦅ ρ₁ ⦆)
≲-refl = n-≲ (λ x x∈xs → x∈xs) 

-- --------------------------------------------------------------------------------
-- Inversion of inclusion for simple rows


≲-inv : ∀ {ρ₁ ρ₂ : SimpleRow NormalType ∅ R[ κ ]} → 
         Ent ∅ (⦅ ρ₁ ⦆ ≲ ⦅ ρ₂ ⦆) → ρ₁ ⊆ ρ₂

-- --------------------------------------------------------------------------------
-- Inversion of combination


·-inv :  ∀ {ρ₁ ρ₂ ρ₃ : SimpleRow NormalType ∅ R[ κ ]} → 
         Ent ∅ (⦅ ρ₁ ⦆ · ⦅ ρ₂ ⦆ ~ ⦅ ρ₃ ⦆) → 
         ρ₁ ⊆ ρ₃ × 
         ρ₂ ⊆ ρ₃ × 
         (∀ x → x ∈ ρ₃ → x ∈ ρ₁ or x ∈ ρ₂)

-- --------------------------------------------------------------------------------
-- Definitions

≲-inv (n-≲ i) = i
≲-inv n-refl = λ x x∈xs → x∈xs 
≲-inv (n-trans {ρ₂ = ne x} e₁ e₂) = ⊥-elim (noNeutrals x)
≲-inv (n-trans {ρ₂ = ⦅ ρ₂ ⦆} e₁ e₂) = ⊆-trans (≲-inv e₁) (≲-inv e₂)
≲-inv (n-·≲L {ρ₂ = ne x} e) = ⊥-elim (noNeutrals x)
≲-inv (n-·≲L {ρ₂ = ⦅ ρ₂ ⦆} e) with ·-inv e 
... | (i₁ , i₂ , i₃) = i₁
≲-inv (n-·≲R {ρ₁ = ne x} e) = ⊥-elim (noNeutrals x)
≲-inv (n-·≲R {ρ₁ = ⦅ ρ₂ ⦆} e) with ·-inv e 
... | (i₁ , i₂ , i₃) = i₂
≲-inv (n-≲lift {ρ₁ = ⦅ xs ⦆} {⦅ ys ⦆} {F} n refl refl) = ⊆-map-mono (F ·'_) (≲-inv n)

·-inv (n-· ρ₁⊆ρ₃ ρ₂⊆ρ₃ ρ₃⊆) = ρ₁⊆ρ₃ , (ρ₂⊆ρ₃ , ρ₃⊆)
·-inv n-ε-R = ⊆-refl , (λ { x () }) , (λ x x∈ρ₁ → left x∈ρ₁)
·-inv n-ε-L = (λ { x () }) , ⊆-refl , (λ x x∈ → right x∈)
·-inv (n-·lift {ρ₁ = ⦅ x₃ ⦆} {⦅ x₄ ⦆} {⦅ x₅ ⦆} {F} e refl refl refl) with ·-inv e
... | i₁ , i₂ , i₃ =  ⊆-map-mono (F ·'_) i₁ , (⊆-map-mono (F ·'_) i₂) , ⊆-map-mono-or (F ·'_) i₃

-- --------------------------------------------------------------------------------
-- Entailment of inclusion is transitive

-- n-trans : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]} → 
--          Ent Γ (ρ₁ ≲ ρ₂) → Ent Γ (ρ₂ ≲ ρ₃) → Ent Γ (ρ₁ ≲ ρ₃)
-- n-trans {ρ₁ = ρ₁} {ρ₂} {ρ₃} ρ₁≲ρ₂ ρ₂≲ρ₃ = {!ρ₁ ρ₂ ρ₃!}

-- --------------------------------------------------------------------------------
-- -- The sum of two labeled rows is not a labeled row

-- ·-impossible :  ∀ {l₁ l₂ l₃ : NormalType ∅ L} {τ₁ τ₂ τ₃ :  NormalType ∅ κ} → 
--                 Ent ∅ ((l₁ ▹ τ₁) · (l₂ ▹ τ₂) ~ (l₃ ▹ τ₃)) → ⊥ 
-- ·-impossible  (n-·lift {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} e x x₁ x₂) = ·-impossible e

-- --------------------------------------------------------------------------------
-- -- If two rows combine to be the empty type then both are the empty row

-- ε-sum : Ent ∅ (ρ₁ · ρ₂ ~ ε) → ρ₁ ≡ ε × ρ₂ ≡ ε 
-- ε-sum n-ε-R = refl , refl
-- ε-sum n-ε-L = refl , refl
-- ε-sum (n-·lift {ρ₁ = ne x} {ρ₄} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ⊥-elim (noNeutrals x)
-- ε-sum (n-·lift {ρ₁ = ε} {ne x} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ⊥-elim (noNeutrals x)
-- ε-sum (n-·lift {ρ₁ = ε} {ε} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ρ₁-eq , ρ₂-eq
-- ε-sum (n-·lift {ρ₁ = ε} {l ▹ τ} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) with ε-sum e 
-- ... | () 
-- ε-sum (n-·lift {ρ₁ = ρ₃ ▹ ρ₅} {ρ₄} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) with ε-sum e 
-- ... | ()

-- --------------------------------------------------------------------------------
-- -- ε forms a least upper bound on rows

-- ε-minimum :  Ent ∅ (ρ ≲ ε) → ρ ≡ ε
-- ε-minimum (n-var ())
-- ε-minimum n-refl = refl
-- ε-minimum (n-trans e e₁) rewrite ε-minimum e₁ = ε-minimum e 
-- ε-minimum {ρ = ρ} (n-·≲L e) = fst (ε-sum e)
-- ε-minimum (n-·≲R e) = snd (ε-sum e)
-- ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = ne x₁} {ε} {F} e x y) = ⊥-elim (noNeutrals x₁) 
-- ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = ε} {ε} {F} e x y) = x
-- ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = l ▹ τ} {ε} {f} e x y) with ε-minimum e
-- ... | () 


-- --------------------------------------------------------------------------------
-- -- ε is the *unique* right identity

-- ε-right-unique : Ent ∅ (ρ₁ · ρ₂ ~ ρ₁) → ρ₂ ≡ ε
-- ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-R = refl
-- ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-L = refl
-- ε-right-unique {ρ₁ = ne x} {_} (n-·lift e _ _ _) = ⊥-elim (noNeutrals x)
-- ε-right-unique {ρ₁ = _} {ne x} (n-·lift e _ _ _ ) = ⊥-elim (noNeutrals x)
-- ε-right-unique {ρ₁ = ε} {ε} (n-·lift e x x₁ x₂) = refl
-- ε-right-unique {ρ₁ = ε} {l ▹ τ} (n-·lift {ρ₁ = ε} {ρ₂ = l' ▹ τ'} {ε} {F = `λ F} e x x₁ x₂) with ε-right-unique e
-- ... | () 
-- ε-right-unique {ρ₁ = ρ₁ ▹ ρ₂} {ε} (n-·lift e x x₁ x₂) = refl
-- ε-right-unique {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ ▹ ρ₃} {l₄ ▹ τ₄} e x x₁ x₂) = ⊥-elim (·-impossible e) 

-- --------------------------------------------------------------------------------
-- -- Reflection of combination equality to propositional equality

-- ε-right-identity : Ent ∅ (ρ₁ · ε ~ ρ₂) → ρ₁ ≡ ρ₂
-- ε-left-identity : Ent ∅ (ε · ρ₁ ~ ρ₂) → ρ₁ ≡ ρ₂

-- ε-right-identity n-ε-R = refl
-- ε-right-identity n-ε-L = refl
-- ε-right-identity (n-·lift {ρ₁ = ne x₃} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- ε-right-identity {ρ₁ = ε} {ρ₂ = ne x₃} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- ε-right-identity {ρ₁ = ε} {ρ₂ = ε} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = refl
-- ε-right-identity {ρ₁ = ε} {ρ₂ = ρ₂ ▹ ρ₄} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃ ▹ ρ₅} e x x₁ x₂) with ε-right-identity e
-- ... | () 
-- ε-right-identity {ρ₁ = ρ₁ ▹ ρ₂} {ne x₃} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- ε-right-identity {ρ₁ = l₁ ▹ τ₁} {ε} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) with trans (ε-right-identity e) (ε-<$>' (sym x₂))
-- ... | () 
-- ε-right-identity {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ = ε} {l₄ ▹ τ₄} {F} e x x₁ x₂) = 
--   trans x (trans (cong₂ _▹_ (inj-▹ₗ (ε-right-identity e)) (cong (F ·'_) (inj-▹ᵣ (ε-right-identity e)))) (sym x₂))


-- ε-left-identity n-ε-R = refl
-- ε-left-identity n-ε-L = refl
-- ε-left-identity (n-·lift {ρ₁ = ε} {ne x₃} {_} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- ε-left-identity (n-·lift {ρ₁ = ε} {_} {ne x₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- ε-left-identity (n-·lift {ρ₁ = ε} {ε} {ε} e x x₁ x₂) = trans x₁ (sym x₂)
-- ε-left-identity (n-·lift {ρ₁ = ε} {ε} {ρ₃ ▹ ρ₄} e x x₁ x₂) with  ε-left-identity e  
-- ... | () 
-- ε-left-identity (n-·lift {ρ₁ = ε} {ρ₂ ▹ ρ₃} {ε} e x x₁ x₂) with ε-left-identity e
-- ... | ()
-- ε-left-identity (n-·lift {ρ₁ = ε} {ρ₂ ▹ ρ₃} {ρ₄ ▹ ρ₅} {F} e x x₁ x₂) = 
--   trans 
--     x₁ 
--     (trans 
--       (cong₂ _▹_ 
--         (inj-▹ₗ (ε-left-identity e)) 
--         (cong (F ·'_) (inj-▹ᵣ (ε-left-identity e)))) 
--       (sym x₂)) 


-- --------------------------------------------------------------------------------
-- -- Reflection of labeled row reflexivity to propositional equality

-- ≲-refl :  ∀ {l₁ l₂ : NormalType ∅ L} {τ₁ τ₂ :  NormalType ∅ κ} → Ent ∅ ((l₁ ▹ τ₁) ≲ (l₂ ▹ τ₂)) → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂)
-- ≲-refl (n-var ())
-- ≲-refl n-refl = refl
-- ≲-refl (n-trans {ρ₂ = ne x} e e₁) = ⊥-elim (noNeutrals x) 
-- ≲-refl (n-trans {ρ₂ = ε} e e₁) with ε-minimum e
-- ... | () 
-- ≲-refl (n-trans {ρ₂ = l₂ ▹ τ₂} e e₁) = trans (≲-refl e) (≲-refl e₁)
-- ≲-refl (n-·≲L {ρ₂ = ne x} e) = ⊥-elim (noNeutrals x)
-- ≲-refl (n-·≲L {ρ₂ = ε} e) = ε-right-identity e
-- ≲-refl (n-·≲L {ρ₂ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e)  
-- ≲-refl (n-·≲R {ρ₁ = ne x} e) = ⊥-elim (noNeutrals x)
-- ≲-refl (n-·≲R {ρ₁ = ε} e) = ε-left-identity e
-- ≲-refl (n-·≲R {ρ₁ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e) 
-- ≲-refl (n-≲lift {ρ₁ = l₃ ▹ τ₃} {l₄ ▹ τ₄} {F} e x x₁) = 
--   trans 
--     x 
--     (trans 
--       (cong₂ _▹_ 
--         (inj-▹ₗ (≲-refl e)) 
--         (cong (F ·'_) (inj-▹ᵣ (≲-refl e)))) 
--       (sym x₁))     
 
--  --------------------------------------------------------------------------------
-- -- Problems

-- no-meaningful-combinations : Ent ∅ (ρ₁ · ρ₂ ~ ρ₃) → ρ₁ ≡ ε or ρ₂ ≡ ε 
-- no-meaningful-combinations {ρ₁ = ne x} {ρ₂} {ρ₃} e = ⊥-elim (noNeutrals x)
-- no-meaningful-combinations {ρ₁ = ρ₁} {ne x} {ρ₃} e = ⊥-elim (noNeutrals x)
-- no-meaningful-combinations {ρ₁ = ρ₁} {ρ₂} {ne x} e = ⊥-elim (noNeutrals x)
-- no-meaningful-combinations {ρ₁ = ε} {ρ₂} {ρ₃} e = left refl
-- no-meaningful-combinations {ρ₁ = ρ₁} {ε} {ρ₃} e = right refl
-- no-meaningful-combinations {ρ₁ = ρ₁ ▹ ρ₄} {ρ₂ ▹ ρ₅} {ε} e = left (ε-minimum (n-·≲L e))
-- no-meaningful-combinations {ρ₁ = ρ₁ ▹ ρ₄} {ρ₂ ▹ ρ₅} {ρ₃ ▹ ρ₆} e = ⊥-elim (·-impossible e)




