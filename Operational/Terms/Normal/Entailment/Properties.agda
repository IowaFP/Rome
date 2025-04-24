{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Normal.Entailment.Properties where

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

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.GVars

open import Rome.Operational.Containment

-- --------------------------------------------------------------------------------
-- Constructive reflexivity of row inclusion

≲-refl : ∀ {ρ₁ : SimpleRow NormalType ∅ R[ κ ]} → 
         NormalEnt ∅ (⦅ ρ₁ ⦆ ≲ ⦅ ρ₁ ⦆)
≲-refl = n-≲ (λ x x∈xs → x∈xs) 

-- --------------------------------------------------------------------------------
-- Inversion of inclusion for simple rows


≲-inv : ∀ {ρ₁ ρ₂ : SimpleRow NormalType ∅ R[ κ ]} → 
         NormalEnt ∅ (⦅ ρ₁ ⦆ ≲ ⦅ ρ₂ ⦆) → ρ₁ ⊆ ρ₂

-- --------------------------------------------------------------------------------
-- Inversion of combination


·-inv :  ∀ {ρ₁ ρ₂ ρ₃ : SimpleRow NormalType ∅ R[ κ ]} → 
         NormalEnt ∅ (⦅ ρ₁ ⦆ · ⦅ ρ₂ ⦆ ~ ⦅ ρ₃ ⦆) → 
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
≲-inv (n-≲lift {ρ₁ = ⦅ xs ⦆} {⦅ ys ⦆} {F} n refl refl) = ⊆-map (F ·'_) (≲-inv n)

·-inv (n-· ρ₁⊆ρ₃ ρ₂⊆ρ₃ ρ₃⊆) = ρ₁⊆ρ₃ , (ρ₂⊆ρ₃ , ρ₃⊆)
·-inv n-ε-R = ⊆-refl , (λ { x () }) , (λ x x∈ρ₁ → left x∈ρ₁)
·-inv n-ε-L = (λ { x () }) , ⊆-refl , (λ x x∈ → right x∈)
·-inv (n-·lift {ρ₁ = ⦅ x₃ ⦆} {⦅ x₄ ⦆} {⦅ x₅ ⦆} {F} e refl refl refl) with ·-inv e
... | i₁ , i₂ , i₃ =  ⊆-map (F ·'_) i₁ , (⊆-map (F ·'_) i₂) , ⊆-map-or (F ·'_) i₃


--------------------------------------------------------------------------------
-- Normalizing entailments to contain just simple rows.
-- Combined with inversion above, this gives us normal forms for entailments (n-≲ and n-·).

norm₁ : NormalEnt ∅ (ρ₁ ≲ ρ₂) → ∃[ xs ] (∃[ ys ] (
        ρ₁ ≡ ⦅ xs ⦆ × 
        ρ₂ ≡ ⦅ ys ⦆))
norm₂ : NormalEnt ∅ (ρ₁ · ρ₂ ~ ρ₃) → ∃[ xs ] (∃[ ys ] (∃[ zs ] (
        ρ₁ ≡ ⦅ xs ⦆ × 
        ρ₂ ≡ ⦅ ys ⦆ × 
        ρ₃ ≡ ⦅ zs ⦆)))

norm₁ (n-≲ {xs = xs} {ys} i) = xs , (ys , (refl , (refl)))
norm₁ {ρ₁ = ne x} n-refl = ⊥-elim (noNeutrals x)
norm₁ {ρ₁ = ⦅ xs ⦆} n-refl = xs , (xs , (refl , (refl)))
norm₁ {ρ₁ = ρ₁} (n-trans {ρ₂ = ρ₂} {ρ₃ = ρ₃} n₁ n₂) with norm₁ n₁ | norm₁ n₂ 
... | (xs , ys , refl , refl) | (ys , zs , refl , refl) = xs , zs , refl , refl 
norm₁ (n-·≲L n) with norm₂ n 
... | xs , ys , zs , refl , refl , refl  = xs , zs , refl , refl
norm₁ (n-·≲R n) with norm₂ n 
... | xs , ys , zs , refl , refl , refl = ys , zs , refl , refl
norm₁ (n-≲lift {F = F} n eq₁ eq₂) with norm₁ n 
... | xs , ys , refl , refl = map (F ·'_) xs , (map (F ·'_) ys , (eq₁ , eq₂))

norm₂ (n-· {xs = xs} {ys} {zs} i₁ i₂ i₃) = xs , (ys , (zs , (refl , refl , refl)))
norm₂ {ρ₁ = ne x} n-ε-R = ⊥-elim (noNeutrals x)
norm₂ {ρ₁ = ⦅ xs ⦆} n-ε-R = xs , [] , xs , refl , refl , refl
norm₂ {ρ₂ = ne x} n-ε-L = ⊥-elim (noNeutrals x)
norm₂ {ρ₂ = ⦅ xs ⦆} n-ε-L = [] , xs , xs , refl , refl , refl
norm₂ (n-·lift {F = F} n eq₁ eq₂ eq₃) with norm₂ n 
... | xs , ys , zs , refl , refl , refl = map (F ·'_) xs , map (F ·'_) ys , map (F ·'_) zs , eq₁ , eq₂ , eq₃

-- --------------------------------------------------------------------------------
-- NormalEntailment of inclusion is transitive

-- n-trans : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]} → 
--          NormalEnt Γ (ρ₁ ≲ ρ₂) → NormalEnt Γ (ρ₂ ≲ ρ₃) → NormalEnt Γ (ρ₁ ≲ ρ₃)
-- n-trans {ρ₁ = ρ₁} {ρ₂} {ρ₃} ρ₁≲ρ₂ ρ₂≲ρ₃ = {!ρ₁ ρ₂ ρ₃!}

-- --------------------------------------------------------------------------------
-- -- The sum of two labeled rows is not a labeled row

-- ·-impossible :  ∀ {l₁ l₂ l₃ : NormalType ∅ L} {τ₁ τ₂ τ₃ :  NormalType ∅ κ} → 
--                 NormalEnt ∅ ((l₁ ▹ τ₁) · (l₂ ▹ τ₂) ~ (l₃ ▹ τ₃)) → ⊥ 
-- ·-impossible  (n-·lift {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} e x x₁ x₂) = ·-impossible e

-- --------------------------------------------------------------------------------
-- -- If two rows combine to be the empty type then both are the empty row

ε-sum : NormalEnt ∅ (ρ₁ · ρ₂ ~ εNF) → ρ₁ ≡ εNF × ρ₂ ≡ εNF
ε-sum (n-· {xs = []} {[]} i₁ i₂ i₃) = refl , refl
ε-sum (n-· {xs = xs} {y ∷ ys} i₁ i₂ i₃) = ∈-elim (i₂ y (here refl))
ε-sum (n-· {xs = x ∷ xs} {ys} i₁ i₂ i₃) = ∈-elim (i₁ x (here refl))
ε-sum n-ε-R = refl , refl
ε-sum n-ε-L = refl , refl
ε-sum (n-·lift {ρ₁ = ρ₁} {ρ₂} {⦅ [] ⦆} {F = F} e eq₁ eq₂ eq₃) with ε-sum e 
... | refl , refl = eq₁ , eq₂

-- --------------------------------------------------------------------------------
-- -- ε forms a least upper bound on rows

ε-minimum :  NormalEnt ∅ (ρ ≲ εNF) → ρ ≡ εNF
ε-minimum (n-≲ {xs = []} i) = refl
ε-minimum (n-≲ {xs = x ∷ xs} i) = ∈-elim (i x (here refl))
ε-minimum (n-≲lift {ρ₁ = ne x} _ _ _) = ⊥-elim (noNeutrals x)
ε-minimum (n-≲lift {ρ₁ = ⦅ xs ⦆} {⦅ [] ⦆} n refl refl) with ε-minimum n 
... | refl = refl
ε-minimum (n-var ())
ε-minimum n-refl = refl
ε-minimum (n-trans e e₁) rewrite ε-minimum e₁ = ε-minimum e 
ε-minimum {ρ = ρ} (n-·≲L e) = fst (ε-sum e)
ε-minimum (n-·≲R e) = snd (ε-sum e)

-- --------------------------------------------------------------------------------
-- -- If two rows combine to be the empty type then both are the empty row

singleton-sum : NormalEnt ∅ (ρ₁ · ρ₂ ~ ⦅ [ τ ] ⦆) → ρ₁ ≡ ⦅ [ τ ] ⦆ or ρ₂ ≡ ⦅ [ τ ] ⦆
singleton-sum {τ = τ} (n-· {xs = []} {[]} i₁ i₂ i₃) = ∈-elim (absurd-left-elim (i₃ τ (here refl)))
singleton-sum {τ = τ} (n-· {xs = []} {y ∷ ys} i₁ i₂ i₃) = {!   !}
singleton-sum {τ = τ} (n-· {xs = x ∷ xs} {[]} i₁ i₂ i₃) = {!   !}
singleton-sum {τ = τ} (n-· {xs = x ∷ xs} {x₁ ∷ ys} i₁ i₂ i₃) = {!   !} 
singleton-sum n-ε-R = {!   !}
singleton-sum n-ε-L = {!   !}
singleton-sum (n-·lift e x x₁ x₂) = {!   !}

-- --------------------------------------------------------------------------------
-- -- ε is the *unique* right identity

-- ε-right-unique : NormalEnt ∅ (ρ₁ · ρ₂ ~ ρ₁) → ρ₂ ≡ ε
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

-- ε-right-identity : NormalEnt ∅ (ρ₁ · ε ~ ρ₂) → ρ₁ ≡ ρ₂
-- ε-left-identity : NormalEnt ∅ (ε · ρ₁ ~ ρ₂) → ρ₁ ≡ ρ₂

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

-- ≲-refl :  ∀ {l₁ l₂ : NormalType ∅ L} {τ₁ τ₂ :  NormalType ∅ κ} → NormalEnt ∅ ((l₁ ▹ τ₁) ≲ (l₂ ▹ τ₂)) → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂)
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

-- no-meaningful-combinations : NormalEnt ∅ (ρ₁ · ρ₂ ~ ρ₃) → ρ₁ ≡ ε or ρ₂ ≡ ε 
-- no-meaningful-combinations {ρ₁ = ne x} {ρ₂} {ρ₃} e = ⊥-elim (noNeutrals x)
-- no-meaningful-combinations {ρ₁ = ρ₁} {ne x} {ρ₃} e = ⊥-elim (noNeutrals x)
-- no-meaningful-combinations {ρ₁ = ρ₁} {ρ₂} {ne x} e = ⊥-elim (noNeutrals x)
-- no-meaningful-combinations {ρ₁ = ε} {ρ₂} {ρ₃} e = left refl
-- no-meaningful-combinations {ρ₁ = ρ₁} {ε} {ρ₃} e = right refl
-- no-meaningful-combinations {ρ₁ = ρ₁ ▹ ρ₄} {ρ₂ ▹ ρ₅} {ε} e = left (ε-minimum (n-·≲L e))
-- no-meaningful-combinations {ρ₁ = ρ₁ ▹ ρ₄} {ρ₂ ▹ ρ₅} {ρ₃ ▹ ρ₆} e = ⊥-elim (·-impossible e)




