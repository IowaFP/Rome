{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Normal.Entailment.Properties where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Equivalence.Relation

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
           {oρ₁ : True (normalOrdered? ρ₁)}  → 
         NormalEnt ∅ ((⦅ ρ₁ ⦆ oρ₁) ≲ (⦅ ρ₁ ⦆ oρ₁))
≲-refl = n-≲ (λ x x∈xs → x∈xs) 

--------------------------------------------------------------------------------
-- Entailments in empty contexts contain only simple rows.

norm-≲ : NormalEnt ∅ (ρ₁ ≲ ρ₂) → 
        ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
        ∃[ ys ] Σ[ oys ∈ True (normalOrdered? ys) ] 
        (ρ₁ ≡ ⦅ xs ⦆ oxs × ρ₂ ≡ ⦅ ys ⦆ oys)

norm-· : NormalEnt ∅ (ρ₁ · ρ₂ ~ ρ₃) → 
        ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
        ∃[ ys ] Σ[ oys ∈ True (normalOrdered? ys) ] 
        ∃[ zs ] Σ[ ozs ∈ True (normalOrdered? zs) ] 
        (ρ₁ ≡ ⦅ xs ⦆ oxs × ρ₂ ≡ ⦅ ys ⦆ oys × ρ₃ ≡ ⦅ zs ⦆ ozs)

norm-≲ (n-≲ {xs = xs} {ys} {oxs} {oys} i) = xs , oxs , ys , oys , refl , refl
norm-≲ {ρ₁ = ne x} n-refl = ⊥-elim (noNeutrals x)
norm-≲ {ρ₁ = ⦅ xs ⦆ oxs} n-refl = xs , oxs , xs , oxs , refl , refl
norm-≲ {ρ₁ = (c ─ c₁) {nsr}} n-refl = ⊥-elim (noComplements nsr refl)
norm-≲ {ρ₁ = l ▹ₙ c} n-refl = ⊥-elim (noNeutrals l)
norm-≲ {ρ₁ = ρ₁} (n-trans {ρ₂ = ρ₂} {ρ₃ = ρ₃} n₁ n₂) with norm-≲ n₁ | norm-≲ n₂ 
... | (xs , oxs , ys , oys , refl , refl) | (ys' , oys' , zs , ozs , refl , refl) = 
  xs , oxs , zs , ozs , refl , refl 
norm-≲ (n-·≲L en) with norm-· en 
... | xs , oxs , ys , oys , zs , ozs , refl , refl , refl = xs , oxs , zs , ozs , refl , refl
norm-≲ (n-·≲R en) with norm-· en 
... | xs , oxs , ys , oys , zs , ozs , refl , refl , refl = ys , oys , zs , ozs , refl , refl
norm-≲ (n-≲lift {F = F} en refl refl) with norm-≲ en 
... | xs , oxs , ys , oys , refl , refl = 
  map (overᵣ (F ·'_)) xs , 
  fromWitness (normal-map-overᵣ xs (F ·'_) (toWitness oxs)) , 
  (map (overᵣ (F ·'_)) ys) , 
  fromWitness (normal-map-overᵣ ys (F ·'_) (toWitness oys)) , 
  cong-⦅⦆ (sym (stability-map F xs)) , 
  cong-⦅⦆ (sym (stability-map F ys))

norm-· (n-· {xs = xs} {ys} {zs} {oxs = oxs} {oys} {ozs} i₁ i₂ i₃) = 
  xs , oxs , ys , oys , zs , ozs , refl , refl , refl
norm-· {ρ₁ = ne x₁} n-ε-R = ⊥-elim (noNeutrals x₁)
norm-· {ρ₁ = ⦅ xs ⦆ oxs} n-ε-R = xs , oxs , [] , tt , xs , oxs , refl , refl , refl
norm-· {ρ₁ = (ρ₁ ─ ρ₂) {nsr}} n-ε-R = ⊥-elim (noComplements nsr refl)
norm-· {ρ₁ = l ▹ₙ ρ₁} n-ε-R = ⊥-elim (noNeutrals l)
norm-· {ρ₂ = ne x₁} n-ε-L = ⊥-elim (noNeutrals x₁)
norm-· {ρ₂ = ⦅ ρ ⦆ oρ} n-ε-L = [] , tt , ρ , oρ , ρ , oρ , refl , refl , refl
norm-· {ρ₂ = (_ ─ _) {nsr}} n-ε-L = ⊥-elim (noComplements nsr refl)
norm-· {ρ₂ = l ▹ₙ _} n-ε-L = ⊥-elim (noNeutrals l)
norm-· (n-·lift {F = F} n refl refl refl) with norm-· n
... | xs , oxs , ys , oys , zs , ozs , refl , refl , refl  = 
  map (overᵣ (F ·'_)) xs , 
  fromWitness (normal-map-overᵣ xs (F ·'_) (toWitness oxs)) , 
  (map (overᵣ (F ·'_)) ys) , 
  fromWitness (normal-map-overᵣ ys (F ·'_) (toWitness oys)) , 
  (map (overᵣ (F ·'_)) zs) , 
  fromWitness (normal-map-overᵣ zs (F ·'_) (toWitness ozs)) , 
  cong-⦅⦆ (sym (stability-map F xs)) , 
  cong-⦅⦆ (sym (stability-map F ys)) ,
  cong-⦅⦆ (sym (stability-map F zs))
norm-· {ρ₁ = ρ₁} {ρ₃ = ρ₃} (n-·complᵣ {nsr = nsr} n) with norm-≲ n | nsr
... | xs , oxs , ys , oys , refl , refl | ()
norm-· (n-·complᵣ' {xs = xs} {ys} {oxs} {oys} {ozs} n) = xs , oxs , ⇓Row (⇑Row ys ─s ⇑Row xs) , ozs , ys , oys , refl , refl , refl
norm-· {ρ₂ = ρ₂} {ρ₃} (n-·complₗ {nsr = nsr} n) with norm-≲ n | nsr
... | _ , _ , _ , _ , refl , refl | ()
norm-· (n-·complₗ' {xs = xs} {ys} {oxs} {oys} {ozs} n) = ⇓Row (⇑Row ys ─s ⇑Row xs) , ozs , xs , oxs , ys , oys , refl , refl , refl


-- --------------------------------------------------------------------------------
-- Inversion of inclusion for simple rows


≲-inv : ∀ {ρ₁ ρ₂ : SimpleRow NormalType ∅ R[ κ ]} → 
          {oρ₁ : True (normalOrdered? ρ₁)}
          {oρ₂ : True (normalOrdered? ρ₂)} → 
         NormalEnt ∅ ((⦅ ρ₁ ⦆ oρ₁) ≲ (⦅ ρ₂ ⦆ oρ₂)) → ρ₁ ⊆ ρ₂

--------------------------------------------------------------------------------
-- Inversion of combination


·-inv :  ∀ {ρ₁ ρ₂ ρ₃ : SimpleRow NormalType ∅ R[ κ ]}
          {oρ₁ : True (normalOrdered? ρ₁)}
          {oρ₂ : True (normalOrdered? ρ₂)} 
          {oρ₃ : True (normalOrdered? ρ₃)} → 
         NormalEnt ∅ (⦅ ρ₁ ⦆ oρ₁ · ⦅ ρ₂ ⦆ oρ₂ ~ ⦅ ρ₃ ⦆ oρ₃) → 
         ρ₁ ⊆ ρ₃ × 
         ρ₂ ⊆ ρ₃ × 
         (∀ x → x ∈ ρ₃ → x ∈ ρ₁ or x ∈ ρ₂)

--------------------------------------------------------------------------------
-- Lemmas about inclusion (needed to prove inversion for n-·compl rules)

⇓Row-mono : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → 
              ρ₁ ⊆ ρ₂ → 
              ⇓Row ρ₁ ⊆ ⇓Row ρ₂ 
⇓Row-mono {ρ₁ = ρ₁} {ρ₂} = ⊆-cong _ ⇓Row (⇓Row-isMap idEnv)

─s-mono : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → 
               (ρ₂ ─s ρ₁) ⊆ ρ₂ 
─s-mono {ρ₁ = ρ₁} {ρ₂ = []} = λ { i () }
─s-mono {ρ₁ = ρ₁} {ρ₂ = (l , τ) ∷ ρ₂} with l ∈L? ρ₁ 
... | yes p = λ { x i → there (─s-mono {ρ₁ = ρ₁} {ρ₂} x i)} 
... | no  q = λ { (.l , .τ) (here refl) → here refl ; x (there i) → there (─s-mono {ρ₁ = ρ₁} {ρ₂} x i) }

⇓Row-⇑Row-─s-mono : ∀ (ρ₁ ρ₂ : SimpleRow NormalType ∅ R[ κ ]) → 
       ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊆ ρ₂
⇓Row-⇑Row-─s-mono ρ₁ ρ₂ = 
  subst 
    (λ x → ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊆ x) 
    (stabilityRow ρ₂) 
    (⇓Row-mono (─s-mono {ρ₁ = ⇑Row ρ₁} {⇑Row ρ₂}))

∈-irrelevant : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → 
                 {oρ : Ordered ρ} → 
                 (l : Label) (τ : Type Δ κ) → 
                 Irrelevant ((l , τ) ∈ ρ)
∈-irrelevant ρ {oρ} l τ (here refl) (here refl) = refl
∈-irrelevant ((l , τ) ∷ ρ) {l<l , snd₁} l τ (here refl) (there (here refl)) = {!l<l is contradiction!}
∈-irrelevant ((l , τ) ∷ (l' , τ') ∷ ρ) {oρ} l τ (here refl) (there (there p₂)) = {!!}
∈-irrelevant ρ {oρ} l τ (there p₁) (here px) = {!!}
∈-irrelevant ρ {oρ} l τ (there p₁) (there p₂) = {!!}

∈-irrelevant' : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → 
                 {oρ : Ordered ρ} → 
                 (l : Label) (τ τ' : Type Δ κ) → 
                 (l , τ) ∈ ρ → (l , τ') ∈ ρ → 
                 τ ≡ τ'
∈-irrelevant' ρ {oρ} l τ τ' (here refl) (here refl) = refl
∈-irrelevant' ρ {oρ} l τ τ' (here refl) (there (here refl)) = {!contradiction (oρ .fst)!}
∈-irrelevant' ((l , τ) ∷ (l₃ , τ₃) ∷ xs) {oρ} l τ τ' (here refl) (there (there {l₃ , τ₃} {xs} τ'∈ρ)) = 
  ∈-irrelevant' ((l , τ) ∷ xs) {ordered-swap (oρ .fst) (oρ .snd)} l τ τ' (here refl) (there τ'∈ρ)
∈-irrelevant' ρ {oρ} l τ τ' (there τ∈ρ) (here refl) = {!!}
∈-irrelevant' ρ {oρ} l τ τ' (there τ∈ρ) (there τ'∈ρ) = {!!}

─s-mono-orᵣ : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → 
               ρ₁ ⊆ ρ₂ → 
               ρ₂ ⊆[ ρ₁ ⊹ (ρ₂ ─s ρ₁) ]
─s-mono-orᵣ {ρ₁ = ρ₁} {(l , τ₂) ∷ ρ₂} i (l , τ) (here refl) with l ∈L? ρ₁ 
─s-mono-orᵣ {ρ₁ = (l , τ₁) ∷ ρ₁} {(l , τ₂) ∷ ρ₂} i (l , τ) (here refl) | yes Here with i (l , τ₁) (here refl)
... | here refl = left (here refl)
... | there c = {!!} -- left (there {!∈-irrelevant' ρ₂ {?} l τ₁ τ₂ c !})
─s-mono-orᵣ {ρ₁ = ρ₁} {(l , τ₂) ∷ ρ₂} i (l , τ) (here refl) | yes (There p₁) = left {!!}
─s-mono-orᵣ {ρ₁ = ρ₁} {(l , τ₂) ∷ ρ₂} i (l , τ) (here refl) | no  q = right (here refl)
─s-mono-orᵣ {ρ₁ = ρ₁} {(l₂ , τ₂) ∷ ρ₂} i (l , τ) (there ∈ρ₂) = {!!}

─s-mono-orₗ : ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → 
               ρ₁ ⊆ ρ₂ → 
               ρ₂ ⊆[ (ρ₂ ─s ρ₁) ⊹ ρ₁ ]
─s-mono-orₗ i = {!!}

⇓Row-⇑Row-─s-mono-orᵣ : 
  ∀ (ρ₁ ρ₂ : SimpleRow NormalType ∅ R[ κ ]) → 
    ρ₁ ⊆ ρ₂ → 
    ρ₂ ⊆[ ρ₁ ⊹ (⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁)) ]
⇓Row-⇑Row-─s-mono-orᵣ ρ₁ ρ₂ i = 
  subst 
    (λ x → ρ₂ ⊆[ x ⊹ ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ])
    (stabilityRow ρ₁)
    (subst 
      (λ x → x ⊆[ ⇓Row (⇑Row ρ₁) ⊹ ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ]) 
      (stabilityRow ρ₂)
      (⊆-cong-or _ ⇓Row (⇓Row-isMap idEnv) (─s-mono-orᵣ {ρ₁ = (⇑Row ρ₁)} {(⇑Row ρ₂)} (⊆-cong _ ⇑Row ⇑Row-isMap i))))

⇓Row-⇑Row-─s-mono-orₗ : 
  ∀ (ρ₁ ρ₂ : SimpleRow NormalType ∅ R[ κ ]) → 
    ρ₁ ⊆ ρ₂ → 
    ρ₂ ⊆[ (⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁)) ⊹ ρ₁ ]
⇓Row-⇑Row-─s-mono-orₗ ρ₁ ρ₂ i =
  subst 
    (λ x → ρ₂ ⊆[ ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊹ x ])
    (stabilityRow ρ₁)
    (subst 
      (λ x → x ⊆[  ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊹ ⇓Row (⇑Row ρ₁) ]) 
      (stabilityRow ρ₂)
      ((⊆-cong-or _ ⇓Row (⇓Row-isMap idEnv) (─s-mono-orₗ {ρ₁ = (⇑Row ρ₁)} {(⇑Row ρ₂)} (⊆-cong _ ⇑Row ⇑Row-isMap i)))))

-- --------------------------------------------------------------------------------
-- Definitions

≲-inv (n-≲ i) = i
≲-inv n-refl = λ x x∈xs → x∈xs 
≲-inv (n-trans {ρ₂ = ne x} e₁ e₂) = ⊥-elim (noNeutrals x)
≲-inv (n-trans {ρ₂ = ⦅ ρ₂ ⦆ _} e₁ e₂) = ⊆-trans (≲-inv e₁) (≲-inv e₂)
≲-inv (n-trans {ρ₂ = ρ₂@((ρ ─ ρ') {nsr})} e₁ e₂) = ⊥-elim (noComplements nsr refl)
≲-inv (n-trans {ρ₂ = l ▹ₙ c} e₁ e₂) = ⊥-elim (noNeutrals l) 
≲-inv (n-·≲L {ρ₂ = ne x} e) = ⊥-elim (noNeutrals x)
≲-inv (n-·≲L {ρ₂ = (c ─ c₁) {nsr}} e) = ⊥-elim (noComplements nsr refl)
≲-inv (n-·≲L {ρ₂ = l ▹ₙ c} e) = ⊥-elim (noNeutrals l)
≲-inv (n-·≲L {ρ₂ = ⦅ ρ₂ ⦆ _} e) with ·-inv e 
... | (i₁ , i₂ , i₃) = i₁
≲-inv (n-·≲R {ρ₁ = ne x} e) = ⊥-elim (noNeutrals x)
≲-inv (n-·≲R {ρ₁ = ⦅ ρ₂ ⦆ _} e) with ·-inv e 
... | (i₁ , i₂ , i₃) = i₂
≲-inv (n-·≲R {ρ₁ = (c ─ c₁) {nsr}} e) = ⊥-elim (noComplements nsr refl)
≲-inv (n-·≲R {ρ₁ = l ▹ₙ c} e) = ⊥-elim (noNeutrals l)
≲-inv (n-≲lift {ρ₁ = ⦅ xs ⦆ _} {⦅ ys ⦆ _} {F} e refl refl) rewrite 
  sym (stability-map F xs) | sym (stability-map F ys) = ⊆-map (overᵣ (F ·'_)) (≲-inv e) 

≲-inv (n-≲lift {ρ₁ = ne x₃} {ρ₂} c x₁ x₂) = ⊥-elim (noNeutrals x₃)
≲-inv (n-≲lift {ρ₁ = ⦅ ρ ⦆ oρ} {ne x₃} c x₁ x₂) = ⊥-elim (noNeutrals x₃)
≲-inv (n-≲lift {ρ₁ = ⦅ ρ ⦆ oρ} {(ρ₂ ─ ρ₃) {nsr}} c x₁ x₂) = ⊥-elim (noComplements nsr refl)
≲-inv (n-≲lift {ρ₁ = ⦅ ρ ⦆ oρ} {l ▹ₙ ρ₂} c x₁ x₂) = ⊥-elim (noNeutrals l)
≲-inv (n-≲lift {ρ₁ = (ρ₁ ─ ρ₃) {nsr}} {ρ₂} c x₁ x₂) = ⊥-elim (noComplements nsr refl)
≲-inv (n-≲lift {ρ₁ = l ▹ₙ ρ₁} {ρ₂} c x₁ x₂) = ⊥-elim (noNeutrals l)

·-inv (n-· ρ₁⊆ρ₃ ρ₂⊆ρ₃ ρ₃⊆) = ρ₁⊆ρ₃ , (ρ₂⊆ρ₃ , ρ₃⊆)
·-inv n-ε-R = ⊆-refl , (λ { x () }) , (λ x x∈ρ₁ → left x∈ρ₁)
·-inv n-ε-L = (λ { x () }) , ⊆-refl , (λ x x∈ → right x∈)
·-inv (n-·lift {ρ₁ = ⦅ x₃ ⦆ _} {⦅ x₄ ⦆ _} {⦅ x₅ ⦆ _} {F} e refl refl refl) with ·-inv e
... | i₁ , i₂ , i₃ rewrite 
    sym (stability-map F x₃) 
  | sym (stability-map F x₄)
  | sym (stability-map F x₅) =  ⊆-map (overᵣ (F ·'_)) i₁ , (⊆-map (overᵣ (F ·'_)) i₂) , ⊆-map-or (overᵣ (F ·'_)) i₃
·-inv (n-·lift {ρ₁ = ne x₄} {ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals x₄)
·-inv (n-·lift {ρ₁ = ⦅ ρ ⦆ oρ} {ne x₄} {_} en x₁ x₂ x₃) = ⊥-elim (noNeutrals x₄)
·-inv (n-·lift {ρ₁ = ⦅ ρ ⦆ oρ} {⦅ ρ₁ ⦆ oρ₁} {ne x₄} en x₁ x₂ x₃) = ⊥-elim (noNeutrals x₄)
·-inv (n-·lift {ρ₁ = ⦅ ρ ⦆ oρ} {⦅ ρ₁ ⦆ oρ₁} {(ρ₃ ─ ρ₄) {nsr}} en x₁ x₂ x₃) = ⊥-elim (noComplements nsr refl)
·-inv (n-·lift {ρ₁ = ⦅ ρ ⦆ oρ} {⦅ ρ₁ ⦆ oρ₁} {l ▹ₙ ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals l)
·-inv (n-·lift {ρ₁ = ⦅ ρ ⦆ oρ} {(ρ₂ ─ ρ₄) {nsr}} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noComplements nsr refl) 
·-inv (n-·lift {ρ₁ = ⦅ ρ ⦆ oρ} {l ▹ₙ ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals l)
·-inv (n-·lift {ρ₁ = (ρ₁ ─ ρ₄) {nsr}} {ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noComplements nsr refl) 
·-inv (n-·lift {ρ₁ = l ▹ₙ ρ₁} {ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals l)
·-inv (n-·complᵣ' en) with  ≲-inv en
·-inv {ρ₁ = ρ₁} {ρ₃ = ρ₃} (n-·complᵣ' en) | ih = ih , ⇓Row-⇑Row-─s-mono ρ₁ ρ₃ , ⇓Row-⇑Row-─s-mono-orᵣ ρ₁ ρ₃ ih
·-inv {ρ₁ = ρ₁} {ρ₂} {ρ₃} (n-·complₗ' en) with ≲-inv en 
... | ih = ⇓Row-⇑Row-─s-mono _ _ , ih , ⇓Row-⇑Row-─s-mono-orₗ ρ₂ ρ₃ ih



-- -- --------------------------------------------------------------------------------
-- -- NormalEntailment of inclusion is transitive

-- -- n-trans : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]} → 
-- --          NormalEnt Γ (ρ₁ ≲ ρ₂) → NormalEnt Γ (ρ₂ ≲ ρ₃) → NormalEnt Γ (ρ₁ ≲ ρ₃)
-- -- n-trans {ρ₁ = ρ₁} {ρ₂} {ρ₃} ρ₁≲ρ₂ ρ₂≲ρ₃ = {!ρ₁ ρ₂ ρ₃!}

-- -- --------------------------------------------------------------------------------
-- -- -- The sum of two labeled rows is not a labeled row

-- -- ·-impossible :  ∀ {l₁ l₂ l₃ : NormalType ∅ L} {τ₁ τ₂ τ₃ :  NormalType ∅ κ} → 
-- --                 NormalEnt ∅ ((l₁ ▹ τ₁) · (l₂ ▹ τ₂) ~ (l₃ ▹ τ₃)) → ⊥ 
-- -- ·-impossible  (n-·lift {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} e x x₁ x₂) = ·-impossible e

-- -- --------------------------------------------------------------------------------
-- -- -- If two rows combine to be the empty type then both are the empty row

-- ε-sum : NormalEnt ∅ (ρ₁ · ρ₂ ~ εNF) → ρ₁ ≡ εNF × ρ₂ ≡ εNF
-- ε-sum (n-· {xs = []} {[]} i₁ i₂ i₃) = refl , refl
-- ε-sum (n-· {xs = xs} {y ∷ ys} i₁ i₂ i₃) = ∈-elim (i₂ y (here refl))
-- ε-sum (n-· {xs = x ∷ xs} {ys} i₁ i₂ i₃) = ∈-elim (i₁ x (here refl))
-- ε-sum n-ε-R = refl , refl
-- ε-sum n-ε-L = refl , refl
-- ε-sum (n-·lift {ρ₁ = ρ₁} {ρ₂} {⦅ [] ⦆} {F = F} e eq₁ eq₂ eq₃) with ε-sum e 
-- ... | refl , refl = eq₁ , eq₂

-- -- --------------------------------------------------------------------------------
-- -- -- ε forms a least upper bound on rows

-- ε-minimum :  NormalEnt ∅ (ρ ≲ εNF) → ρ ≡ εNF
-- ε-minimum (n-≲ {xs = []} i) = refl
-- ε-minimum (n-≲ {xs = x ∷ xs} i) = ∈-elim (i x (here refl))
-- ε-minimum (n-≲lift {ρ₁ = ne x} _ _ _) = ⊥-elim (noNeutrals x)
-- ε-minimum (n-≲lift {ρ₁ = ⦅ xs ⦆} {⦅ [] ⦆} n refl refl) with ε-minimum n 
-- ... | refl = refl
-- ε-minimum (n-var ())
-- ε-minimum n-refl = refl
-- ε-minimum (n-trans e e₁) rewrite ε-minimum e₁ = ε-minimum e 
-- ε-minimum {ρ = ρ} (n-·≲L e) = fst (ε-sum e)
-- ε-minimum (n-·≲R e) = snd (ε-sum e)

-- -- --------------------------------------------------------------------------------
-- -- -- If two rows combine to be the empty type then both are the empty row

-- singleton-sum : NormalEnt ∅ (ρ₁ · ρ₂ ~ ⦅ [ τ ] ⦆) → ρ₁ ≡ ⦅ [ τ ] ⦆ or ρ₂ ≡ ⦅ [ τ ] ⦆
-- singleton-sum {τ = τ} (n-· {xs = []} {[]} i₁ i₂ i₃) = ∈-elim (absurd-left-elim (i₃ τ (here refl)))
-- singleton-sum {τ = τ} (n-· {xs = []} {y ∷ ys} i₁ i₂ i₃) = {!   !}
-- singleton-sum {τ = τ} (n-· {xs = x ∷ xs} {[]} i₁ i₂ i₃) = {!   !}
-- singleton-sum {τ = τ} (n-· {xs = x ∷ xs} {x₁ ∷ ys} i₁ i₂ i₃) = {!   !} 
-- singleton-sum n-ε-R = {!   !}
-- singleton-sum n-ε-L = {!   !}
-- singleton-sum (n-·lift e x x₁ x₂) = {!   !}

-- -- --------------------------------------------------------------------------------
-- -- -- ε is the *unique* right identity

-- -- ε-right-unique : NormalEnt ∅ (ρ₁ · ρ₂ ~ ρ₁) → ρ₂ ≡ ε
-- -- ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-R = refl
-- -- ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-L = refl
-- -- ε-right-unique {ρ₁ = ne x} {_} (n-·lift e _ _ _) = ⊥-elim (noNeutrals x)
-- -- ε-right-unique {ρ₁ = _} {ne x} (n-·lift e _ _ _ ) = ⊥-elim (noNeutrals x)
-- -- ε-right-unique {ρ₁ = ε} {ε} (n-·lift e x x₁ x₂) = refl
-- -- ε-right-unique {ρ₁ = ε} {l ▹ τ} (n-·lift {ρ₁ = ε} {ρ₂ = l' ▹ τ'} {ε} {F = `λ F} e x x₁ x₂) with ε-right-unique e
-- -- ... | () 
-- -- ε-right-unique {ρ₁ = ρ₁ ▹ ρ₂} {ε} (n-·lift e x x₁ x₂) = refl
-- -- ε-right-unique {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ ▹ ρ₃} {l₄ ▹ τ₄} e x x₁ x₂) = ⊥-elim (·-impossible e) 

-- -- --------------------------------------------------------------------------------
-- -- -- Reflection of combination equality to propositional equality

-- -- ε-right-identity : NormalEnt ∅ (ρ₁ · ε ~ ρ₂) → ρ₁ ≡ ρ₂
-- -- ε-left-identity : NormalEnt ∅ (ε · ρ₁ ~ ρ₂) → ρ₁ ≡ ρ₂

-- -- ε-right-identity n-ε-R = refl
-- -- ε-right-identity n-ε-L = refl
-- -- ε-right-identity (n-·lift {ρ₁ = ne x₃} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- -- ε-right-identity {ρ₁ = ε} {ρ₂ = ne x₃} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- -- ε-right-identity {ρ₁ = ε} {ρ₂ = ε} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = refl
-- -- ε-right-identity {ρ₁ = ε} {ρ₂ = ρ₂ ▹ ρ₄} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃ ▹ ρ₅} e x x₁ x₂) with ε-right-identity e
-- -- ... | () 
-- -- ε-right-identity {ρ₁ = ρ₁ ▹ ρ₂} {ne x₃} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- -- ε-right-identity {ρ₁ = l₁ ▹ τ₁} {ε} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) with trans (ε-right-identity e) (ε-<$>' (sym x₂))
-- -- ... | () 
-- -- ε-right-identity {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ = ε} {l₄ ▹ τ₄} {F} e x x₁ x₂) = 
-- --   trans x (trans (cong₂ _▹_ (inj-▹ₗ (ε-right-identity e)) (cong (F ·'_) (inj-▹ᵣ (ε-right-identity e)))) (sym x₂))


-- -- ε-left-identity n-ε-R = refl
-- -- ε-left-identity n-ε-L = refl
-- -- ε-left-identity (n-·lift {ρ₁ = ε} {ne x₃} {_} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- -- ε-left-identity (n-·lift {ρ₁ = ε} {_} {ne x₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
-- -- ε-left-identity (n-·lift {ρ₁ = ε} {ε} {ε} e x x₁ x₂) = trans x₁ (sym x₂)
-- -- ε-left-identity (n-·lift {ρ₁ = ε} {ε} {ρ₃ ▹ ρ₄} e x x₁ x₂) with  ε-left-identity e  
-- -- ... | () 
-- -- ε-left-identity (n-·lift {ρ₁ = ε} {ρ₂ ▹ ρ₃} {ε} e x x₁ x₂) with ε-left-identity e
-- -- ... | ()
-- -- ε-left-identity (n-·lift {ρ₁ = ε} {ρ₂ ▹ ρ₃} {ρ₄ ▹ ρ₅} {F} e x x₁ x₂) = 
-- --   trans 
-- --     x₁ 
-- --     (trans 
-- --       (cong₂ _▹_ 
-- --         (inj-▹ₗ (ε-left-identity e)) 
-- --         (cong (F ·'_) (inj-▹ᵣ (ε-left-identity e)))) 
-- --       (sym x₂)) 


-- -- --------------------------------------------------------------------------------
-- -- -- Reflection of labeled row reflexivity to propositional equality

-- -- ≲-refl :  ∀ {l₁ l₂ : NormalType ∅ L} {τ₁ τ₂ :  NormalType ∅ κ} → NormalEnt ∅ ((l₁ ▹ τ₁) ≲ (l₂ ▹ τ₂)) → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂)
-- -- ≲-refl (n-var ())
-- -- ≲-refl n-refl = refl
-- -- ≲-refl (n-trans {ρ₂ = ne x} e e₁) = ⊥-elim (noNeutrals x) 
-- -- ≲-refl (n-trans {ρ₂ = ε} e e₁) with ε-minimum e
-- -- ... | () 
-- -- ≲-refl (n-trans {ρ₂ = l₂ ▹ τ₂} e e₁) = trans (≲-refl e) (≲-refl e₁)
-- -- ≲-refl (n-·≲L {ρ₂ = ne x} e) = ⊥-elim (noNeutrals x)
-- -- ≲-refl (n-·≲L {ρ₂ = ε} e) = ε-right-identity e
-- -- ≲-refl (n-·≲L {ρ₂ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e)  
-- -- ≲-refl (n-·≲R {ρ₁ = ne x} e) = ⊥-elim (noNeutrals x)
-- -- ≲-refl (n-·≲R {ρ₁ = ε} e) = ε-left-identity e
-- -- ≲-refl (n-·≲R {ρ₁ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e) 
-- -- ≲-refl (n-≲lift {ρ₁ = l₃ ▹ τ₃} {l₄ ▹ τ₄} {F} e x x₁) = 
-- --   trans 
-- --     x 
-- --     (trans 
-- --       (cong₂ _▹_ 
-- --         (inj-▹ₗ (≲-refl e)) 
-- --         (cong (F ·'_) (inj-▹ᵣ (≲-refl e)))) 
-- --       (sym x₁))     
 
-- --  --------------------------------------------------------------------------------
-- -- -- Problems

-- -- no-meaningful-combinations : NormalEnt ∅ (ρ₁ · ρ₂ ~ ρ₃) → ρ₁ ≡ ε or ρ₂ ≡ ε 
-- -- no-meaningful-combinations {ρ₁ = ne x} {ρ₂} {ρ₃} e = ⊥-elim (noNeutrals x)
-- -- no-meaningful-combinations {ρ₁ = ρ₁} {ne x} {ρ₃} e = ⊥-elim (noNeutrals x)
-- -- no-meaningful-combinations {ρ₁ = ρ₁} {ρ₂} {ne x} e = ⊥-elim (noNeutrals x)
-- -- no-meaningful-combinations {ρ₁ = ε} {ρ₂} {ρ₃} e = left refl
-- -- no-meaningful-combinations {ρ₁ = ρ₁} {ε} {ρ₃} e = right refl
-- -- no-meaningful-combinations {ρ₁ = ρ₁ ▹ ρ₄} {ρ₂ ▹ ρ₅} {ε} e = left (ε-minimum (n-·≲L e))
-- -- no-meaningful-combinations {ρ₁ = ρ₁ ▹ ρ₄} {ρ₂ ▹ ρ₅} {ρ₃ ▹ ρ₆} e = ⊥-elim (·-impossible e)




