-- {-# OPTIONS --safe #-}
module Rome.Both.Terms.Entailment.Properties where

open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax

open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Properties.Substitution
open import Rome.Both.Types.Semantic.NBE

open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Stability

open import Rome.Both.Terms.Syntax
open import Rome.Both.Terms.GVars

open import Rome.Both.Containment

-- --------------------------------------------------------------------------------
-- Constructive reflexivity of row inclusion

≲-refl : ∀ {ρ₁ : SimpleRow (NormalType (∅ {ι∅}) κ)} →            
           {oρ₁ : True (normalOrdered? ρ₁)}  → 
         Ent ∅ ((⦅ ρ₁ ⦆ oρ₁) ≲ (⦅ ρ₁ ⦆ oρ₁))
≲-refl = n-incl (λ x x∈xs → x∈xs) 

--------------------------------------------------------------------------------
-- Entailments in empty contexts contain only simple rows.

norm-≲ : Ent ∅ (ρ₁ ≲ ρ₂) → 
        ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
        ∃[ ys ] Σ[ oys ∈ True (normalOrdered? ys) ] 
        (ρ₁ ≡ ⦅ xs ⦆ oxs × ρ₂ ≡ ⦅ ys ⦆ oys)

norm-· : Ent ∅ (ρ₁ · ρ₂ ~ ρ₃) → 
        ∃[ xs ] Σ[ oxs ∈ True (normalOrdered? xs) ] 
        ∃[ ys ] Σ[ oys ∈ True (normalOrdered? ys) ] 
        ∃[ zs ] Σ[ ozs ∈ True (normalOrdered? zs) ] 
        (ρ₁ ≡ ⦅ xs ⦆ oxs × ρ₂ ≡ ⦅ ys ⦆ oys × ρ₃ ≡ ⦅ zs ⦆ ozs)
norm-≲ {ρ₁ = φ <$> x} {ρ₂ = ρ₂} n = ⊥-elim (noNeutrals x)
norm-≲ {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = φ <$> x₁} n = ⊥-elim (noNeutrals x₁)
norm-≲ {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = (ρ₂ ─ ρ₃) {nsr}} n = ⊥-elim (noComplements nsr refl)
norm-≲ {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = l ▹ₙ ρ₂} n = ⊥-elim (noNeutrals l)
norm-≲ {ρ₁ = (ρ₁ ─ ρ₃) {nsr}} {ρ₂ = ρ₂} n = ⊥-elim (noComplements nsr refl)
norm-≲ {ρ₁ = l ▹ₙ ρ₁} {ρ₂ = ρ₂} n = ⊥-elim (noNeutrals l)
norm-≲ {ρ₁ = ⦅ xs ⦆ oxs} {ρ₂ = ⦅ ys ⦆ oys} n = xs , oxs , ys , oys , refl , refl


norm-· {ρ₁ = φ <$> x} {ρ₂ = ρ₂} {ρ₃ = ρ₃} n = ⊥-elim (noNeutrals x)
norm-· {ρ₁ = (ρ₁ ─ ρ₄) {nsr}} {ρ₂ = ρ₂} {ρ₃ = ρ₃} n = ⊥-elim (noComplements nsr refl)
norm-· {ρ₁ = l ▹ₙ ρ₁} {ρ₂ = ρ₂} {ρ₃ = ρ₃} n = ⊥-elim (noNeutrals l)
norm-· {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = φ <$> x₁} {ρ₃ = ρ₃} n = ⊥-elim (noNeutrals x₁)
norm-· {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = (ρ₂ ─ ρ₄) {nsr}} {ρ₃ = ρ₃} n = ⊥-elim (noComplements nsr refl)
norm-· {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = l ▹ₙ ρ₂} {ρ₃ = ρ₃} n =  ⊥-elim (noNeutrals l)
norm-· {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = ⦅ ρ₁ ⦆ oρ₁} {ρ₃ = φ <$> x₁} n = ⊥-elim (noNeutrals x₁)
norm-· {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = ⦅ ρ₁ ⦆ oρ₁} {ρ₃ = (ρ₃ ─ ρ₄) {nsr}} n = ⊥-elim (noComplements nsr refl)
norm-· {ρ₁ = ⦅ ρ ⦆ oρ} {ρ₂ = ⦅ ρ₁ ⦆ oρ₁} {ρ₃ = l ▹ₙ ρ₃} n = ⊥-elim (noNeutrals l)
norm-· {ρ₁ = ⦅ xs ⦆ oxs} {ρ₂ = ⦅ ys ⦆ oys} {ρ₃ = ⦅ zs ⦆ ozs} n = xs , oxs , ys , oys , zs , ozs , refl , refl , refl


-- --------------------------------------------------------------------------------
-- Inversion of inclusion for simple rows

≲-inv : ∀ {ρ₁ ρ₂ : SimpleRow (NormalType (∅ {ι∅}) κ)} → 
          {oρ₁ : True (normalOrdered? ρ₁)}
          {oρ₂ : True (normalOrdered? ρ₂)} → 
         Ent ∅ ((⦅ ρ₁ ⦆ oρ₁) ≲ (⦅ ρ₂ ⦆ oρ₂)) → ρ₁ ⊆ ρ₂

--------------------------------------------------------------------------------
-- Inversion of combination


·-inv :  ∀ {ρ₁ ρ₂ ρ₃ : SimpleRow (NormalType (∅ {ι∅}) κ)}
          {oρ₁ : True (normalOrdered? ρ₁)}
          {oρ₂ : True (normalOrdered? ρ₂)} 
          {oρ₃ : True (normalOrdered? ρ₃)} → 
         Ent ∅ (⦅ ρ₁ ⦆ oρ₁ · ⦅ ρ₂ ⦆ oρ₂ ~ ⦅ ρ₃ ⦆ oρ₃) → 
         ρ₁ ⊆ ρ₃ × 
         ρ₂ ⊆ ρ₃ × 
         (∀ x → x ∈ ρ₃ → x ∈ ρ₁ or x ∈ ρ₂)

--------------------------------------------------------------------------------
-- Lemmas about inclusion (needed to prove inversion for n-·compl rules)

⇓Row-mono : ∀ {ρ₁ ρ₂ : SimpleRow (Type Δ κ)} → 
              ρ₁ ⊆ ρ₂ → 
              ⇓Row ρ₁ ⊆ ⇓Row ρ₂ 
⇓Row-mono {ρ₁ = ρ₁} {ρ₂} = ⊆-cong _ ⇓Row (⇓Row-isMap idEnv)

─s-mono : ∀ {ρ₁ ρ₂ : SimpleRow (Type Δ κ)} → 
               (ρ₂ ─s ρ₁) ⊆ ρ₂ 
─s-mono {ρ₁ = ρ₁} {ρ₂ = []} = λ { i () }
─s-mono {ρ₁ = ρ₁} {ρ₂ = (l , τ) ∷ ρ₂} with l ∈L? ρ₁ 
... | yes p = λ { x i → there (─s-mono {ρ₁ = ρ₁} {ρ₂} x i)} 
... | no  q = λ { (.l , .τ) (here refl) → here refl ; x (there i) → there (─s-mono {ρ₁ = ρ₁} {ρ₂} x i) }

⇓Row-⇑Row-─s-mono : ∀ (ρ₁ ρ₂ : SimpleRow (NormalType Δ κ)) → 
       ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊆ ρ₂
⇓Row-⇑Row-─s-mono ρ₁ ρ₂ = 
  subst 
    (λ x → ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊆ x) 
    (stabilityRow ρ₂) 
    (⇓Row-mono (─s-mono {ρ₁ = ⇑Row ρ₁} {⇑Row ρ₂}))

open IsStrictPartialOrder (SPO) using (asym)

labelsIdentifyTypes : ∀ {ρ : SimpleRow (Type Δ κ)} → 
                 {oρ : Ordered ρ} → 
                 {l : Label} {τ τ' : Type Δ κ} → 
                 (l , τ) ∈ ρ → (l , τ') ∈ ρ → 
                 τ ≡ τ'
labelsIdentifyTypes {ρ = ρ} {oρ} {l} {τ} {τ'} (here refl) (here refl) = refl
labelsIdentifyTypes {ρ = ρ} {l<l , oxs} {l} (here refl) (there (here refl)) = ⊥-elim (asym {l} {l} l<l l<l)
labelsIdentifyTypes {ρ = (l , τ) ∷ (l₃ , τ₃) ∷ xs} {oρ} {l} {τ} {τ'} (here refl) (there (there {l₃ , τ₃} {xs} τ'∈ρ)) = 
  labelsIdentifyTypes {oρ = ordered-swap (oρ .fst) (oρ .snd)} (here refl) (there τ'∈ρ)
labelsIdentifyTypes {ρ = ρ} {l<l , oxs} {l} {τ} {τ'} (there (here refl)) (here refl) = ⊥-elim (asym {l} {l} l<l l<l)
labelsIdentifyTypes {ρ = ((l , τ') ∷ (l'' , τ'') ∷ xs)} {oρ} {l} {τ} {τ'} (there (there τ∈ρ)) (here refl) = 
  sym (labelsIdentifyTypes {oρ = ordered-swap (oρ .fst) (oρ .snd)} (here refl) (there τ∈ρ))  
labelsIdentifyTypes {ρ = (l₁ , τ₁) ∷ xs} {oρ} {l} {τ} {τ'} (there τ∈ρ) (there τ'∈ρ) = labelsIdentifyTypes {oρ = ordered-cons (l₁ , τ₁) xs oρ} τ∈ρ τ'∈ρ

∈L⇒∈ : ∀ {l : Label} {ρ : SimpleRow (Type Δ κ)} →  
        l ∈L ρ → Σ[ τ ∈ Type Δ κ ]((l , τ) ∈ ρ)
∈L⇒∈ (Here {τ = τ}) = τ , (here refl)
∈L⇒∈ (There Inn) = ∈L⇒∈ Inn .fst , there (∈L⇒∈ Inn .snd)

InComplement : ∀ {l : Label} {τ : Type Δ κ} {ρ₁ ρ₂ : SimpleRow (Type Δ κ)} →  
           ¬ (l ∈L ρ₁) → (l , τ) ∈ ρ₂ → (l , τ) ∈ (ρ₂ ─s ρ₁)
InComplement {l = l} {τ} {ρ₁} {ρ₂} ¬∈ρ₁ (here refl) with l ∈L? ρ₁
... | yes p = ⊥-elim (¬∈ρ₁ p)
... | no  q = here refl
InComplement {l = l} {τ} {ρ₁} {ρ₂} ¬∈ρ₁ (there {(l' , τ')} {xs} ∈ρ₂) with l' ∈L? ρ₁ 
... | yes p = InComplement ¬∈ρ₁ ∈ρ₂
... | no  q = there (InComplement ¬∈ρ₁ ∈ρ₂)

─s-mono-orᵣ : ∀ {ρ₁ ρ₂ : SimpleRow (Type Δ κ)}
               {oρ₂ : Ordered ρ₂} → 
               ρ₁ ⊆ ρ₂ → 
               ρ₂ ⊆[ ρ₁ ⊹ (ρ₂ ─s ρ₁) ]

─s-mono-orᵣ {ρ₁ = ρ₁} {ρ₂} i (l , τ) (here refl)           with l ∈L? ρ₁ 
─s-mono-orᵣ {ρ₁ = ρ₁} {ρ₂} i (l , τ) (here refl)    | yes p with ∈L⇒∈ p
─s-mono-orᵣ {ρ₁ = ρ₁} {(l , τ) ∷ ρ₂} {oρ₂ = oρ₂} i (l , τ) (here refl)    | yes p | τ' , τ'∈ 
  rewrite labelsIdentifyTypes {oρ = oρ₂} (here refl) (i (l , τ') τ'∈) = left τ'∈
─s-mono-orᵣ {ρ₁ = ρ₁} {ρ₂} i (l , τ) (here refl)    | no p with l ∈L? ρ₁ 
... | yes q = ⊥-elim (p q) 
... | no q = right (here refl)
─s-mono-orᵣ {ρ₁ = ρ₁} {(l₂ , τ₂) ∷ ρ₂} {oρ₂ = oρ₂} i (l , τ) (there w) with l ∈L? ρ₁ | l₂ ∈L? ρ₁ 
... | no  p | yes q  = right (InComplement p w)
... | no  p | no  q  = right (there (InComplement p w))
... | yes p | _ with ∈L⇒∈ p 
... | τ' , τ'∈ with labelsIdentifyTypes {oρ = oρ₂} (there w) (i (l , τ') τ'∈) 
... | refl = left τ'∈

─s-mono-orₗ : ∀ {ρ₁ ρ₂ : SimpleRow (Type Δ κ)} → 
                {oρ₂ : Ordered ρ₂} → 
               ρ₁ ⊆ ρ₂ → 
               ρ₂ ⊆[ (ρ₂ ─s ρ₁) ⊹ ρ₁ ]
─s-mono-orₗ {ρ₁ = ρ₁} {ρ₂} i (l , τ) (here refl)           with l ∈L? ρ₁ 
─s-mono-orₗ {ρ₁ = ρ₁} {ρ₂} i (l , τ) (here refl)    | yes p with ∈L⇒∈ p
─s-mono-orₗ {ρ₁ = ρ₁} {(l , τ) ∷ ρ₂} {oρ₂ = oρ₂} i (l , τ) (here refl)    | yes p | τ' , τ'∈ 
  rewrite labelsIdentifyTypes {oρ = oρ₂} (here refl) (i (l , τ') τ'∈) = right τ'∈
─s-mono-orₗ {ρ₁ = ρ₁} {ρ₂} i (l , τ) (here refl)    | no p with l ∈L? ρ₁ 
... | yes q = ⊥-elim (p q) 
... | no q = left (here refl)
─s-mono-orₗ {ρ₁ = ρ₁} {(l₂ , τ₂) ∷ ρ₂} {oρ₂ = oρ₂} i (l , τ) (there w) with l ∈L? ρ₁ | l₂ ∈L? ρ₁ 
... | no  p | yes q  = left (InComplement p w)
... | no  p | no  q  = left (there (InComplement p w))
... | yes p | _ with ∈L⇒∈ p 
... | τ' , τ'∈ with labelsIdentifyTypes {oρ = oρ₂} (there w) (i (l , τ') τ'∈) 
... | refl = right τ'∈

⇓Row-⇑Row-─s-mono-orᵣ : 
  ∀ (ρ₁ ρ₂ : SimpleRow (NormalType Δ κ)) → 
    {oρ₂ : NormalOrdered ρ₂} → 
    ρ₁ ⊆ ρ₂ → 
    ρ₂ ⊆[ ρ₁ ⊹ (⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁)) ]
⇓Row-⇑Row-─s-mono-orᵣ ρ₁ ρ₂ {oρ₂} i = 
  subst 
    (λ x → ρ₂ ⊆[ x ⊹ ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ])
    (stabilityRow ρ₁)
    (subst 
      (λ x → x ⊆[ ⇓Row (⇑Row ρ₁) ⊹ ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ]) 
      (stabilityRow ρ₂)
      (⊆-cong-or _ ⇓Row (⇓Row-isMap idEnv) 
        (─s-mono-orᵣ {ρ₁ = (⇑Row ρ₁)} {(⇑Row ρ₂)} {oρ₂ = Ordered⇑ ρ₂ oρ₂} (⊆-cong _ ⇑Row ⇑Row-isMap i))))

⇓Row-⇑Row-─s-mono-orₗ : 
  ∀ (ρ₁ ρ₂ : SimpleRow (NormalType Δ κ)) →
    {oρ₂ : NormalOrdered ρ₂} → 
    ρ₁ ⊆ ρ₂ → 
    ρ₂ ⊆[ (⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁)) ⊹ ρ₁ ]
⇓Row-⇑Row-─s-mono-orₗ ρ₁ ρ₂ {oρ₂} i =
  subst 
    (λ x → ρ₂ ⊆[ ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊹ x ])
    (stabilityRow ρ₁)
    (subst 
      (λ x → x ⊆[  ⇓Row (⇑Row ρ₂ ─s ⇑Row ρ₁) ⊹ ⇓Row (⇑Row ρ₁) ]) 
      (stabilityRow ρ₂)
      ((⊆-cong-or _ ⇓Row (⇓Row-isMap idEnv) (─s-mono-orₗ {ρ₁ = (⇑Row ρ₁)} {(⇑Row ρ₂)} {oρ₂ = Ordered⇑ ρ₂ oρ₂} (⊆-cong _ ⇑Row ⇑Row-isMap i)))))

-- --------------------------------------------------------------------------------
-- Definitions

≲-inv (n-incl i) = i
≲-inv n-refl = λ x x∈xs → x∈xs 
≲-inv (_n-⨾_ {ρ₂ = φ <$> x} e₁ e₂) = ⊥-elim (noNeutrals x)
≲-inv (_n-⨾_ {ρ₂ = ⦅ ρ₂ ⦆ _} e₁ e₂) = ⊆-trans (≲-inv e₁) (≲-inv e₂)
≲-inv (_n-⨾_ {ρ₂ = ρ₂@((ρ ─ ρ') {nsr})} e₁ e₂) = ⊥-elim (noComplements nsr refl)
≲-inv (_n-⨾_ {ρ₂ = l ▹ₙ c} e₁ e₂) = ⊥-elim (noNeutrals l) 
≲-inv (n-plusL≲ {ρ₂ = φ <$> x} e) = ⊥-elim (noNeutrals x)
≲-inv (n-plusL≲ {ρ₂ = (c ─ c₁) {nsr}} e) = ⊥-elim (noComplements nsr refl)
≲-inv (n-plusL≲ {ρ₂ = l ▹ₙ c} e) = ⊥-elim (noNeutrals l)
≲-inv (n-plusL≲ {ρ₂ = ⦅ ρ₂ ⦆ _} e) with ·-inv e 
... | (i₁ , i₂ , i₃) = i₁
≲-inv (n-plusR≲ {ρ₁ = φ <$> x} e) = ⊥-elim (noNeutrals x)
≲-inv (n-plusR≲ {ρ₁ = ⦅ ρ₂ ⦆ _} e) with ·-inv e 
... | (i₁ , i₂ , i₃) = i₂
≲-inv (n-plusR≲ {ρ₁ = (c ─ c₁) {nsr}} e) = ⊥-elim (noComplements nsr refl)
≲-inv (n-plusR≲ {ρ₁ = l ▹ₙ c} e) = ⊥-elim (noNeutrals l)
≲-inv (n-map≲ {ρ₁ = ⦅ xs ⦆ _} {⦅ ys ⦆ _} {F} e refl refl) rewrite 
  sym (stability-map F xs) | sym (stability-map F ys) = ⊆-map (map₂ (F ·'_)) (≲-inv e) 

≲-inv (n-map≲ {ρ₁ = φ <$> x₃} {ρ₂} c x₁ x₂) = ⊥-elim (noNeutrals x₃)
≲-inv (n-map≲ {ρ₁ = ⦅ ρ ⦆ oρ} {φ <$> x₃} c x₁ x₂) = ⊥-elim (noNeutrals x₃)
≲-inv (n-map≲ {ρ₁ = ⦅ ρ ⦆ oρ} {(ρ₂ ─ ρ₃) {nsr}} c x₁ x₂) = ⊥-elim (noComplements nsr refl)
≲-inv (n-map≲ {ρ₁ = ⦅ ρ ⦆ oρ} {l ▹ₙ ρ₂} c x₁ x₂) = ⊥-elim (noNeutrals l)
≲-inv (n-map≲ {ρ₁ = (ρ₁ ─ ρ₃) {nsr}} {ρ₂} c x₁ x₂) = ⊥-elim (noComplements nsr refl)
≲-inv (n-map≲ {ρ₁ = l ▹ₙ ρ₁} {ρ₂} c x₁ x₂) = ⊥-elim (noNeutrals l)

·-inv (n-plus ρ₁⊆ρ₃ ρ₂⊆ρ₃ ρ₃⊆) = ρ₁⊆ρ₃ , (ρ₂⊆ρ₃ , ρ₃⊆)
·-inv n-emptyR = ⊆-refl , (λ { x () }) , (λ x x∈ρ₁ → left x∈ρ₁)
·-inv n-emptyL = (λ { x () }) , ⊆-refl , (λ x x∈ → right x∈)
·-inv (n-map· {ρ₁ = ⦅ x₃ ⦆ _} {⦅ x₄ ⦆ _} {⦅ x₅ ⦆ _} {F} e refl refl refl) with ·-inv e
... | i₁ , i₂ , i₃ rewrite 
    sym (stability-map F x₃) 
  | sym (stability-map F x₄)
  | sym (stability-map F x₅) =  ⊆-map (map₂ (F ·'_)) i₁ , (⊆-map (map₂ (F ·'_)) i₂) , ⊆-map-or (map₂ (F ·'_)) i₃
·-inv (n-map· {ρ₁ = φ <$> x₄} {ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals x₄)
·-inv (n-map· {ρ₁ = ⦅ ρ ⦆ oρ} {φ <$> x₄} {_} en x₁ x₂ x₃) = ⊥-elim (noNeutrals x₄)
·-inv (n-map· {ρ₁ = ⦅ ρ ⦆ oρ} {⦅ ρ₁ ⦆ oρ₁} {φ <$> x₄} en x₁ x₂ x₃) = ⊥-elim (noNeutrals x₄)
·-inv (n-map· {ρ₁ = ⦅ ρ ⦆ oρ} {⦅ ρ₁ ⦆ oρ₁} {(ρ₃ ─ ρ₄) {nsr}} en x₁ x₂ x₃) = ⊥-elim (noComplements nsr refl)
·-inv (n-map· {ρ₁ = ⦅ ρ ⦆ oρ} {⦅ ρ₁ ⦆ oρ₁} {l ▹ₙ ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals l)
·-inv (n-map· {ρ₁ = ⦅ ρ ⦆ oρ} {(ρ₂ ─ ρ₄) {nsr}} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noComplements nsr refl) 
·-inv (n-map· {ρ₁ = ⦅ ρ ⦆ oρ} {l ▹ₙ ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals l)
·-inv (n-map· {ρ₁ = (ρ₁ ─ ρ₄) {nsr}} {ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noComplements nsr refl) 
·-inv (n-map· {ρ₁ = l ▹ₙ ρ₁} {ρ₂} {ρ₃} en x₁ x₂ x₃) = ⊥-elim (noNeutrals l)
·-inv (n-complR en) with  ≲-inv en
·-inv {ρ₁ = ρ₁} {ρ₃ = ρ₃} {oρ₃ = oρ₃} (n-complR en) | ih = ih , ⇓Row-⇑Row-─s-mono ρ₁ ρ₃ , ⇓Row-⇑Row-─s-mono-orᵣ ρ₁ ρ₃ {oρ₂ = toWitness oρ₃} ih
·-inv {ρ₁ = ρ₁} {ρ₂} {ρ₃} {oρ₃ = oρ₃} (n-complL en) with ≲-inv en 
... | ih = ⇓Row-⇑Row-─s-mono _ _ , ih , ⇓Row-⇑Row-─s-mono-orₗ ρ₂ ρ₃ {oρ₂ = toWitness oρ₃} ih
