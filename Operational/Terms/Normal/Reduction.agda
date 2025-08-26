{-# OPTIONS --safe #-}
module Rome.Operational.Terms.Normal.Reduction where

open import Rome.Operational.Prelude
open import Rome.Operational.Containment

open import Rome.Operational.Kinds.Syntax


open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Entailment.Properties
open import Rome.Operational.Terms.Normal.Substitution

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.Normal.GVars
open import Rome.Operational.Terms.Normal.SynAna

--------------------------------------------------------------------------------
-- Defining projection

data _∈ᵣ_ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ] } → (l : Label × NormalTerm Γ τ) → Record Γ xs → Set where
  Here : ∀ {l} {τ : NormalType Δ ★} {xs : SimpleRow NormalType Δ R[ ★ ]} {M : NormalTerm Γ τ} → 
           {rxs : Record Γ xs} → 
           (l , M) ∈ᵣ (l ▹ M ⨾ rxs)

  There : ∀ {l l'} {τ υ : NormalType Δ ★} 
            {xs : SimpleRow NormalType Δ R[ ★ ]} {M : NormalTerm Γ τ} {M' : NormalTerm Γ υ} → 
            {rxs : Record Γ xs} → 

           (l , M) ∈ᵣ rxs → (l , M) ∈ᵣ (l' ▹ M' ⨾ rxs)

get : ∀ {l : Label} {xs : SimpleRow NormalType Δ R[ ★ ]} (rxs : Record Γ xs) → 
      (l , τ) ∈ xs → 
      ∃[ M ] (_∈ᵣ_ {τ = τ} (l , M) rxs)
get ∅ ()
get {τ = τ} {l = l} {xs} (l ▹ M ⨾ rxs) (here refl) = M , Here
get (l ▹ M ⨾ rxs) (there i) with get rxs i 
... | M' , loc = M' , There loc

project :  ∀ {xs ys : SimpleRow NormalType Δ R[ ★ ]} → 
            {oxs : True (normalOrdered? xs)} {oys : True (normalOrdered? ys)} →
            (rys : Record Γ ys) → 
            xs ⊆ ys →
            Record Γ xs 
project {xs = []} rys i = ∅
project {xs = (l , τ) ∷ xs} {ys} {oxs} {oys} rys i with get rys (i (l , τ) (here refl))
... | M , M∈rys = 
  l ▹ M ⨾  project 
             {oxs = fromWitness (normalOrdered-tail (l , τ) xs (toWitness oxs))} 
             {oys} rys 
             (truncate-⊆ i)

concatRec : ∀ {xs ys zs : SimpleRow NormalType Δ R[ ★ ]} → 
            (rxs : Record Γ xs) → 
            (rys : Record Γ ys) → 
            zs ⊆[ xs ⊹ ys ] → 
            Record Γ zs 
concatRec {zs = []} rxs rys i₃ = ∅
concatRec {zs = (l , τ) ∷ zs} rxs rys i₃ with i₃ (l , τ) (here refl) 
... | left inxs  = l ▹ (get rxs inxs .fst) ⨾ concatRec rxs rys (truncate-⊆-or i₃) 
... | right inys = l ▹ (get rys inys .fst) ⨾ concatRec rxs rys (truncate-⊆-or i₃) 

--------------------------------------------------------------------------------
-- Reduction of entailments in an empty context

infixr 0 _=⇒_
data _=⇒_ : ∀ {π : NormalPred Δ R[ κ ]} → Ent Γ π → Ent Γ π → Set where
  
  ξ-⨾₁ : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               {M M' : Ent Γ (ρ₁ ≲ ρ₂)}
               {N : Ent Γ (ρ₂ ≲ ρ₃)} → 

             M =⇒ M' →
             ------------
              (_n-⨾_ M N) =⇒ (_n-⨾_ M' N)

  ξ-⨾₂ : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               {M : Ent Γ (ρ₁ ≲ ρ₂)}
               {N N' : Ent Γ (ρ₂ ≲ ρ₃)} → 

             N =⇒ N' →
             ------------
              (_n-⨾_ M N) =⇒ (_n-⨾_ M N')

  ξ-plusL≲ : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
            {M M' : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)} →

            M =⇒ M' →
            -----------
            n-plusL≲ M =⇒ n-plusL≲ M'

  ξ-plusR≲ : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
            {M M' : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)} →

            M =⇒ M' →
            -----------
            n-plusR≲ M =⇒ n-plusR≲ M'
        


  ξ-map≲ : ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             (N N' : Ent Γ (ρ₁ ≲ ρ₂)) →
             {x y : NormalType Δ R[ κ₂ ]} → 
             (eq₁ : x ≡ (F <$>' ρ₁)) → 
             (eq₂ : y ≡ F <$>' ρ₂) → 
             
            N =⇒ N' → 
            ------------------------------------------
             n-map≲ {F = F} N eq₁ eq₂ =⇒ n-map≲ {F = F} N' eq₁ eq₂


  ξ-map· : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             (N N' : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) →
             {x y  z : NormalType Δ R[ κ₂ ]} → 
             (eq₁ : x ≡ (F <$>' ρ₁)) → 
             (eq₂ : y ≡ F <$>' ρ₂) → 
             (eq₃ : z ≡ F <$>' ρ₃) → 
             
            N =⇒ N' → 
            ------------------------------------------
             n-map· {F = F} N eq₁ eq₂ eq₃ =⇒ n-map· {F = F} N' eq₁ eq₂ eq₃


  ξ-complR : ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]}
              {oxs : True (normalOrdered? xs)} 
              {oys : True (normalOrdered? ys)}
              {ozs : True (normalOrdered? (⇓Row (⇑Row ys ∖s ⇑Row xs)))} → 
             (N N' : Ent Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys)) →

            N =⇒ N' → 
            ------------------------------------------
             n-complR {ozs = ozs} N =⇒ n-complR N'

  ξ-complL : ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]}
              {oxs : True (normalOrdered? xs)} 
              {oys : True (normalOrdered? ys)}
              {ozs : True (normalOrdered? (⇓Row (⇑Row ys ∖s ⇑Row xs)))} → 
             (N N' : Ent Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys)) →

            N =⇒ N' → 
            ------------------------------------------
             n-complL {ozs = ozs} N =⇒ n-complL N'
     
  ------------------------------------------------------------
  -- Computational rules

  δ-refl : ∀ (xs : SimpleRow NormalType Δ R[ κ ]) (oxs : True (normalOrdered? xs)) → 

         ----------------------------------------------------------
         _=⇒_ {Γ = Γ} (n-refl {ρ₁ = ⦅ xs ⦆ oxs}) (n-incl (λ _ i → i))
  δ-emptyR : ∀ {xs : SimpleRow NormalType Δ R[ κ ]} {oxs : True (normalOrdered? xs)} → 

           n-emptyR =⇒ n-plus {Γ = Γ} {xs = xs} {oxs = oxs} (λ _ i → i) (λ x ()) (λ _ i → left i)

  δ-emptyL : ∀ {ys : SimpleRow NormalType Δ R[ κ ]} {oys : True (normalOrdered? ys)} → 

           n-emptyL =⇒ n-plus {Γ = Γ} {ys = ys} {oys = oys} (λ x ()) (λ _ i → i) (λ _ i → right i)

  δ-⨾ : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]}
              {oxs : True (normalOrdered? xs)} 
              {oys : True (normalOrdered? ys)} 
              {ozs : True (normalOrdered? zs)} →
              (i₁ : xs ⊆ ys) → (i₂ : ys ⊆ zs) → 
              -----------------------------------------------------------------------------
              _n-⨾_ (n-incl {Γ = Γ} {oxs = oxs} {oys = oys} i₁) (n-incl {oys = ozs} i₂) =⇒ n-incl (⊆-trans i₁ i₂)

  δ-plusL≲ : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)} 
            {ozs : True (normalOrdered? zs)} →
            (i₁ : xs ⊆ zs) → (i₂ : ys ⊆ zs) → 
            (i₃ : zs ⊆[ xs ⊹ ys ]) → 

            -------------------------------
            n-plusL≲ (n-plus {Γ = Γ} {oxs = oxs} {oys} {ozs} i₁ i₂ i₃) =⇒ n-incl i₁

  δ-plusR≲ : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)} 
            {ozs : True (normalOrdered? zs)} →
            (i₁ : xs ⊆ zs) → (i₂ : ys ⊆ zs) → 
            (i₃ : zs ⊆[ xs ⊹ ys ]) → 

            -------------------------------
            n-plusR≲ (n-plus {Γ = Γ} {oxs = oxs} {oys} {ozs} i₁ i₂ i₃) =⇒ n-incl i₂

  δ-map≲ : ∀ {xs ys : SimpleRow NormalType Δ R[ κ₁ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)}
            {F : NormalType Δ (κ₁ `→ κ₂)} → 
            (i : xs ⊆ ys) → 
            
            
            ------------------------------
            n-map≲ {F = F} (n-incl {Γ = Γ} {oxs = oxs} {oys} i) refl refl  =⇒ 
            n-incl (⊆-cong _ _ (sym ∘ stability-map F) i)

  δ-map· : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ₁ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)}
            {ozs : True (normalOrdered? zs)}
            {F : NormalType Δ (κ₁ `→ κ₂)} → 
            (i₁ : xs ⊆ zs) (i₂ : ys ⊆ zs) (i₃ : zs ⊆[ xs ⊹ ys ]) → 
            
            
            ------------------------------
            n-map· {F = F} (n-plus {Γ = Γ} {oxs = oxs} {oys} {ozs} i₁ i₂ i₃) refl refl refl  =⇒ 
            n-plus 
              (⊆-cong _ _ (sym ∘ stability-map F) i₁) 
              (⊆-cong _ _ (sym ∘ stability-map F) i₂) 
              (⊆-cong-or _ _ (sym ∘ stability-map F) i₃)

  δ-complR :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ₁ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)}
            {ozs : True (normalOrdered? (⇓Row (⇑Row ys ∖s ⇑Row xs)))}
            (i : xs ⊆ ys) → 

            -----------------------------------------------------------------------------------------
            n-complR {Γ = Γ} {ozs = ozs} (n-incl {oxs = oxs} {oys} i) =⇒ 
            n-plus 
              i 
              (⇓Row-⇑Row-∖s-mono xs ys) 
              (⇓Row-⇑Row-∖s-mono-orᵣ xs ys {toWitness oys} i)
    

  δ-complL :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ₁ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)}
            {ozs : True (normalOrdered? (⇓Row (⇑Row ys ∖s ⇑Row xs)))}
            (i : xs ⊆ ys) → 

            -----------------------------------------------------------------------------------------
            n-complL {Γ = Γ} {ozs = ozs} (n-incl {oxs = oxs} {oys} i) =⇒ 
            n-plus 
              (⇓Row-⇑Row-∖s-mono xs ys) 
              i
              (⇓Row-⇑Row-∖s-mono-orₗ xs ys {toWitness oys} i)

--------------------------------------------------------------------------------
-- Small step semantics.

infixr 0 _—→_ _—→ᵣ_

data _—→_ : ∀ {τ} → NormalTerm Γ τ → NormalTerm Γ τ → Set
data _—→ᵣ_ : ∀ {xs} → Record Γ xs → Record Γ xs → Set where

  ξ-record₁ : ∀ {l} {xs} {M : NormalTerm Γ τ} {r r' : Record Γ xs} → 

              
           r —→ᵣ r' → 
           ------------------------------
           (l ▹ M ⨾ r) —→ᵣ (l ▹ M ⨾ r') 
  
  ξ-record₂ : ∀ {l} {xs} {M M' : NormalTerm Γ τ} {r : Record Γ xs} → 

           (M —→ M') → 
           ------------------------------
           (l ▹ M ⨾ r) —→ᵣ (l ▹ M' ⨾ r) 

data _—→_ where
  -- congruence rules
  ξ-·1 : ∀ {M₁ M₂ : NormalTerm Γ (τ₁ `→ τ₂)} {N : NormalTerm Γ τ₁} →
           M₁ —→ M₂ →
           -----------------
           M₁ · N —→ M₂ · N

  ξ-·2 : ∀ {M : NormalTerm Γ (τ₁ `→ τ₂)} {N₁ N₂ : NormalTerm Γ τ₁} →
           N₁ —→ N₂ →
           -----------------
           M · N₁ —→ M · N₂

  ξ-·[] : ∀ {τ'} {M₁ M₂ : NormalTerm Γ (`∀ τ)} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·[ τ' ] —→ M₂ ·[ τ' ]

  ξ-·⟨⟩ : ∀ {M₁ M₂ : NormalTerm Γ (π ⇒ τ)} {e : Ent Γ π} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·⟨ e ⟩ —→ M₂ ·⟨ e ⟩

  ξ-Out : ∀ {F} {M₁ M₂ : NormalTerm Γ (μ F)} →
               M₁ —→ M₂ →
               -----------------------
               Out F M₁ —→ Out F M₂

  ξ-In : ∀ {F} {M₁ M₂ : NormalTerm Γ (F ·' (μ F))} →
             M₁ —→ M₂ →
             -----------------------
             In F M₁ —→ In F M₂

  ξ-Π▹₁ : ∀ {l : Label}
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (ℓ₁ Π▹ M) —→ (ℓ₂ Π▹ M)

  ξ-Σ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ]} {oxs : True (normalOrdered? xs)}
             {l : Label} (M₁ M₂ : NormalTerm Γ τ) (i : (l , τ) ∈ xs) → 

        M₁ —→ M₂ → 
        ------------------------------------
        ⟨_▹_⟩via_ {xs = xs} {oxs} l M₁ i —→ ⟨ l ▹ M₂ ⟩via i

  ξ-Π/₁ : ∀  {l : Label}
            (M₁ M₂ : NormalTerm Γ (Π (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Π/ ℓ) —→ (M₂ Π/ ℓ)        

  ξ-Π/₂ : ∀  {l : Label}
            (M : NormalTerm Γ (Π (l ▹' τ))) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (M Π/ ℓ₁) —→ (M Π/ ℓ₂)        

  ξ-Σ▹₁ : ∀ {l : Label}
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (ℓ₁ Σ▹ M) —→ (ℓ₂ Σ▹ M)

  ξ-Σ/₁ : ∀  {l : Label}
            (M₁ M₂ : NormalTerm Γ (Σ (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Σ/ ℓ) —→ (M₂ Σ/ ℓ)        

  ξ-Σ/₂ : ∀  {l : Label}
            (M : NormalTerm Γ (Σ (l ▹' τ))) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (M Σ/ ℓ₁) —→ (M Σ/ ℓ₂)           

  ξ-prj : ∀ 
            (M₁ M₂ : NormalTerm Γ (Π ρ₂)) (e : Ent Γ (ρ₁ ≲ ρ₂)) → 

            M₁ —→ M₂ → 
            ------------ 
            prj M₁ e —→ prj M₂ e

  ξ-prj⇒ : ∀ 
            (M : NormalTerm Γ (Π ρ₂)) (e₁ e₂ : Ent Γ (ρ₁ ≲ ρ₂)) → 

            e₁ =⇒ e₂ → 
            ------------ 
            prj M e₁ —→ prj M e₂

  ξ-inj : ∀ 
            (M₁ M₂ : NormalTerm Γ (Σ ρ₁)) (e : Ent Γ (ρ₁ ≲ ρ₂)) → 

            M₁ —→ M₂ → 
            ------------ 
            inj M₁ e —→ inj M₂ e

  ξ-inj⇒ : ∀ 
            (M : NormalTerm Γ (Σ ρ₁)) (e₁ e₂ : Ent Γ (ρ₁ ≲ ρ₂)) → 

            e₁ =⇒ e₂ → 
            ------------ 
            inj M e₁ —→ inj M e₂

  ξ-⊹₁ : ∀
         (M₁ M₂ : NormalTerm Γ (Π ρ₁)) (N : NormalTerm Γ (Π ρ₂)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
         (M₁ —→ M₂) → 
         (M₁ ⊹ N) e —→ (M₂ ⊹ N) e

  ξ-⊹₂ : ∀
         (M : NormalTerm Γ (Π ρ₁)) (N₁ N₂ : NormalTerm Γ (Π ρ₂)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (N₁ —→ N₂) → 
       (M ⊹ N₁) e —→ (M ⊹ N₂) e

  ξ-⊹₃ : ∀
         (M : NormalTerm Γ (Π ρ₁)) (N : NormalTerm Γ (Π ρ₂)) 
         (e₁ e₂ : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (e₁ =⇒ e₂) → 
       (M ⊹ N) e₁ —→ (M ⊹ N) e₂

  ξ-▿₁ : ∀
         (M₁ M₂ : NormalTerm Γ (Σ ρ₁ `→ τ)) (N : NormalTerm Γ (Σ ρ₂ `→ τ)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (M₁ —→ M₂) → 
       (M₁ ▿ N) e —→ (M₂ ▿ N) e

  ξ-▿₂ : ∀
         (M : NormalTerm Γ (Σ ρ₁ `→ τ)) (N₁ N₂ : NormalTerm Γ (Σ ρ₂ `→ τ)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (N₁ —→ N₂) → 
       (M ▿ N₁) e —→ (M ▿ N₂) e

  ξ-▿₃ : ∀
         (M : NormalTerm Γ (Σ ρ₁ `→ τ)) (N : NormalTerm Γ (Σ ρ₂ `→ τ)) 
         (e₁ e₂ : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
         (e₁ =⇒ e₂) → 
         (M ▿ N) e₁ —→ (M ▿ N) e₂

  ξ-Syn : (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) → (M₁ M₂ : NormalTerm Γ (SynT' ρ φ)) →
          M₁ —→ M₂ → 
          ------------
          syn ρ φ M₁ —→ syn ρ φ M₂

  ξ-Ana : (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) → 
          (τ : NormalType Δ ★) → 
          {τ₁ τ₂ : NormalType Δ ★} → 
          (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁)
          (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂)
          (M₁ M₂ : NormalTerm Γ τ₁) →
          M₁ —→ M₂ → 
          ------------
          ana ρ φ τ eq₁ eq₂ M₁ —→ ana ρ φ τ eq₁ eq₂ M₂  


  ξ-⟨⟩ : ∀  {xs} {oxs : True (normalOrdered? xs)} {r r' : Record Γ xs} → 

              
           r —→ᵣ r' → 
           ------------------------------
           (⟨_⟩ {oxs = oxs} r) —→ ⟨ r' ⟩

  ----------------------------------------
  -- computational rules

  β-λ : ∀ {M : NormalTerm (Γ , τ₁) τ₂} {N : NormalTerm Γ τ₁} →
          
          -----------------------
          (`λ M) · N —→ M β[ N ]

  β-Λ : ∀ {τ₁ τ₂} {M : NormalTerm (Γ ,, κ) τ₂}  →

          --------------------------
          Λ M ·[ τ₁ ] —→ M β·[ τ₁ ]

  β-ƛ : ∀ {M : NormalTerm (Γ ,,, π) τ} {e : Ent Γ π} →
          
          -----------------------
          (`ƛ M) ·⟨ e ⟩ —→ (M βπ[ e ])

  δ-In : ∀ {F} {M : NormalTerm Γ (F ·' μ F)} →

             -------------------------
             Out F (In F M) —→ M

  δ-fix : ∀ (M : NormalTerm Γ (τ `→ τ)) → 

          -------------
          fix M —→ M · (fix M)

  δ-Π▹ : ∀ {l : Label} → 
           (M : NormalTerm Γ τ) →
           ((# (lab l)) Π▹ M) —→ (⟨ (l ▹ M ⨾ ∅) ⟩)

  δ-Σ▹ : ∀ {l : Label} → 
           (M : NormalTerm Γ τ) →
           ((# (lab l)) Σ▹ M) —→ (⟨ l ▹ M ⟩via (here refl))

  δ-Π/ : ∀ {l : Label} (M : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋) → 

        ---------------------------
        (⟨ l ▹ M ⨾ ∅ ⟩ Π/ ℓ) —→ M

  δ-Σ/ : ∀ {l : Label} (M : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋) → 

        ---------------------------
        ((⟨ l ▹ M ⟩via (here refl)) Σ/ ℓ) —→ M

  δ-prj : ∀ {xs ys : SimpleRow NormalType Δ R[ ★ ]} → 
            {oxs : True (normalOrdered? xs)} {oys : True (normalOrdered? ys)} →
            (rys : Record Γ ys) → 
            (i : xs ⊆ ys) → 
            ---------------------------
            (prj (⟨_⟩ {oxs = oys} rys) (n-incl {oxs = oxs} i) ) —→ ⟨ project {oxs = oxs} {oys = oys} rys i ⟩ 

  δ-inj : ∀ {xs ys : SimpleRow NormalType Δ R[ ★ ]} → 
            {oxs : True (normalOrdered? xs)} {oys : True (normalOrdered? ys)} →
            (l : Label) (M : NormalTerm Γ τ) → 
            (i : xs ⊆ ys)
            (h : (l , τ) ∈ xs) → 
            ---------------------------
            inj (⟨ l ▹ M ⟩via h) (n-incl {oxs = oxs} {oys} i) —→ ⟨ l ▹ M ⟩via (i (l , τ) h)


  δ-⊹ : ∀ {xs ys zs : SimpleRow NormalType Δ R[ ★ ]} → 
          {oxs : True (normalOrdered? xs)} 
          {oys : True (normalOrdered? ys)}
          {ozs : True (normalOrdered? zs)} →
          (r₁ : Record Γ xs) (r₂ : Record Γ ys) → 
          (i₁ : xs ⊆ zs) 
          (i₂ : ys ⊆ zs) 
          (i₃ : zs ⊆[ xs ⊹ ys ]) → 


        ---------------------------------------------
        (⟨ r₁ ⟩ ⊹ ⟨ r₂ ⟩) (n-plus {oxs = oxs} {oys = oys} {ozs} i₁ i₂ i₃) —→ ⟨ concatRec r₁ r₂ i₃ ⟩ 

  δ-▿₁ : ∀ {xs ys zs : SimpleRow NormalType Δ R[ ★ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)} 
            {ozs : True (normalOrdered? zs)}
            (F : NormalTerm Γ  (Σ (⦅ xs ⦆ oxs) `→ τ'))
            (G : NormalTerm Γ (Σ (⦅ ys ⦆ oys) `→ τ'))
            (e : Ent Γ (⦅ xs ⦆ oxs · ⦅ ys ⦆ oys ~ ⦅ zs ⦆ ozs))
            {l : Label}
            (M : NormalTerm Γ τ) 
            (i₁ : (l , τ) ∈ zs) → 
            (i₂ : (l , τ) ∈ xs) → 

           -------------------------------------------------
           ((F ▿ G) e) · (⟨ l ▹ M ⟩via i₁) —→ F · (⟨ l ▹ M ⟩via i₂)

  δ-▿₂ : ∀ {xs ys zs : SimpleRow NormalType Δ R[ ★ ]}
            {oxs : True (normalOrdered? xs)} 
            {oys : True (normalOrdered? ys)} 
            {ozs : True (normalOrdered? zs)}
            (F : NormalTerm Γ  (Σ (⦅ xs ⦆ oxs) `→ τ'))
            (G : NormalTerm Γ (Σ (⦅ ys ⦆ oys) `→ τ'))
            (e : Ent Γ (⦅ xs ⦆ oxs · ⦅ ys ⦆ oys ~ ⦅ zs ⦆ ozs))
            {l : Label}
            (M : NormalTerm Γ τ) 
            (i₁ : (l , τ) ∈ zs) → 
            (i₂ : (l , τ) ∈ ys) → 

           -------------------------------------------------
           ((F ▿ G) e) · (⟨ l ▹ M ⟩via i₁) —→ G · (⟨ l ▹ M ⟩via i₂)

  δ-ana : ∀ {xs : SimpleRow NormalType ∅ R[ κ ]} 
            {oxs : True (normalOrdered? xs)}
            (φ : NormalType ∅ (κ `→ ★))
            {oxs' : True (normalOrdered? (map (map₂ (φ ·'_)) xs))}
            (τ φυ : NormalType ∅ ★) 
            (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ (⦅ xs ⦆ oxs)))) ≡ Σ (⦅ map (map₂ (φ ·'_)) xs ⦆ oxs'))
            (M : NormalTerm ∅ (AnaT' (⦅ xs ⦆ oxs) φ τ)) 
            (l : Label) 
            (N : NormalTerm ∅ φυ)
            (V : Value N) → 
            (i : (l , φυ) ∈ (map (map₂ (_·'_ φ)) xs)) →
          (ana (⦅ xs ⦆ oxs) φ τ refl eq₂ M · (⟨ l ▹ N ⟩via i)) —→ 
          (anaVariant φ xs τ oxs oxs' M (⟨ l ▹ N ⟩via i) (V-Σ l V i))

  δ-syn : ∀ {xs : SimpleRow NormalType ∅ R[ κ ]} 
            {oxs : True (normalOrdered? xs)}
            (φ : NormalType ∅ (κ `→ ★))
            {oxs' : True (normalOrdered? (map (map₂ (φ ·'_)) xs))}
            (eq : Π (⦅ map (map₂ (φ ·'_)) xs ⦆ oxs') ≡ (⇓ (Π · (⇑ φ <$> ⇑ (⦅ xs ⦆ oxs)))))
            (M : NormalTerm ∅ (SynT' (⦅ xs ⦆ oxs) φ)) →
            (syn (⦅ xs ⦆ oxs) φ M) —→ (conv eq ⟨ synRecord φ xs oxs M ⟩)
