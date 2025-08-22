{-# OPTIONS --safe #-}
module Rome.Operational.Types.Checking where 

open import Rome.Operational.Prelude 

open import Rome.Operational.Kinds.Syntax 
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Kinds.Decidability

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Normal.Syntax


import Rome.Operational.Types.Pre.Syntax as Pre 
open Pre.Type
open Pre.Pred

--------------------------------------------------------------------------------
-- Embedding intrinsically kinded judgments back to pre-syntax

forget : Type Δ κ → Pre.Type Δ 
forgetPred : Pred Type Δ κ → Pre.Pred Δ 
forget (` α) = ` α
forget (`λ τ) = `λ (forget τ)
forget (τ₁ · τ₂) = forget τ₁ · forget τ₂
forget (τ₁ `→ τ₂) = forget τ₁ `→ forget τ₂
forget (`∀ τ) = `∀ (forget τ)
forget (μ τ) = μ (forget τ) 
forget (π ⇒ τ) = forgetPred π ⇒ forget τ
forget (lab l) = lab l
forget ⌊ τ ⌋ = ⌊ forget τ ⌋
forget (τ₁ ▹ τ₂) = forget τ₁ ▹ forget τ₂
forget (τ₁ <$> τ₂) = forget τ₁ <$> forget τ₂
forget Π = Π
forget Σ = Σ 

forgetPred (ρ₁ · ρ₂ ~ ρ₃) = forget ρ₁ · forget ρ₂ ~ forget ρ₃
forgetPred (ρ₁ ≲ ρ₂) = forget ρ₁ ≲ forget ρ₂ 

forgetNF : NormalType Δ κ → Pre.Type Δ
forgetNF = forget ∘ ⇑ 


--------------------------------------------------------------------------------
-- Kind checking from normal forms

check : ∀ (κ : Kind) (Δ : KEnv) (τ : Pre.Type Δ) → Dec (Σ[ τ' ∈ Type Δ κ ] (forget τ' ≡ τ))
check κ Δ (` {κ = κ'} x) with κ ≡k? κ'
... | yes refl = yes (` x , refl)
... | no  q = no (λ { (` α , refl)  → q refl }) 
check (κ₁ `→ κ₂) Δ (`λ τ) = {! check κ₂ (Δ ,, κ₁)   !}  
-- ... | yes (υ , eq) = yes ({! `λ  !} , {!   !})
-- ... | no q = {!   !} 
check κ Δ (τ · τ₁) = {!   !}
check κ Δ (τ `→ τ₁) = {!   !}
check κ Δ (`∀ τ) = {!   !}
check κ Δ (μ τ) = {!   !}
check κ Δ (π ⇒ τ) = {!   !}
check κ Δ (lab l) = {!   !}
check κ Δ ⌊ τ ⌋ = {!   !}
check κ Δ (τ ▹ τ₁) = {!   !}
check κ Δ (τ <$> τ₁) = {!   !}
check κ Δ Π = {!   !}
check κ Δ Σ = {!   !}
check κ Δ (τ ∖ τ₁) = {!   !} 



--------------------------------------------------------------------------------
-- Decidability of kind checking 

-- infer : ∀ (Δ : KEnv) (τ : Pre.Type Δ) → Dec (Σ[ κ ∈ Kind ] (Σ[ τ' ∈ Type Δ κ ] (forget τ' ≡ τ)))
-- check : ∀ (κ : Kind) (Δ : KEnv) (τ : Pre.Type Δ) → Dec (Σ[ τ' ∈ Type Δ κ ] (forget τ' ≡ τ))

-- infer Δ (` {κ} x) = yes (κ , ((` x) , refl))
-- infer Δ (`λ {κ₁ = κ₁} τ) with infer (Δ ,, κ₁) τ 
-- ... | yes (κ₂ , τ' , refl) = yes (κ₁ `→ κ₂ , `λ τ' , refl)
-- ... | no  p = no (λ { (κ₂ , ` α , ())
--                     ; (κ₂ , `λ τ' , refl) → p (_ , τ' , refl)
--                     ; (κ₂ , τ' · τ'' , ())
--                     ; (κ₂ , (τ' `→ τ'') , ())
--                     ; (κ₂ , `∀ τ' , ())
--                     ; (κ₂ , μ τ' , ())
--                     ; (κ₂ , (π ⇒ τ') , ())
--                     ; (κ₂ , lab l , ())
--                     ; (κ₂ , ⌊ τ' ⌋ , ())
--                     ; (κ₂ , ε , ())
--                     ; (κ₂ , (τ' ▹ τ'') , ())
--                     ; (κ₂ , (τ' <$> τ'') , ())
--                     ; (κ₂ , Π , ())
--                     ; (κ₂ , Σ , ()) })
-- infer Δ (τ · τ₁) = {!   !}
-- infer Δ (τ `→ τ₁) = {!   !}
-- infer Δ (`∀ {κ = κ₁} τ) with check ★ (Δ ,, κ₁) τ 
-- ... | yes (τ' , refl) = yes (★ , `∀ τ' , refl)
-- ... | no p  = no (λ { (_ , ` α , ())
--                     ; (_ , `λ τ' , ())
--                     ; (_ , τ' · τ'' , ())
--                     ; (_ , (τ' `→ τ'') , ())
--                     ; (_ , `∀ τ' , refl) → p (τ' , refl)
--                     ; (_ , μ τ' , ())
--                     ; (_ , (π ⇒ τ') , ())
--                     ; (_ , lab l , ())
--                     ; (_ , ⌊ τ' ⌋ , ())
--                     ; (_ , ε , ())
--                     ; (_ , (τ' ▹ τ'') , ())
--                     ; (_ , (τ' <$> τ'') , ())
--                     ; (_ , Π , ())
--                     ; (_ , Σ , ()) })
-- infer Δ (μ τ) = {!   !}
-- infer Δ (π ⇒ τ) = {!   !}
-- infer Δ (lab l) = yes (L , lab l , refl)
-- infer Δ ⌊ τ ⌋ = map′ (λ { (τ' , refl) → (★ , ⌊ τ' ⌋ , refl) }) (λ { (κ , ` α , ())
--                                                                   ; (κ , `λ τ' , ())
--                                                                   ; (κ , τ' · τ'' , ())
--                                                                   ; (κ , (τ' `→ τ'') , ())
--                                                                   ; (κ , `∀ τ' , ())
--                                                                   ; (κ , μ τ' , ())
--                                                                   ; (κ , (π ⇒ τ') , ())
--                                                                   ; (κ , lab l , ())
--                                                                   ; (κ , ⌊ τ' ⌋ , refl) → τ' , refl
--                                                                   ; (κ , ε , ())
--                                                                   ; (κ , (τ' ▹ τ'') , ())
--                                                                   ; (κ , (τ' <$> τ'') , ())
--                                                                   ; (κ , Π , ())
--                                                                   ; (κ , Σ , ()) }) (check L Δ τ)
-- -- infer Δ ε = yes (R[ ★ ] , ε , refl)
-- infer Δ (l ▹ τ) = {!   !}
-- infer Δ (τ₁ <$> τ₂) = {!   !}
-- infer Δ Π = yes (R[ ★ ] `→ ★ , Π , refl)
-- infer Δ Σ = yes (R[ ★ ] `→ ★ , Σ , refl)

-- check κ₁ Δ (` {κ = κ₂} x) with κ₁ ≡k? κ₂
-- ... | yes refl = yes (` x , refl)
-- ... | no p     = no ( λ { (` α , refl) → p refl })

-- check (κ₁ `→ κ₂) Δ (`λ {κ₃} τ) with κ₁ ≡k? κ₃ 
-- ... | no  p  = no λ { (`λ τ' , refl) → p refl }
-- ... | yes refl with check κ₂ (Δ ,, κ₁) τ 
-- ...            | yes (τ' , eq) = yes ((`λ τ') , (cong `λ eq))
-- ...            | no q = no (λ { (`λ x , refl) → q (x , refl ) })

-- -- nontrivial cases
-- check κ₂ Δ (τ₁ · τ₂) with infer Δ τ₂
-- ... | no  p = no (λ { (τ' · τ'' , refl) → p (_ , τ'' , refl) })
-- ... | yes (κ₁ , τ₂' , refl) with check (κ₁ `→ κ₂) Δ τ₁ 
-- ...                       | yes (τ₁' , refl) = yes (τ₁' · τ₂' , refl) 
-- ...                       | no  p = no (λ { (τ' · τ'' , eq) → p ({! τ₁  !} , {!   !}) }) 
-- check κ Δ (π ⇒ τ) = {!   !}
-- check ★ Δ (τ `→ τ₁) = {!   !}
-- check ★ Δ (`∀ τ) = {!   !}
-- check ★ Δ (μ τ) = {!   !}
-- check ★ Δ ⌊ τ ⌋ = {!   !}
-- check L Δ (lab l) = yes (lab l , refl)
-- check R[ κ ] Δ (τ ▹ τ₁) = {!   !}
-- check R[ κ ] Δ (τ <$> τ₁) = {!   !}
-- check (κ `→ κ₁) Δ Π = {!   !}
-- check κ Δ Σ = {!   !} 
-- -- boring cases 
-- check ★ Δ (`λ τ) = no (λ { (` α , ())
--                            ; (x · x₁ , ())
--                            ; ((x `→ x₁) , ())
--                            ; (`∀ x , ())
--                            ; (μ x , ())
--                            ; ((π ⇒ x) , ())
--                            ; (⌊ x ⌋ , ()) })
-- check L Δ (`λ τ) = no (λ { (` α , ())
--                            ; (τ' · τ'' , ())
--                            ; (lab l , ()) }) 
-- check R[ κ ] Δ (`λ τ) = no (λ { (` α , ())
--                                 ; (x · x₁ , ())
--                                 ; (ε , ())
--                                 ; ((x ▹ x₁) , ())
--                                 ; ((x <$> x₁) , ()) })
-- check L Δ (τ `→ τ₁) = no (λ { (` α , ())
--                               ; (x · x₁ , ())
--                               ; (lab l , ()) })
-- check (κ `→ κ₁) Δ (τ `→ τ₁) = no (λ { (` α , ())
--                                       ; (`λ x , ())
--                                       ; (x · x₁ , ())
--                                       ; (Π , ())
--                                       ; (Σ , ()) })
-- check R[ κ ] Δ (τ `→ τ₁) = no (λ { (` α , ())
--                                    ; (x · x₁ , ())
--                                    ; (ε , ())
--                                    ; ((x ▹ x₁) , ())
--                                    ; ((x <$> x₁) , ()) })
-- check L Δ (`∀ τ) = no (λ { (` α , ())
--                            ; (x · x₁ , ())
--                            ; (lab l , ()) })
-- check (κ `→ κ₁) Δ (`∀ τ) = no (λ { (` α , ())
--                                    ; (`λ x , ())
--                                    ; (x · x₁ , ())
--                                    ; (Π , ())
--                                    ; (Σ , ()) })
-- check R[ κ ] Δ (`∀ τ) = no (λ { (` α , ())
--                                 ; (x · x₁ , ())
--                                 ; (ε , ())
--                                 ; ((x ▹ x₁) , ())
--                                 ; ((x <$> x₁) , ()) }) 
-- check L Δ (μ τ) = no (λ { (` α , ())
--                           ; (x · x₁ , ())
--                           ; (lab l , ()) })
-- check (κ `→ κ₁) Δ (μ τ) = no (λ { (` α , ())
--                                   ; (`λ x , ())
--                                   ; (x · x₁ , ())
--                                   ; (Π , ())
--                                   ; (Σ , ()) }) 
-- check R[ κ ] Δ (μ τ) = no (λ { (` α , ())
--                                ; (x · x₁ , ())
--                                ; (ε , ())
--                                ; ((x ▹ x₁) , ())
--                                ; ((x <$> x₁) , ()) }) 
-- check ★ Δ (lab l) = no (λ { (` α , ())
--                             ; (x · x₁ , ())
--                             ; ((x `→ x₁) , ())
--                             ; (`∀ x , ())
--                             ; (μ x , ())
--                             ; ((π ⇒ x) , ())
--                             ; (⌊ x ⌋ , ()) }) 
-- check (κ `→ κ₁) Δ (lab l) = no (λ { (` α , ())
--                                     ; (`λ x , ())
--                                     ; (x · x₁ , ())
--                                     ; (Π , ())
--                                     ; (Σ , ()) })
-- check R[ κ ] Δ (lab l) = no (λ { (` α , ())
--                                  ; (x · x₁ , ())
--                                  ; (ε , ())
--                                  ; ((x ▹ x₁) , ())
--                                  ; ((x <$> x₁) , ()) })
-- check L Δ ⌊ τ ⌋ = no (λ { (` α , ())
--                           ; (x · x₁ , ())
--                           ; (lab l , ()) })
-- check (κ `→ κ₁) Δ ⌊ τ ⌋ = no (λ { (` α , ())
--                                   ; (`λ x , ())
--                                   ; (x · x₁ , ())
--                                   ; (Π , ())
--                                   ; (Σ , ()) })
-- check R[ κ ] Δ ⌊ τ ⌋ = no (λ { (` α , ())
--                                ; (x · x₁ , ())
--                                ; (ε , ())
--                                ; ((x ▹ x₁) , ())
--                                ; ((x <$> x₁) , ()) })
-- check ★ Δ ε = no (λ { (` α , ())
--                       ; (x · x₁ , ())
--                       ; ((x `→ x₁) , ())
--                       ; (`∀ x , ())
--                       ; (μ x , ())
--                       ; ((π ⇒ x) , ())
--                       ; (⌊ x ⌋ , ()) })
-- check L Δ ε = no (λ { (` α , ())
--                       ; (x · x₁ , ())
--                       ; (lab l , ()) })
-- check (κ `→ κ₁) Δ ε = no (λ { (` α , ())
--                               ; (`λ x , ())
--                               ; (x · x₁ , ())
--                               ; (Π , ())
--                               ; (Σ , ()) })
-- check R[ κ ] Δ ε = yes (ε , refl)
-- check ★ Δ (τ ▹ τ₁) = no (λ { (` α , ())
--                              ; (x · x₁ , ())
--                              ; ((x `→ x₁) , ())
--                              ; (`∀ x , ())
--                              ; (μ x , ())
--                              ; ((π ⇒ x) , ())
--                              ; (⌊ x ⌋ , ()) })
-- check L Δ (τ ▹ τ₁) = no (λ { (` α , ())
--                              ; (x · x₁ , ())
--                              ; (lab l , ()) })
-- check (κ `→ κ₁) Δ (τ ▹ τ₁) = no (λ { (` α , ())
--                                      ; (`λ x , ())
--                                      ; (x · x₁ , ())
--                                      ; (Π , ())
--                                      ; (Σ , ()) })
-- check ★ Δ (τ <$> τ₁) = no (λ { (` α , ())
--                                ; (x · x₁ , ())
--                                ; ((x `→ x₁) , ())
--                                ; (`∀ x , ())
--                                ; (μ x , ())
--                                ; ((π ⇒ x) , ())
--                                ; (⌊ x ⌋ , ()) })
-- check L Δ (τ <$> τ₁) = no (λ { (` α , ())
--                                ; (x · x₁ , ())
--                                ; (lab l , ()) })
-- check (κ `→ κ₁) Δ (τ <$> τ₁) = no (λ { (` α , ())
--                                        ; (`λ x , ())
--                                        ; (x · x₁ , ())
--                                        ; (Π , ())
--                                        ; (Σ , ()) })
-- check ★ Δ Π = no (λ { (` α , ())
--                       ; (x · x₁ , ())    
--                       ; ((x `→ x₁) , ())
--                       ; (`∀ x , ())
--                       ; (μ x , ())
--                       ; ((π ⇒ x) , ())
--                       ; (⌊ x ⌋ , ()) })
-- check L Δ Π = no (λ { (` α , ())
--                       ; (x · x₁ , ())
--                       ; (lab l , ()) })
-- check R[ κ ] Δ Π = no (λ { (` α , ())
--                            ; (x · x₁ , ())
--                            ; (ε , ())
--                            ; ((x ▹ x₁) , ())
--                            ; ((x <$> x₁) , ()) })
