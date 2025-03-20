{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Checking where 

open import Rome.Operational.Prelude 

open import Rome.Operational.Kinds.Syntax 
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Kinds.Decidability

open import Rome.Operational.Types.Syntax


import Rome.Operational.Types.Pre.Syntax as Pre 
open Pre.Type
open Pre.Pred

--------------------------------------------------------------------------------
-- Embedding intrinsically kinded judgments back to pre-syntax

forget : Type Δ κ → Pre.Type Δ 
forgetPred : Pred Δ κ → Pre.Pred Δ 
forget (` α) = ` α
forget (`λ τ) = `λ (forget τ)
forget (τ₁ · τ₂) = forget τ₁ · forget τ₂
forget (τ₁ `→ τ₂) = forget τ₁ `→ forget τ₂
forget (`∀ τ) = `∀ (forget τ)
forget (μ τ) = μ (forget τ) 
forget (π ⇒ τ) = forgetPred π ⇒ forget τ
forget (lab l) = lab l
forget ⌊ τ ⌋ = ⌊ forget τ ⌋
forget ε = ε
forget (τ₁ ▹ τ₂) = forget τ₁ ▹ forget τ₂
forget (τ₁ <$> τ₂) = forget τ₁ <$> forget τ₂
forget Π = Π
forget Σ = Σ 

forgetPred (ρ₁ · ρ₂ ~ ρ₃) = forget ρ₁ · forget ρ₂ ~ forget ρ₃
forgetPred (ρ₁ ≲ ρ₂) = forget ρ₁ ≲ forget ρ₂ 

--------------------------------------------------------------------------------
-- Decidability of kind checking 

checks? : ∀ (κ : Kind) (Δ : KEnv) (τ : Pre.Type Δ) → Dec (Σ[ τ' ∈ Type Δ κ ] (forget τ' ≡ τ))
checks? κ₁ Δ (` {κ = κ₂} x) with κ₁ ≡k? κ₂
... | yes refl = yes (` x , refl)
... | no p     = no ( λ { (` α , refl) → p refl })

checks? (κ₁ `→ κ₂) Δ (`λ {κ₃} τ) with κ₁ ≡k? κ₃ 
... | no  p  = no λ { (`λ τ' , refl) → p refl }
... | yes refl with checks? κ₂ (Δ ,, κ₁) τ 
...            | yes (τ' , eq) = yes ((`λ τ') , (cong `λ eq))
...            | no q = no (λ { (`λ x , refl) → q (x , refl ) })

-- nontrivial cases
checks? κ Δ (τ · τ₁) = {!   !}
checks? κ Δ (π ⇒ τ) = {!   !}
checks? ★ Δ (τ `→ τ₁) = {!   !}
checks? ★ Δ (`∀ τ) = {!   !}
checks? ★ Δ (μ τ) = {!   !}
checks? ★ Δ ⌊ τ ⌋ = {!   !}
checks? L Δ (lab l) = yes (lab l , refl)
checks? R[ κ ] Δ (τ ▹ τ₁) = {!   !}
checks? R[ κ ] Δ (τ <$> τ₁) = {!   !}
checks? (κ `→ κ₁) Δ Π = {!   !}
checks? κ Δ Σ = {!   !} 
-- boring cases 
checks? ★ Δ (`λ τ) = no (λ { (` α , ())
                           ; (x · x₁ , ())
                           ; ((x `→ x₁) , ())
                           ; (`∀ x , ())
                           ; (μ x , ())
                           ; ((π ⇒ x) , ())
                           ; (⌊ x ⌋ , ()) })
checks? L Δ (`λ τ) = no (λ { (` α , ())
                           ; (τ' · τ'' , ())
                           ; (lab l , ()) }) 
checks? R[ κ ] Δ (`λ τ) = no (λ { (` α , ())
                                ; (x · x₁ , ())
                                ; (ε , ())
                                ; ((x ▹ x₁) , ())
                                ; ((x <$> x₁) , ()) })
checks? L Δ (τ `→ τ₁) = no (λ { (` α , ())
                              ; (x · x₁ , ())
                              ; (lab l , ()) })
checks? (κ `→ κ₁) Δ (τ `→ τ₁) = no (λ { (` α , ())
                                      ; (`λ x , ())
                                      ; (x · x₁ , ())
                                      ; (Π , ())
                                      ; (Σ , ()) })
checks? R[ κ ] Δ (τ `→ τ₁) = no (λ { (` α , ())
                                   ; (x · x₁ , ())
                                   ; (ε , ())
                                   ; ((x ▹ x₁) , ())
                                   ; ((x <$> x₁) , ()) })
checks? L Δ (`∀ τ) = no (λ { (` α , ())
                           ; (x · x₁ , ())
                           ; (lab l , ()) })
checks? (κ `→ κ₁) Δ (`∀ τ) = no (λ { (` α , ())
                                   ; (`λ x , ())
                                   ; (x · x₁ , ())
                                   ; (Π , ())
                                   ; (Σ , ()) })
checks? R[ κ ] Δ (`∀ τ) = no (λ { (` α , ())
                                ; (x · x₁ , ())
                                ; (ε , ())
                                ; ((x ▹ x₁) , ())
                                ; ((x <$> x₁) , ()) }) 
checks? L Δ (μ τ) = no (λ { (` α , ())
                          ; (x · x₁ , ())
                          ; (lab l , ()) })
checks? (κ `→ κ₁) Δ (μ τ) = no (λ { (` α , ())
                                  ; (`λ x , ())
                                  ; (x · x₁ , ())
                                  ; (Π , ())
                                  ; (Σ , ()) }) 
checks? R[ κ ] Δ (μ τ) = no (λ { (` α , ())
                               ; (x · x₁ , ())
                               ; (ε , ())
                               ; ((x ▹ x₁) , ())
                               ; ((x <$> x₁) , ()) }) 
checks? ★ Δ (lab l) = no (λ { (` α , ())
                            ; (x · x₁ , ())
                            ; ((x `→ x₁) , ())
                            ; (`∀ x , ())
                            ; (μ x , ())
                            ; ((π ⇒ x) , ())
                            ; (⌊ x ⌋ , ()) }) 
checks? (κ `→ κ₁) Δ (lab l) = no (λ { (` α , ())
                                    ; (`λ x , ())
                                    ; (x · x₁ , ())
                                    ; (Π , ())
                                    ; (Σ , ()) })
checks? R[ κ ] Δ (lab l) = no (λ { (` α , ())
                                 ; (x · x₁ , ())
                                 ; (ε , ())
                                 ; ((x ▹ x₁) , ())
                                 ; ((x <$> x₁) , ()) })
checks? L Δ ⌊ τ ⌋ = no (λ { (` α , ())
                          ; (x · x₁ , ())
                          ; (lab l , ()) })
checks? (κ `→ κ₁) Δ ⌊ τ ⌋ = no (λ { (` α , ())
                                  ; (`λ x , ())
                                  ; (x · x₁ , ())
                                  ; (Π , ())
                                  ; (Σ , ()) })
checks? R[ κ ] Δ ⌊ τ ⌋ = no (λ { (` α , ())
                               ; (x · x₁ , ())
                               ; (ε , ())
                               ; ((x ▹ x₁) , ())
                               ; ((x <$> x₁) , ()) })
checks? ★ Δ ε = no (λ { (` α , ())
                      ; (x · x₁ , ())
                      ; ((x `→ x₁) , ())
                      ; (`∀ x , ())
                      ; (μ x , ())
                      ; ((π ⇒ x) , ())
                      ; (⌊ x ⌋ , ()) })
checks? L Δ ε = no (λ { (` α , ())
                      ; (x · x₁ , ())
                      ; (lab l , ()) })
checks? (κ `→ κ₁) Δ ε = no (λ { (` α , ())
                              ; (`λ x , ())
                              ; (x · x₁ , ())
                              ; (Π , ())
                              ; (Σ , ()) })
checks? R[ κ ] Δ ε = yes (ε , refl)
checks? ★ Δ (τ ▹ τ₁) = no (λ { (` α , ())
                             ; (x · x₁ , ())
                             ; ((x `→ x₁) , ())
                             ; (`∀ x , ())
                             ; (μ x , ())
                             ; ((π ⇒ x) , ())
                             ; (⌊ x ⌋ , ()) })
checks? L Δ (τ ▹ τ₁) = no (λ { (` α , ())
                             ; (x · x₁ , ())
                             ; (lab l , ()) })
checks? (κ `→ κ₁) Δ (τ ▹ τ₁) = no (λ { (` α , ())
                                     ; (`λ x , ())
                                     ; (x · x₁ , ())
                                     ; (Π , ())
                                     ; (Σ , ()) })
checks? ★ Δ (τ <$> τ₁) = no (λ { (` α , ())
                               ; (x · x₁ , ())
                               ; ((x `→ x₁) , ())
                               ; (`∀ x , ())
                               ; (μ x , ())
                               ; ((π ⇒ x) , ())
                               ; (⌊ x ⌋ , ()) })
checks? L Δ (τ <$> τ₁) = no (λ { (` α , ())
                               ; (x · x₁ , ())
                               ; (lab l , ()) })
checks? (κ `→ κ₁) Δ (τ <$> τ₁) = no (λ { (` α , ())
                                       ; (`λ x , ())
                                       ; (x · x₁ , ())
                                       ; (Π , ())
                                       ; (Σ , ()) })
checks? ★ Δ Π = no (λ { (` α , ())
                      ; (x · x₁ , ())
                      ; ((x `→ x₁) , ())
                      ; (`∀ x , ())
                      ; (μ x , ())
                      ; ((π ⇒ x) , ())
                      ; (⌊ x ⌋ , ()) })
checks? L Δ Π = no (λ { (` α , ())
                      ; (x · x₁ , ())
                      ; (lab l , ()) })
checks? R[ κ ] Δ Π = no (λ { (` α , ())
                           ; (x · x₁ , ())
                           ; (ε , ())
                           ; ((x ▹ x₁) , ())
                           ; ((x <$> x₁) , ()) })