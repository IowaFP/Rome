{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Commutativity where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Normal.Renaming as N
open import Rome.Operational.Types.Normal.Properties.Renaming as NTypeProps
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Theorems.Completeness.Relation
open import Rome.Operational.Types.Theorems.Completeness.Congruence

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with application.

↻-ren-app : ∀ (ρ : Renaming Δ₁ Δ₂) {F G : SemType Δ₁ (κ₁ `→ κ₂)} → _≋_ {κ = κ₁ `→ κ₂} F G → 
                {V₁ V₂ : SemType Δ₁ κ₁} → V₁ ≋ V₂ →  
                renSem ρ (F ·V V₁) ≋ (renSem {κ = κ₁ `→ κ₂} ρ G ·V renSem ρ V₂)
↻-ren-app ρ {F} {G} (Unif-F , Unif-G , Ext) {V₁} {V₂} r = 
  trans-≋ (Unif-F id ρ V₁ V₂ r) ((Ext ρ (ren-≋ ρ (refl-≋ₗ (sym-≋ r)))))

--------------------------------------------------------------------------------
-- - Renaming commutes with labeled rows (↻-ren-▹)
-- - Renaming under labeled rows respects functor composition laws (renSem-comp-▹; implied by ↻-ren-▹)
-- - Renaming commutes with labeled rows housing applications of Kripke functions (ren-comp-Kripke-▹)

↻-ren-▹ : ∀ (ρ : Renaming Δ₁ Δ₂) (l : NormalType Δ₁ L) (V₁ V₂ : SemType Δ₁ κ)  → 
                   V₁ ≋ V₂ → _≋_ {κ = R[ κ ]} (renSem {κ = R[ κ ]} ρ (l ▹V V₁)) (N.ren ρ l ▹V renSem ρ V₂)
↻-ren-▹ {κ = κ} ρ l V₁ V₂ q = refl , (ren-≋ ρ q)

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with <$>

↻-ren-<$> : ∀ (ρ : Renaming Δ₁ Δ₂) 
            {V₁ V₂ : SemType Δ₁ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ₁ R[ κ₁ ]} → 
            _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (renSem {κ = R[ κ₂ ]} ρ (V₁ <$>V W₁)) (renSem {κ = κ₁ `→ κ₂} ρ V₂ <$>V renSem {κ = R[ κ₁ ]} ρ W₂)
↻-ren-<$> ρ {V₁} {V₂} v {left x} {left x₁} refl = cong (_<$> renNE ρ x) (↻-ren-reify ρ v)
↻-ren-<$> ρ {V₁} {V₂} v {right (l , τ₁)} {right (.l , τ₂)} (refl , q) = refl , (↻-ren-app ρ v q)

--------------------------------------------------------------------------------
-- - Renaming commutes with ξ
-- - ξ is congruent w.r.t. semantic equivalence 


Unif-ξ : ∀ {Δ} {κ} (Ξ : Xi) → Uniform {Δ = Δ} {κ₁ = R[ κ ]} {κ₂ = κ} (ξ-Kripke Ξ)
Unif-ξ▹ : ∀ (Ξ : Xi) (l : NormalType Δ L) (F : SemType Δ (κ₁ `→ κ₂)) → _≋_ {κ = κ₁ `→ κ₂} F F →             
              Uniform {κ₁ = κ₁} {κ₂ = κ₂}  (λ ρ v → ξ Ξ (N.ren ρ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ F ·V v)))
↻-ren-ξ : ∀ {Δ₁} {Δ₂} (Ξ : Xi) {κ : Kind} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          _≋_ {κ = R[ κ ]} V₁ V₂ → renSem ρ (ξ Ξ V₁) ≋ ξ Ξ (renSem {κ = R[ κ ]} ρ V₂) 
cong-ξ : ∀ (Ξ : Xi) {κ} {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → ξ Ξ τ₁ ≋ ξ Ξ τ₂

Unif-ξ Ξ ρ = ↻-ren-ξ Ξ

Unif-ξ▹ {κ₁ = κ₁} {κ₂} Ξ l F q@(Unif-F , _ , Ext) ρ₁ ρ₂ V₁ V₂ q' =
    trans-≋ 
      (↻-ren-ξ Ξ ρ₂ 
        (N.ren ρ₁ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ₁ F ·V V₁)) 
        (N.ren ρ₁ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ₁ F ·V V₁)) 
        (refl , cong-App 
          {V₁ = renSem {κ = κ₁ `→ κ₂} ρ₁ F} 
          {renSem {κ = κ₁ `→ κ₂} ρ₁ F} 
          (ren-≋ {κ = κ₁ `→ κ₂} ρ₁ q) 
          {V₁} {V₁} 
          (refl-≋ₗ q'))) 
      (cong-ξ Ξ
         {τ₁ =
          right (N.ren ρ₂ (N.ren ρ₁ l) , renSem ρ₂ (renSem {κ = κ₁ `→ κ₂}  ρ₁ F ·V V₁))}
         {τ₂ =
          N.ren (λ x → ρ₂ (ρ₁ x)) l ▹V
          (renSem {κ = κ₁ `→ κ₂} (λ x → ρ₂ (ρ₁ x)) F ·V renSem ρ₂ V₂)}
         ((sym (ren-comp ρ₁ ρ₂ l)) , 
            trans-≋ 
              (↻-ren-app 
                ρ₂ 
                {renSem {κ = κ₁ `→ κ₂} ρ₁ F} 
                {renSem {κ = κ₁ `→ κ₂} ρ₁ F} 
                (ren-≋ {κ = κ₁ `→ κ₂} {V₁ = F} {V₂ = F} ρ₁ (refl-≋ₗ {κ = κ₁ `→ κ₂}  q)) 
                {V₁} {V₂} q') 
              (Ext (ρ₂ ∘ ρ₁) (ren-≋ ρ₂ (refl-≋ᵣ q')))))

open Xi
↻-ren-ξ Ξ {★} ρ (left x) (left _) refl = Ξ .ren-★ ρ (ne x)
↻-ren-ξ Ξ {L} ρ (left x) (left _) refl = Ξ .ren-L ρ (ne x)
↻-ren-ξ Ξ {κ₁ `→ κ₂} ρ (left x) (left _) refl = 
  {! ren-Uniform ρ ? !} , 
  {!   !} , 
  {!   !}
↻-ren-ξ Ξ {R[ κ ]} ρ (left x) (left _) refl = cong (_<$> renNE ρ x) (cong `λ {! ↻-ren-ξ Ξ (lift ρ) !})
↻-ren-ξ Ξ {★} ρ (right (l , τ)) (right (.l , .τ)) (refl , refl) = Ξ .ren-★ ρ (l ▹ τ)
↻-ren-ξ Ξ {L} ρ (right (l , τ)) (right (.l , .τ)) (refl , refl) = Ξ .ren-L ρ (l ▹ τ)
↻-ren-ξ Ξ {κ₁ `→ κ₂} ρ (right (l , F)) (right (.l , G)) (refl , q) = {!   !}
  -- ren-Uniform {F = λ ρ₁ v → ξ Ξ (N.ren ρ₁ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ₁ F ·V v))} ρ
  --   (Unif-ξ▹ Ξ l F (refl-≋ₗ q)) , 
  --   Unif-ξ▹ Ξ (N.ren ρ l) (renSem {κ = κ₁ `→ κ₂} ρ G) (ren-≋ ρ (refl-≋ᵣ q)) , 
  --   λ ρ₁ {V₁ = V₁} {V₂} v → cong-ξ Ξ
  --     {τ₁ =
  --      right
  --      (N.ren (λ x → ρ₁ (ρ x)) l , (renSem {κ = κ₁ `→ κ₂} (λ x → ρ₁ (ρ x)) F ·V V₁))}
  --     {τ₂ =
  --      right (N.ren ρ₁ (N.ren ρ l) , (renSem {κ = κ₁ `→ κ₂} ρ₁ (renSem {κ = κ₁ `→ κ₂} ρ G) ·V V₂))}
  --     ((ren-comp ρ ρ₁ l) , cong-App (ren-comp-≋ ρ ρ₁ q) v)
↻-ren-ξ Ξ {R[ κ ]} ρ (right (l , τ₁)) (right (.l , τ₂)) (refl , q) = refl , (↻-ren-ξ Ξ ρ τ₁ τ₂ q)

cong-ξ Ξ {κ = ★} {left x} {left _} refl = refl
cong-ξ Ξ {κ = L} {left x} {left _} refl = refl
cong-ξ Ξ {κ = κ₁ `→ κ₂} {left x} {left _} refl = {! Unif-ξ▹ Ξ  !}
cong-ξ Ξ {κ = R[ κ ]} {left x} {left _} refl = refl
cong-ξ Ξ {κ = ★} {right (l , τ₁)} {right (.l , τ₂)} (refl , refl) = refl
cong-ξ Ξ {κ = L} {right (l , τ₁)} {right (.l , τ₂)} (refl , refl) = refl
cong-ξ Ξ {κ = κ₁ `→ κ₂} {right (l , F)} {right (.l , G)} (refl , q@(Unif-F , Unif-G , Ext)) = 
  Unif-ξ▹ Ξ l F (refl-≋ₗ {κ = κ₁ `→ κ₂} q) ,
  Unif-ξ▹ Ξ l G (refl-≋ᵣ {κ = κ₁ `→ κ₂} q) ,
  λ ρ {V₁ = V₁} {V₂} v → cong-ξ Ξ (refl , Ext ρ v)
cong-ξ Ξ {κ = R[ κ ]} {right (l , τ₁)} {right (.l , τ₂)} (refl , q) = refl , (cong-ξ Ξ q)

---------------------------------------
-- instantiations for π

↻-ren-π : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          V₁ ≋ V₂ → renSem ρ (π V₁) ≋ π (renSem {κ = R[ κ ]} ρ V₂) 
↻-ren-π = ↻-ren-ξ Π-rec

cong-π : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → π τ₁ ≋ π τ₂
cong-π = cong-ξ Π-rec

Unif-π▹ : ∀ (l : NormalType Δ L) (F : SemType Δ (κ₁ `→ κ₂)) → _≋_ {κ = κ₁ `→ κ₂} F F →             
              Uniform {κ₁ = κ₁} {κ₂ = κ₂}  (λ ρ v → π (N.ren ρ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ F ·V v)))
Unif-π▹ = Unif-ξ▹ Π-rec

Unif-π : ∀ {Δ} {κ} → Uniform (π-Kripke {Δ = Δ} {κ = κ})
Unif-π ρ₁ = ↻-ren-π

---------------------------------------
-- instantiations for σ

↻-ren-σ : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          V₁ ≋ V₂ → renSem ρ (σ V₁) ≋ σ (renSem {κ = R[ κ ]} ρ V₂) 
↻-ren-σ = ↻-ren-ξ Σ-rec

cong-σ : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → _≋_ {κ = R[ κ ]} τ₁ τ₂ → σ τ₁ ≋ σ τ₂
cong-σ = cong-ξ Σ-rec

Unif-σ▹ : ∀ (l : NormalType Δ L) (F : SemType Δ (κ₁ `→ κ₂)) → _≋_ {κ = κ₁ `→ κ₂} F F →             
              Uniform {κ₁ = κ₁} {κ₂ = κ₂}  (λ ρ v → σ (N.ren ρ l ▹V (renSem {κ = κ₁ `→ κ₂} ρ F ·V v)))
Unif-σ▹ = Unif-ξ▹ Σ-rec

Unif-σ : ∀ {Δ} {κ} → Uniform (σ-Kripke {Δ = Δ} {κ = κ})
Unif-σ ρ₁ = ↻-ren-σ


--------------------------------------------------------------------------------
-- semantic renaming commutes with evaluation
--
--            eval in (renSem ρ ∘ η₂)
--  Type Δ₁ κ  ------
--  |                \            
--  | eval in η₁       \          
--  |                    \          
--  V                      V        
-- NormalType Δ₂ κ ----------> SemType Δ₂ κ
--                  renSem ρ 


↻-renSem-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (renSem ρ (eval τ η₁)) ≋ eval τ (renSem ρ ∘ η₂)
↻-renSem-eval-pred : ∀ (ρ : Renaming Δ₂ Δ₃) (π : Pred Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (N.renPred ρ (evalPred π η₁)) ≡ evalPred π (renSem ρ ∘ η₂)
idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
          eval τ η₁ ≋ eval τ η₂
idext-pred : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (π : Pred Δ₁ R[ κ ]) →
               evalPred π η₁ ≡ evalPred π η₂

↻-renSem-eval-pred ρ (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} P rewrite 
    ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-renSem-eval ρ ρ₁ P)
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-renSem-eval ρ ρ₂ P)  
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₃) | reify-≋ (↻-renSem-eval ρ ρ₃ P)  = refl
↻-renSem-eval-pred ρ (ρ₁ ≲ ρ₂) P rewrite
    ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₁) | reify-≋ (↻-renSem-eval ρ ρ₁ P)
  | ↻-ren-reify ρ (idext (refl-≋ₗ ∘ P) ρ₂) | reify-≋ (↻-renSem-eval ρ ρ₂ P)  = refl

↻-renSem-eval ρ Unit e = refl
↻-renSem-eval {κ = κ} ρ (` α) e = ren-≋ ρ (e α)
↻-renSem-eval ρ₁ (`λ τ) {η₁} {η₂} e = 
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≋ 
      (↻-renSem-eval ρ₃ τ (extend-≋ {η₂ = renSem (ρ₂ ∘ ρ₁) ∘ η₂}  (λ x → ren-≋ (ρ₂ ∘ ρ₁) (e x)) v)) 
      (idext (λ { Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) ; (S x) → sym-≋ (ren-comp-≋ (ρ₂ ∘ ρ₁) ρ₃ (e x)) }) τ)) ,
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≋ 
      (↻-renSem-eval ρ₃ τ (extend-≋ {η₂ = renSem ρ₂ ∘ (renSem ρ₁ ∘ η₂)}  (λ x → ren-≋ ρ₂ (sym-≋ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x)))))) v)) 
      (idext 
        (λ {     Z → ren-≋ ρ₃ (refl-≋ₗ (sym-≋ v)) 
           ; (S x) → sym-≋ (ren-comp-≋ ρ₂ ρ₃ (ren-≋ ρ₁ (refl-≋ₗ (sym-≋ (e x))))) }) τ)) ,
  λ ρ₂ q → idext (λ { Z → q ; (S x) → ren-comp-≋ ρ₁ ρ₂ (e x) }) τ
↻-renSem-eval {κ = .κ₂} ρ (_·_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {η₁} {η₂} e = 
  trans-≋
    (↻-ren-app ρ (idext (refl-≋ₗ ∘ e) τ₁) (idext (refl-≋ₗ ∘ e) τ₂))     
    (cong-App (↻-renSem-eval ρ τ₁ e) (↻-renSem-eval ρ τ₂ e))
↻-renSem-eval ρ (τ₁ `→ τ₂) e = cong₂ _`→_ (↻-renSem-eval ρ τ₁ e) (↻-renSem-eval ρ τ₂ e)
↻-renSem-eval ρ (`∀ κ τ) {η₁} {η₂} e = cong (`∀ κ) 
  (trans 
    (↻-renSem-eval (lift ρ) τ {↑e η₁} {↑e η₂} 
      (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl))) 
    (idext E τ))
  where
    E : Env-≋ (renSem (lift ρ) ∘ ↑e {κ = κ} η₂) (↑e (renSem ρ ∘ η₂))
    E Z = ↻-ren-reflect (lift ρ) (` Z)
    E (S x) = 
      trans-≋ 
        (sym-≋ (ren-comp-≋ S (lift ρ) (refl-≋ₗ (sym-≋ (e x))))) 
        (ren-comp-≋ ρ S (refl-≋ᵣ (e x)))
↻-renSem-eval ρ (μ τ) {η₁} {η₂} e = cong μ 
  (trans 
    (↻-ren-reify ρ (idext e τ)) 
    (reify-≋ (↻-renSem-eval ρ τ (refl-≋ᵣ ∘ e))))
↻-renSem-eval ρ (π ⇒ τ) e = cong₂ _⇒_ (↻-renSem-eval-pred ρ π e) (↻-renSem-eval ρ τ e)
↻-renSem-eval ρ (lab l) e = refl
↻-renSem-eval ρ (l ▹ τ) {η₁} {η₂} e = (↻-renSem-eval ρ l e) , (↻-renSem-eval ρ τ e)
↻-renSem-eval ρ ⌊ τ ⌋ e = cong ⌊_⌋ (↻-renSem-eval ρ τ e)
↻-renSem-eval ρ Π e = Unif-π , Unif-π , (λ ρ₁ x → cong-π x) 
↻-renSem-eval ρ Σ e = Unif-σ , Unif-σ , (λ ρ₁ x → cong-σ x) 
↻-renSem-eval ρ (τ₁ <$> τ₂) {η₁} {η₂} e = 
  trans-≋ 
    (↻-ren-<$> ρ (idext e τ₁) (idext e τ₂)) 
    (cong-<$> (↻-renSem-eval ρ τ₁ (refl-≋ᵣ ∘ e)) (↻-renSem-eval ρ τ₂ (refl-≋ᵣ ∘ e)))

-- ------------------------------------------------------------------------------
-- idext 

-- Evaluating types in related environments yields related semantic types.


idext-pred e (ρ₁ · ρ₂ ~ ρ₃) rewrite 
    sym (reify-≋ (idext e ρ₁))
  | sym (reify-≋ (idext e ρ₂)) 
  | sym (reify-≋ (idext e ρ₃))  = refl
idext-pred e (ρ₁ ≲ ρ₂) rewrite 
    sym (reify-≋ (idext e ρ₁))
  | sym (reify-≋ (idext e ρ₂))  = refl

idext {κ = κ} e Unit = refl
idext {κ = ★} e (` x) = e x
idext {κ = L} e (` x) = e x
idext {κ = κ `→ κ₁} e (` x) = e x
idext {κ = R[ κ ]} e (` x) = e x
idext {κ = κ} e (`λ τ) = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
           ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) τ)) ,
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ sym-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ₗ (sym-≋ q))
           ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e x))) }) τ)) , 
  λ ρ q → idext (extend-≋ (ren-≋ ρ ∘ e) q) τ
idext {κ = κ} e (τ₁ · τ₂) = snd (snd (idext e τ₁)) id (idext e τ₂)
idext {κ = κ} e (τ₁ `→ τ₂) = cong₂ _`→_ (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (π ⇒ τ) = cong₂ _⇒_ (idext-pred e π) (idext e τ)
idext {κ = κ} e (`∀ κ₁ τ) = cong (`∀ κ₁) (idext (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) τ)
idext {κ = ★} {η₁} {η₂} e (μ τ) with eval τ η₁ | eval τ η₂ | idext e τ
... | F | G | (Unif-F , Unif-G , Ext) = cong μ (cong `λ (Ext S refl))
idext {κ = κ} e (lab x) = refl
idext {κ = R[ κ ]} {η₁} {η₂} e (l ▹ τ) = (idext e l) , (idext e τ)
idext {κ = κ} e ⌊ τ ⌋ = cong ⌊_⌋ (idext e τ)
idext {κ = R[ κ₁ ] `→ κ₁} {η₁} {η₂} e Π = 
  Unif-π , 
  Unif-π , 
  λ ρ x → cong-π x 
idext {κ = κ} e Σ =
  Unif-σ , 
  Unif-σ , 
  λ ρ x → cong-σ x 
idext {κ = .(R[ κ₂ ])} e (_<$>_ {κ₁} {κ₂} τ₁ τ₂) = cong-<$> (idext e τ₁) (idext e τ₂) 

--------------------------------------------------------------------------------
-- Syntactic renaming commutes with evaluation
-- 

--            eval in (η₂ ∘ ρ)
--  Type Δ₁ κ  -------
--  |                 \            
--  | ren ρ            \          
--  |                   \          
--  V                    V        
-- Type Δ₂ κ ----------> SemType Δ₃ κ
--           eval in η₁ 

↻-ren-eval : ∀ (ρ : Renaming Δ₁ Δ₂) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₂ Δ₃} → 
                  (e : Env-≋ η₁ η₂) → eval (Types.ren ρ τ) η₁ ≋ eval τ (η₂ ∘ ρ)
↻-ren-eval-pred : ∀ (ρ : Renaming Δ₁ Δ₂) (τ : Pred Δ₁ R[ κ ]) → {η₁ η₂ : Env Δ₂ Δ₃} → 
                  (e : Env-≋ η₁ η₂) → evalPred (Types.renPred ρ τ) η₁ ≡ evalPred τ (η₂ ∘ ρ)

↻-ren-eval-pred ρ (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} e rewrite
    reify-≋ (↻-ren-eval ρ ρ₁ e)
  | reify-≋ (↻-ren-eval ρ ρ₂ e)  
  | reify-≋ (↻-ren-eval ρ ρ₃ e)  = refl
↻-ren-eval-pred ρ (ρ₁ ≲ ρ₂) e rewrite
    reify-≋ (↻-ren-eval ρ ρ₁ e)
  | reify-≋ (↻-ren-eval ρ ρ₂ e)  = refl

↻-ren-eval ρ Unit {η₁} {η₂} e = refl
↻-ren-eval ρ (` α) {η₁} {η₂} e = e (ρ α)
↻-ren-eval ρ (`λ τ) {η₁} {η₂} e = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
  trans-≋ 
    (↻-renSem-eval ρ₂ 
      (Types.ren (lift ρ) τ) 
      (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q)) 
    (idext 
      (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q) 
         ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) 
      (Types.ren (lift ρ) τ))) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ᵣ ∘ e ∘ ρ) q)) 
      (idext 
        (λ { Z     → ren-≋ ρ₂ (refl-≋ᵣ q) 
           ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ (e (ρ x)))) }) 
        τ)) , 
  λ ρ' q → 
    trans-≋ 
      (↻-ren-eval (Types.lift ρ) τ (extend-≋ (ren-≋ ρ' ∘ e) q) ) 
      (idext 
        (λ { Z     → refl-≋ᵣ q 
           ; (S x) → ren-≋ ρ' (refl-≋ᵣ (e (ρ x))) }) 
        τ)
↻-ren-eval ρ (τ₁ · τ₂) {η₁} {η₂} e = cong-App (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e)
↻-ren-eval ρ (τ₁ `→ τ₂) {η₁} {η₂} e = cong₂ _`→_ (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e)
↻-ren-eval ρ (`∀ κ τ) {η₁} {η₂} e = cong (`∀ κ) 
  (trans 
    (↻-ren-eval (lift ρ) τ 
      (extend-≋ 
        (ren-≋ S ∘ e) 
        (reflect-≋ {τ₁ = ` Z} refl))) 
    (idext 
      (λ { Z     → reflect-≋ refl 
         ; (S x) → (ren-≋ S ∘ refl-≋ᵣ ∘ e) (ρ x) }) τ))
↻-ren-eval ρ (μ τ) {η₁} {η₂} e = cong μ (reify-≋ (↻-ren-eval ρ τ e))
↻-ren-eval ρ (π ⇒ τ) {η₁} {η₂} e = cong₂ _⇒_ (↻-ren-eval-pred ρ π e) (↻-ren-eval ρ τ e)
↻-ren-eval ρ (lab l) {η₁} {η₂} e = refl
↻-ren-eval ρ (τ₁ ▹ τ₂) {η₁} {η₂} e = cong-▹ (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e)
↻-ren-eval ρ ⌊ τ ⌋ {η₁} {η₂} e = cong ⌊_⌋ (↻-ren-eval ρ τ e)
↻-ren-eval ρ Π {η₁} {η₂} e = Unif-π , Unif-π , λ ρ x → cong-π x
↻-ren-eval ρ Σ {η₁} {η₂} e = Unif-σ , Unif-σ , λ ρ x → cong-σ x
↻-ren-eval ρ (τ₁ <$> τ₂) {η₁} {η₂} e = cong-<$> (↻-ren-eval ρ τ₁ e) (↻-ren-eval ρ τ₂ e)


--------------------------------------------------------------------------------
-- Substitution lemma
-- 
-- Evaluation commutes with syntactic substitution

↻-subst-eval : ∀ (τ : Type Δ κ) {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ →
                        (σ : Types.Substitution Δ Δ₁) → 
                    eval (Types.sub σ τ) η₁ ≋ eval τ (λ x → eval (σ x) η₂)
↻-subst-eval-pred : ∀ (π : Pred Δ R[ κ ]) {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ →
                        (σ : Types.Substitution Δ Δ₁) → 
                    evalPred (Types.subPred σ π) η₁ ≡ evalPred π (λ x → eval (σ x) η₂)
↻-subst-eval-pred (ρ₁ · ρ₂ ~ ρ₃) e σ rewrite 
    reify-≋ (↻-subst-eval ρ₁ e σ) 
  | reify-≋ (↻-subst-eval ρ₂ e σ) 
  | reify-≋ (↻-subst-eval ρ₃ e σ) = refl
↻-subst-eval-pred (ρ₁ ≲ ρ₂) e σ rewrite
    reify-≋ (↻-subst-eval ρ₁ e σ) 
  | reify-≋ (↻-subst-eval ρ₂ e σ) = refl

↻-subst-eval Unit e σ = refl 
↻-subst-eval (` α) e σ = idext e (σ α)
↻-subst-eval (`λ τ) {η₁} {η₂} e σ =  
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ 
        (Types.sub (Types.lifts σ) τ) 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ₗ ∘ e) q)) 
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q) ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (refl-≋ₗ (e x))) }) 
        (Types.sub (Types.lifts σ) τ))) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ idext (refl-≋ᵣ ∘ e) ∘ σ) q)) 
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q) 
           ; (S x) → sym-≋ 
                       (ren-comp-≋ ρ₁ ρ₂ 
                         (idext (refl-≋ᵣ ∘ e) (σ x)))})
        τ)) , 
  λ ρ q → 
    trans-≋ 
    (↻-subst-eval τ 
      (extend-≋ (ren-≋ ρ ∘ e) q) 
      (Types.lifts σ)) 
    (idext 
      (λ { Z →  refl-≋ᵣ q 
         ; (S x) → trans-≋ 
                     (↻-ren-eval S (σ x) (extend-≋ (ren-≋ ρ ∘ refl-≋ᵣ ∘ e) (refl-≋ᵣ q))) 
                     (sym-≋ (↻-renSem-eval ρ (σ x) (refl-≋ᵣ ∘ e)))})
      τ)  
↻-subst-eval (`∀ κ τ) e σ = cong (`∀ κ) 
  (trans 
    (↻-subst-eval τ (extend-≋ (ren-≋ S ∘ e) (reflect-≋ refl)) (Types.lifts σ) ) 
    (idext 
      (λ { Z     → reflect-≋ refl 
         ; (S x) → trans-≋ 
                      (↻-ren-eval S (σ x) (extend-≋ (ren-≋ S ∘ refl-≋ᵣ ∘ e) (reflect-≋ refl))) 
                      (sym-≋ (↻-renSem-eval S (σ x) (refl-≋ᵣ ∘ e) )) }) 
      τ))
↻-subst-eval (τ₁ · τ₂) e σ = cong-App (↻-subst-eval τ₁ e σ) (↻-subst-eval τ₂ e σ) 
↻-subst-eval (τ₁ `→ τ₂) e σ = cong₂ _`→_ (↻-subst-eval τ₁ e σ) (↻-subst-eval τ₂ e σ)
↻-subst-eval (μ τ) e σ = cong μ (reify-≋ (↻-subst-eval τ e σ))
↻-subst-eval (π ⇒ τ) e σ = cong₂ _⇒_ (↻-subst-eval-pred π e σ) (↻-subst-eval τ e σ)
↻-subst-eval (lab l) e σ = refl
↻-subst-eval (τ₁ ▹ τ₂) e σ = (↻-subst-eval τ₁ e σ) , (↻-subst-eval τ₂ e σ)
↻-subst-eval ⌊ τ₁ ⌋ e σ = cong ⌊_⌋ (↻-subst-eval τ₁ e σ)
↻-subst-eval Π e σ = Unif-π , Unif-π , λ ρ v → cong-π v
↻-subst-eval Σ e σ = Unif-σ , Unif-σ , λ ρ v → cong-σ v
↻-subst-eval (τ₁ <$> τ₂) e σ = cong-<$> (↻-subst-eval τ₁ e σ) (↻-subst-eval τ₂ e σ)

transfer : ∀ (f : Type Δ₁ (κ₁ `→ κ₂)) → (ρ : Renaming Δ₂ Δ₃) {V₁ V₂ : SemType Δ₃ κ₁} → (V₁ ≋ V₂) → {η₁ η₂ : Env Δ₁ Δ₂} → 
              Env-≋ η₁ η₂ →  eval f (renSem ρ ∘ η₁) id V₁ ≋ eval f η₂ ρ V₂
transfer (` α) ρ v e = snd (snd (e α)) ρ v
transfer (`λ f) ρ v e = idext (λ { Z → v
                                 ; (S x) → {!   !} }) f
transfer (f · f₁) ρ v e = trans-≋ (snd (snd (transfer f ρ {!   !} e)) id v) {!   !}
transfer Π ρ v e = cong-π v
transfer Σ ρ v e = cong-σ v