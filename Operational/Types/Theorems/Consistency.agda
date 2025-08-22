{-# OPTIONS --safe #-}
module Rome.Operational.Types.Theorems.Consistency where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming 
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Equivalence.Properties
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming
  using (↻-ren-⇑NE ; ↻-ren-⇑)

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Consistency.Relation public

--------------------------------------------------------------------------------
-- syntactic mapping relates to semantic precomposition

map-over-⇑Row : ∀ (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (xs : SimpleRow Type Δ R[ κ₁ ]) → 
                (n : ℕ) (P : Fin n → Label × SemType Δ κ₁) → 
                ⟦ f ⟧≋ F → 
                ⟦ xs ⟧r≋ (n , P) → 
                ⟦ map (map₂ (f ·_)) xs ⟧r≋ (n , map₂ (F id) ∘ P)
map-over-⇑Row f F [] zero P rel-f rel-xs = tt
map-over-⇑Row f F (x ∷ xs) (suc n) P rel-f (rel-x , rel-xs) = 
  (rel-x .fst , 
  subst-⟦⟧≋ (eq-· (inst (renₖ-id f)) eq-refl) (rel-f id (rel-x .snd))) , 
  map-over-⇑Row f F xs n (P ∘ fsuc) rel-f rel-xs 

--------------------------------------------------------------------------------
-- Congruence over syntactic/semantic mapping

cong-<$>⟦⟧≋ : ∀ (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (v : Type Δ R[ κ₁ ]) (V : SemType Δ R[ κ₁ ]) → 
                ⟦ f ⟧≋ F → 
                ⟦ v ⟧≋ V → 
                ⟦ f <$> v ⟧≋ F <$>V V 
cong-<$>⟦⟧≋ f F v (φ <$> n) rel-f (g , g-eq , g-sound) = 
  (`λ (weakenₖ f · (weakenₖ g · (` Z)))) , 
  (eq-trans (eq-<$> eq-refl g-eq) eq-map-∘) , 
  (λ r vee → 
    subst-⟦⟧≋ 
      (eq-trans 
        (eq-· 
          (inst (subₖ-weaken-over-lift r f _)) 
          (eq-· 
            (inst (subₖ-weaken-over-lift r g _)) 
            eq-refl)) (eq-sym eq-β)) 
      (rel-f r (g-sound r vee)))
cong-<$>⟦⟧≋ f F v (l ▹ τ) rel-f (υ , eq , rel) = 
  (renₖ id f · υ) , 
  (eq-trans 
    (eq-<$> eq-refl eq) 
    (eq-trans 
      eq-▹$ 
        (eq-▹ 
          eq-refl 
          (eq-· 
            (eq-sym (inst (renₖ-id f))) 
            eq-refl)))) , 
  rel-f id rel
cong-<$>⟦⟧≋ f F v (row (n , P) x₁) rel-f (xs , oxs , eq , rel) = 
  map (map₂ (_·_ f)) xs , 
  fromWitness (map-map₂ xs (_·_ f) (toWitness oxs)) , 
  eq-trans (eq-<$> eq-refl eq) (eq-trans eq-map eq-refl), 
  map-over-⇑Row f F xs n P rel-f rel
  
cong-<$>⟦⟧≋ f F v ((V₂ ∖ V₁) {nr}) rel-f (υ₂ , υ₁ , eq , rel₂ , rel₁) = 
  (f <$> υ₂) ,
  (f <$> υ₁) , 
  eq-trans 
    (eq-<$> eq-refl eq) 
    eq-<$>-∖ , 
  cong-<$>⟦⟧≋ f F υ₂ V₂ rel-f rel₂ , 
  cong-<$>⟦⟧≋ f F υ₁ V₁ rel-f rel₁

--------------------------------------------------------------------------------
-- Congruence over complement

∈Row→∈L≋ : ∀ {n : ℕ} {P : Fin n → Label × SemType Δ κ} {l : Label} → 
              l ∈Row P → l ∈L (⇑Row (reifyRow' n P))
∈Row→∈L≋ {n = n} (fzero , refl) = Here
∈Row→∈L≋ {n = n} (fsuc i , eq) = There (∈Row→∈L≋ (i , eq))

∈L→∈Row≋ : ∀ {n : ℕ} {P : Fin n → Label × SemType Δ κ} {l : Label} → 
              l ∈L (⇑Row (reifyRow' n P)) → l ∈Row P
∈L→∈Row≋ {n = suc n} Here = fzero , refl
∈L→∈Row≋ {n = suc n} (There ev) with ∈L→∈Row≋ ev 
... | i , eq = (fsuc i) , eq

cong-∖⟦⟧≋ : ∀ {υ₂ υ₁ : Type Δ R[ κ ]} {ρ₂ ρ₁ : SemType Δ R[ κ ]} → 
              ⟦ υ₂ ⟧≋ ρ₂ → 
              ⟦ υ₁ ⟧≋ ρ₁ → 
              ⟦ υ₂ ∖ υ₁ ⟧≋ (ρ₂ ∖V ρ₁) 
cong-∖⟦⟧≋ {ρ₂ = φ <$> x} {φ₁ <$> x₁} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = φ <$> x} {x₁ ▹ x₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = φ <$> x} {row ρ x₁} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = φ <$> x} {ρ₁ ∖ ρ₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = x ▹ x₁} {φ <$> x₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = x ▹ x₁} {x₂ ▹ x₃} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = x ▹ x₁} {row ρ x₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = x ▹ x₁} {ρ₁ ∖ ρ₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = row ρ x} {φ <$> x₁} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = row ρ x} {x₁ ▹ x₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = row ρ x} {row ρ₁ x₁} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = row ρ x} {ρ₁ ∖ ρ₂} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = ρ₂ ∖ ρ₃} {φ <$> x} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = ρ₂ ∖ ρ₃} {x ▹ x₁} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = ρ₂ ∖ ρ₃} {row ρ x} rel₂ rel₁ = {!   !}
cong-∖⟦⟧≋ {ρ₂ = ρ₂ ∖ ρ₃} {ρ₁ ∖ ρ₄} rel₂ rel₁ = {!   !} 

cong-compl⟦⟧≋ : ∀ {n m : ℕ} 
                {P : Fin n → Label × SemType Δ κ}
                {Q : Fin m → Label × SemType Δ κ} →
                ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P) → 
                ⟦ ⇑Row (reifyRow' m Q) ⟧r≋ (m , Q) → 
                ⟦ ⇑Row (reifyRow' n P) ∖s ⇑Row (reifyRow' m Q) ⟧r≋ compl P Q
cong-compl⟦⟧≋ {n = zero} {P = P} {Q} P≋ Q≋ = tt
cong-compl⟦⟧≋ {n = suc n} {m} {P = P} {Q} P≋ Q≋ with P fzero .fst ∈Row? Q | P fzero .fst ∈L? ⇑Row (reifyRow' m Q) 
... | yes p | yes q = cong-compl⟦⟧≋ (P≋ .snd) Q≋
... | yes p | no q = ⊥-elim (q (∈Row→∈L≋ p))
... | no p | yes q = ⊥-elim (p (∈L→∈Row≋ q))
... | no p | no q = (refl , P≋ .fst .snd) , (cong-compl⟦⟧≋ (P≋ .snd) Q≋)

--------------------------------------------------------------------------------
-- Apply is sound

sound-apply : ∀ {κ₂} (v : Type Δ κ₁) (V : SemType Δ κ₁) → 
               ⟦ v ⟧≋ V → 
               consistentKripke {κ₂ = κ₂} (`λ (` Z · renₖ S v)) (apply V)
sound-apply v V rel-v r {g} {G} rel-G = 
  subst-⟦⟧≋ 
    (eq-sym eq-β)
  (subst-⟦⟧≋ 
    (eq-sym 
      (eq-· eq-refl 
      (eq-trans 
        (inst (cong (subₖ (extendₖ ` g)) (↻-liftₖ-weaken r v)))
        (inst (subₖ-weaken (renₖ r v) g))))) 
  (subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id g)) eq-refl) 
    (rel-G id (ren-⟦⟧≋ r rel-v))))

--------------------------------------------------------------------------------
-- Π and Π-Kripke are soundly related

sound-Π : ∀ {nl : True (notLabel? κ₁)} → 
        consistentKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} (Π {notLabel = nl}) Π-Kripke
sound-Σ : ∀ {nl : True (notLabel? κ₁)} → 
        consistentKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} (Σ {notLabel = nl}) Σ-Kripke

-- Mapping _apply_ over a row is semantic application
map-apply : ∀ (xs : SimpleRow Type Δ₁ R[ κ₁ `→ κ₂ ]) (n : ℕ) (P : Fin n → Label × KripkeFunction Δ₁ κ₁ κ₂) → 
               (φ : Renamingₖ Δ₁ Δ₂) → 
               (v : Type Δ₂ κ₁) (V : SemType Δ₂ κ₁) → 
               (rel-v : ⟦ v ⟧≋ V) → 
               (rel-xs : ⟦ xs ⟧r≋ (n , P)) → 
             ⟦ map (map₂ (_·_ (`λ (` Z · weakenₖ v))))
               (subRowₖ (extendₖ ` v)
                 (renRowₖ S (renRowₖ φ xs)))
             ⟧r≋ (n , λ x → (P x . fst) , apply V id (renKripke φ (P x .snd)))
map-apply [] zero P r v V rel-v rel-xs = tt 
map-apply ((l , τ) ∷ xs) (suc n) P r v V rel-v (rel-x , rel-xs) = 
  (rel-x .fst , 
  subst-⟦⟧≋ 
    (eq-sym eq-β) 
  (subst-⟦⟧≋ 
    (eq-sym (eq-· ((inst (sym (↻-subₖ-renₖ (renₖ r τ))))) (inst (sym (↻-subₖ-renₖ v))))) 
  (subst-⟦⟧≋ 
    (eq-· 
      (eq-sym (inst (subₖ-id (renₖ r τ)))) 
      (eq-sym (inst (subₖ-id v)))) 
    (subst-⟦⟧≋ 
      (eq-· eq-refl (inst (renₖ-id v))) 
      (rel-x .snd r (ren-⟦⟧≋ id rel-v)))))) ,
  map-apply xs n (P ∘ fsuc) r v V rel-v rel-xs

--------------------------------------------------------------------------------
--
-- Mapping Π over a row relates to pre-composition by semantic Π 
--
-- N.b. we can't use map-over-⇑Row' to define map-Π without violating termination
-- checking in sound-Π later.

map-Π : ∀ {nl : True (notLabel? κ)} (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
        ⟦ map (map₂ (_·_ (Π {notLabel = nl}))) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΠV (P i .snd))

map-Σ : ∀ {nl : True (notLabel? κ)} (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
        ⟦ map (map₂ (_·_ (Σ {notLabel = nl}))) (⇑Row (reifyRow' n P)) ⟧r≋ (n ,  λ i → P i .fst , ΣV (P i .snd))

--------------------------------------------------------------------------------
-- Consistency of Π and ΠV definition

sound-Π {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Π {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {v} {φ <$> n} (f , eq , sound-f) r {v'} {V'} rel-v = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r eq))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc)
    (sound-Π id 
    (_ , 
    ((eq-trans 
        (eq-· eq-β eq-refl) 
    (eq-trans 
      eq-β 
    (eq-trans 
      eq-map-∘ 
    (eq-<$> 
      (eq-trans 
        (eq-λ (eq-· 
          (eq-λ (eq-· 
            eq-refl 
            (eq-trans 
              (inst (↻-liftₖ-weaken S v')) 
              eq-refl))) 
          (eq-· 
            (renₖ-≡t S (inst (subₖ-weaken (renₖ r f) v'))) eq-refl))) 
        (eq-trans 
          (eq-λ eq-β) 
        (eq-trans (eq-λ (eq-· eq-refl (inst (subₖ-weaken (renₖ S v') _)))) eq-refl)))
      (eq-trans 
        (inst (subₖ-weaken (renₖ r (⇑NE n)) v')) 
        (eq-sym (inst (↻-ren-⇑NE r n)))))))) , 
    (λ {Δ} → sound {Δ})))))
    where 
      sound : consistentKripkeNE 
              (`λ (renₖ S (renₖ r f) · ` Z · renₖ S v'))
              (λ {Δ'} r₁ x₁ → apply V' r₁ (φ (r₁ ∘ r) x₁))
      sound r₁ n = 
        subst-⟦⟧≋ 
          (eq-trans 
            (eq-trans 
              (eq-· 
                (eq-· 
                  (inst (trans (renₖ-id _) (renₖ-comp r r₁  f))) 
                  (inst (renₖ-id _))) 
                eq-refl) 
              (eq-· 
                (eq-· (inst (subₖ-weaken-over-lift r₁ (renₖ r f) _)) eq-refl) 
                (inst (subₖ-weaken-over-lift r₁ v' _)))) 
            (eq-sym eq-β)) 
          (sound-f (r₁ ∘ r) n id (ren-⟦⟧≋ r₁ rel-v))     
sound-Π {κ₁ = R[ κ ]} ρ {v} {φ <$> n} (f , eq , sound-f) = 
  (`λ (weakenₖ Π · (weakenₖ f · ` Z))) , 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Π (eq-trans eq-map-∘ eq-refl))) , 
  λ r m → subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym m)) 
    (subst-⟦⟧≋ 
      (eq-sym eq-β) 
      (sound-Π id 
        (subst-⟦⟧≋ 
          (eq-· 
            (inst (subₖ-weaken-over-lift r f (⇑ (η-norm _)))) 
            m)
          (sound-f r m))))
sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (xs , oxs , eq , rel) ρ₂ {v} {V} rel-v = 
    subst-⟦⟧≋ (eq-sym (eq-Π-assoc)) 
    (sound-Π ρ₂ {renₖ ρ₂ f ?? v} 
      (⇑Row
        (reifyRow
         (n , (λ x₁ → P x₁ .fst , apply V id (renKripke ρ₂ (P x₁ .snd))))) , 
      (fromWitness 
        (Ordered⇑ _ (reifyRowOrdered _  
        (orderPreservingChanges (λ X → X {_} ρ₂ (renSem id V)) (ordered-⟦⟧r≋ xs (n , P) rel (toWitness oxs))))) , 
      ((eq-trans 
        (eq-· 
          (eq-· 
            eq-refl 
            (renₖ-≡t ρ₂ eq)) 
        eq-refl) 
        (eq-trans 
          (eq-· 
            eq-β 
            eq-refl) 
        (eq-trans 
          eq-β 
        (eq-trans 
          eq-map 
        (eq-row 
          (reify-⟦⟧r≋ (map-apply xs n P ρ₂ v V rel-v rel))))))) , 
      refl-⟦⟧r≋ (map-apply xs n P ρ₂ v V rel-v rel)))))
sound-Π {κ₁ = κ₁ `→ κ₂} r₁ {_} {l ▹ F} (f , eq , rel) r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r₂ eq))) eq-refl)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-· (eq-sym eq-β) eq-refl)) 
  (subst-⟦⟧≋ (eq-· eq-refl (eq-sym eq-β)) 
  (sound-Π r₂ 
    ((renₖ r₂ f · v) , 
    ((eq-trans 
      eq-▹$ 
      (eq-▹ 
        (eq-trans 
          (inst (sym (↻-subₖ-renₖ (renₖ r₂ (⇑NE l))))) 
        (eq-trans 
          (inst (subₖ-id (renₖ r₂ (⇑NE l)))) 
        (inst (sym (↻-ren-⇑NE r₂ l))))) 
        (eq-trans 
          eq-β 
        (eq-trans 
          (eq-· (inst (sym (↻-subₖ-renₖ (renₖ r₂ f)))) (inst (sym (↻-subₖ-renₖ v)))) 
        (eq-· (inst (subₖ-id (renₖ r₂ f))) (inst (subₖ-id v))))))) , 
    subst-⟦⟧≋ (eq-· eq-refl (inst (renₖ-id v))) (rel r₂ (ren-⟦⟧≋ id rel-V))))))))

sound-Π {κ₁ = κ₁ `→ κ₂} r₁ {f} {(V₂ ∖ V₁) {nr}} (υ₂ , υ₁ , eq , rel₂ , rel₁) r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r₂ eq))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Π-assoc) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl 
      (eq-· (eq-sym eq-β) eq-refl)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym eq-β)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym eq-<$>-∖)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl 
      (eq-∖ 
        (eq-<$> eq-refl (inst (↻-subₖ-renₖ (renₖ r₂ υ₂)))) 
        (eq-<$> eq-refl (inst (↻-subₖ-renₖ (renₖ r₂ υ₁)))))) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl 
      (eq-∖ 
        (eq-<$> eq-refl (inst (sym (subₖ-id (renₖ r₂ υ₂))))) 
        (eq-<$> eq-refl (inst (sym (subₖ-id (renₖ r₂ υ₁))))))) 
  (sound-Π r₂ 
    ((_ , _ , eq-refl , 
      cong-<$>⟦⟧≋ _ (apply V) _ (renSem r₂ V₂) (sound-apply v V rel-V) (ren-⟦⟧≋ r₂ rel₂) , 
      cong-<$>⟦⟧≋ _ (apply V) _ (renSem r₂ V₁) (sound-apply v V rel-V) (ren-⟦⟧≋ r₂ rel₁) )))))))))
sound-Π {κ₁ = R[ κ ]} {nl = nl} ρ {v} {row (n , P) _} (xs , oxs , eq , rel) = 
    map (map₂ (Π ·_)) xs , 
    fromWitness (map-map₂ xs (Π ·_) (toWitness oxs)) , 
    eq-trans 
      (eq-· eq-refl eq) 
    (eq-trans eq-Π 
      eq-map) , 
    map-over-⇑Row Π (λ ρ v → ξ Π-rec v) xs n P sound-Π rel
sound-Π {κ₁ = R[ κ ]} {nl = nl} ρ {v} {l ▹ τ} (υ , eq , rel) = 
  Π · υ ,
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Π 
  (eq-trans 
    eq-▹$ 
  eq-refl)) , 
  sound-Π id rel
sound-Π {κ₁ = R[ κ ]} {nl = nl} r {v} {(ρ₂ ∖ ρ₁) {nr}} (υ₂ , υ₁ , eq , rel₂ , rel₁) = 
  (Π <$> υ₂) , 
  (Π <$> υ₁) , 
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Π 
  eq-<$>-∖) , 
  subst-⟦⟧≋ eq-Π (sound-Π id rel₂) , 
  subst-⟦⟧≋ eq-Π (sound-Π id rel₁)
map-Π zero P rel = tt
map-Π {nl = nl} (suc n) P ((refl , rel-fzero) , rel-fsuc) = (refl , sound-Π {nl = nl} id rel-fzero) , (map-Π n (P ∘ fsuc) rel-fsuc)

--------------------------------------------------------------------------------
-- Consistency of Σ and ΣV definition (identical to Π def'n above)

sound-Σ {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≋ q)
sound-Σ {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {v} {φ <$> n} (f , eq , sound-f) r {v'} {V'} rel-v = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r eq))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Σ-assoc)
    (sound-Σ id 
    (_ , 
    ((eq-trans 
        (eq-· eq-β eq-refl) 
    (eq-trans 
      eq-β 
    (eq-trans 
      eq-map-∘ 
    (eq-<$> 
      (eq-trans 
        (eq-λ (eq-· 
          (eq-λ (eq-· 
            eq-refl 
            (eq-trans 
              (inst (↻-liftₖ-weaken S v')) 
              eq-refl))) 
          (eq-· 
            (renₖ-≡t S (inst (subₖ-weaken (renₖ r f) v'))) eq-refl))) 
        (eq-trans 
          (eq-λ eq-β) 
        (eq-trans (eq-λ (eq-· eq-refl (inst (subₖ-weaken (renₖ S v') _)))) eq-refl)))
      (eq-trans 
        (inst (subₖ-weaken (renₖ r (⇑NE n)) v')) 
        (eq-sym (inst (↻-ren-⇑NE r n)))))))) , 
    (λ {Δ} → sound {Δ})))))
    where 
      sound : consistentKripkeNE 
              (`λ (renₖ S (renₖ r f) · ` Z · renₖ S v'))
              (λ {Δ'} r₁ x₁ → apply V' r₁ (φ (r₁ ∘ r) x₁))
      sound r₁ n = 
        subst-⟦⟧≋ 
          (eq-trans 
            (eq-trans 
              (eq-· 
                (eq-· 
                  (inst (trans (renₖ-id _) (renₖ-comp r r₁  f))) 
                  (inst (renₖ-id _))) 
                eq-refl) 
              (eq-· 
                (eq-· (inst (subₖ-weaken-over-lift r₁ (renₖ r f) _)) eq-refl) 
                (inst (subₖ-weaken-over-lift r₁ v' _)))) 
            (eq-sym eq-β)) 
          (sound-f (r₁ ∘ r) n id (ren-⟦⟧≋ r₁ rel-v))     
sound-Σ {κ₁ = R[ κ ]} ρ {v} {φ <$> n} (f , eq , sound-f) = 
  (`λ (weakenₖ Σ · (weakenₖ f · ` Z))) , 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Σ (eq-trans eq-map-∘ eq-refl))) , 
  λ r m → subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym m)) 
    (subst-⟦⟧≋ 
      (eq-sym eq-β) 
      (sound-Σ id 
        (subst-⟦⟧≋ 
          (eq-· 
            (inst (subₖ-weaken-over-lift r f (⇑ (η-norm _)))) 
            m)
          (sound-f r m))))
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (xs , oxs , eq , rel) ρ₂ {v} {V} rel-v = 
    subst-⟦⟧≋ (eq-sym (eq-Σ-assoc)) 
    (sound-Σ ρ₂ {renₖ ρ₂ f ?? v} 
      (⇑Row
        (reifyRow
         (n , (λ x₁ → P x₁ .fst , apply V id (renKripke ρ₂ (P x₁ .snd))))) , 
      (fromWitness 
        (Ordered⇑ _ (reifyRowOrdered _  
        (orderPreservingChanges (λ X → X {_} ρ₂ (renSem id V)) (ordered-⟦⟧r≋ xs (n , P) rel (toWitness oxs))))) , 
      ((eq-trans 
        (eq-· 
          (eq-· 
            eq-refl 
            (renₖ-≡t ρ₂ eq)) 
        eq-refl) 
        (eq-trans 
          (eq-· 
            eq-β 
            eq-refl) 
        (eq-trans 
          eq-β 
        (eq-trans 
          eq-map 
        (eq-row 
          (reify-⟦⟧r≋ (map-apply xs n P ρ₂ v V rel-v rel))))))) , 
      refl-⟦⟧r≋ (map-apply xs n P ρ₂ v V rel-v rel)))))
sound-Σ {κ₁ = κ₁ `→ κ₂} r₁ {_} {l ▹ F} (f , eq , rel) r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ 
    (eq-sym eq-Σ-assoc) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r₂ eq))) eq-refl)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-· (eq-sym eq-β) eq-refl)) 
  (subst-⟦⟧≋ (eq-· eq-refl (eq-sym eq-β)) 
  (sound-Σ r₂ 
    ((renₖ r₂ f · v) , 
    ((eq-trans 
      eq-▹$ 
      (eq-▹ 
        (eq-trans 
          (inst (sym (↻-subₖ-renₖ (renₖ r₂ (⇑NE l))))) 
        (eq-trans 
          (inst (subₖ-id (renₖ r₂ (⇑NE l)))) 
        (inst (sym (↻-ren-⇑NE r₂ l))))) 
        (eq-trans 
          eq-β 
        (eq-trans 
          (eq-· (inst (sym (↻-subₖ-renₖ (renₖ r₂ f)))) (inst (sym (↻-subₖ-renₖ v)))) 
        (eq-· (inst (subₖ-id (renₖ r₂ f))) (inst (subₖ-id v))))))) , 
    subst-⟦⟧≋ (eq-· eq-refl (inst (renₖ-id v))) (rel r₂ (ren-⟦⟧≋ id rel-V))))))))

sound-Σ {κ₁ = κ₁ `→ κ₂} r₁ {f} {(V₂ ∖ V₁) {nr}} (υ₂ , υ₁ , eq , rel₂ , rel₁) r₂ {v} {V} rel-V = 
  subst-⟦⟧≋ 
    (eq-· (eq-· eq-refl (eq-sym (renₖ-≡t r₂ eq))) eq-refl) 
  (subst-⟦⟧≋ 
    (eq-sym eq-Σ-assoc) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl 
      (eq-· (eq-sym eq-β) eq-refl)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym eq-β)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl (eq-sym eq-<$>-∖)) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl 
      (eq-∖ 
        (eq-<$> eq-refl (inst (↻-subₖ-renₖ (renₖ r₂ υ₂)))) 
        (eq-<$> eq-refl (inst (↻-subₖ-renₖ (renₖ r₂ υ₁)))))) 
  (subst-⟦⟧≋ 
    (eq-· eq-refl 
      (eq-∖ 
        (eq-<$> eq-refl (inst (sym (subₖ-id (renₖ r₂ υ₂))))) 
        (eq-<$> eq-refl (inst (sym (subₖ-id (renₖ r₂ υ₁))))))) 
  (sound-Σ r₂ 
    ((_ , _ , eq-refl , 
      cong-<$>⟦⟧≋ _ (apply V) _ (renSem r₂ V₂) (sound-apply v V rel-V) (ren-⟦⟧≋ r₂ rel₂) , 
      cong-<$>⟦⟧≋ _ (apply V) _ (renSem r₂ V₁) (sound-apply v V rel-V) (ren-⟦⟧≋ r₂ rel₁) )))))))))
sound-Σ {κ₁ = R[ κ ]} {nl = nl} ρ {v} {row (n , P) _} (xs , oxs , eq , rel) = 
    map (map₂ (Σ ·_)) xs , 
    fromWitness (map-map₂ xs (Σ ·_) (toWitness oxs)) , 
    eq-trans 
      (eq-· eq-refl eq) 
    (eq-trans eq-Σ 
      eq-map) , 
    map-over-⇑Row Σ (λ ρ v → ξ Σ-rec v) xs n P sound-Σ rel
sound-Σ {κ₁ = R[ κ ]} {nl = nl} ρ {v} {l ▹ τ} (υ , eq , rel) = 
  Σ · υ ,
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Σ 
  (eq-trans 
    eq-▹$ 
  eq-refl)) , 
  sound-Σ id rel
sound-Σ {κ₁ = R[ κ ]} {nl = nl} r {v} {(ρ₂ ∖ ρ₁) {nr}} (υ₂ , υ₁ , eq , rel₂ , rel₁) = 
  (Σ <$> υ₂) , 
  (Σ <$> υ₁) , 
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Σ 
  eq-<$>-∖) , 
  subst-⟦⟧≋ eq-Σ (sound-Σ id rel₂) , 
  subst-⟦⟧≋ eq-Σ (sound-Σ id rel₁)

map-Σ zero P rel = tt
map-Σ {nl = nl} (suc n) P ((refl , rel-fzero) , rel-fsuc) = (refl , sound-Σ {nl = nl} id rel-fzero) , (map-Σ n (P ∘ fsuc) rel-fsuc)


--------------------------------------------------------------------------------
-- Fundamental lemma  

fundC : ∀ {Δ₁ Δ₂ κ}(τ : Type Δ₁ κ){σ : Substitutionₖ Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subₖ σ τ ⟧≋ (eval τ η)

--------------------------------------------------------------------------------
-- Fundamental lemma for rows

fundCRow : ∀ {Δ₁ Δ₂ κ}(xs : SimpleRow Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η  → ⟦ subRowₖ σ xs ⟧r≋ (evalRow xs η)
fundCRow [] e = tt
fundCRow ((l , τ) ∷ xs) e = (refl , fundC τ e ) , fundCRow xs e

--------------------------------------------------------------------------------
-- mapping an application over a row is application of the semantic row.

fundC-map-app : ∀ (n : ℕ) (P : Fin n → Label × SemType Δ₂ κ₁) →  
                (τ₁ : Type Δ₁ (κ₁ `→ κ₂)) → 
                (rel : ⟦ ⇑Row (reifyRow' n P) ⟧r≋ (n , P)) → 
                {σ : Substitutionₖ Δ₁ Δ₂} → {η : SemEnv Δ₁ Δ₂} → 
                ⟦ σ ⟧≋e η → 
                ⟦ map (map₂ (_·_ (subₖ σ τ₁))) (⇑Row (reifyRow' n P)) ⟧r≋ (n , (λ x → P x .fst , eval τ₁ η id (P x .snd)))

fundC-map-app zero P _ _ _ = tt
fundC-map-app (suc n) P τ₁ (rel-fzero , rel-fsuc) {σ} e =
  (refl , (subst-⟦⟧≋ (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) (fundC τ₁ e id (rel-fzero .snd)))) ,
  fundC-map-app n (P ∘ fsuc) τ₁ rel-fsuc e

--------------------------------------------------------------------------------
-- Fundamental lemma for predicates
          
fundCPred : ∀ {Δ₁ κ}(π : Pred Type Δ₁ R[ κ ]){σ : Substitutionₖ Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≋e η → (subPredₖ σ π) ≡p ⇑Pred (evalPred π η)           
fundCPred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-⟦⟧≋ (fundC ρ₁ e)) eq-· (reify-⟦⟧≋ (fundC ρ₂ e)) ~ (reify-⟦⟧≋ (fundC ρ₃ e))
fundCPred (ρ₁ ≲ ρ₂) e = (reify-⟦⟧≋ (fundC ρ₁ e)) eq-≲ (reify-⟦⟧≋ (fundC ρ₂ e))

--------------------------------------------------------------------------------
-- Fundamental lemma definition 

fundC (` α) {σ} {η} e = e α
fundC (`λ τ) {σ} {η} e ρ {v} {V} q = 
  subst-⟦⟧≋ 
    (eq-sym eq-β) 
    (subst-⟦⟧≋ 
      (eq-trans 
        (eq-trans 
          (inst (subₖ-cong (λ { Z → refl ; (S x) → trans (renₖ-subₖ-id ρ (σ x)) (↻-subₖ-renₖ (σ x)) }) τ)) 
          (inst (subₖ-comp τ))) 
        (inst (↻-subₖ-renₖ (subₖ (liftsₖ σ) τ)))) 
      (fundC τ (extend-⟦⟧≋ (ren-⟦⟧≋ ρ ∘ e) q)))
fundC (τ₁ · τ₂) {σ} {η} e  = 
  subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) 
    (fundC τ₁ e id (fundC τ₂ e))
fundC (τ₁ `→ τ₂) {σ} {η} e = eq-→ (fundC τ₁ e) (fundC τ₂ e)
fundC (`∀ τ) {σ} {η} e = eq-∀ (fundC τ {liftsₖ σ} {lifte η} (weaken-⟦⟧≋ e))
fundC (μ τ) {σ} {η} e = eq-μ
    (eq-trans 
        (eq-η {f = subₖ σ τ}) 
        (eq-λ (fundC τ e S eq-refl)))
fundC (π ⇒ τ) {σ} {η} e = eq-⇒ (fundCPred π e) (fundC τ e)
fundC (lab l) {σ} {η} e = eq-refl
fundC ⌊ τ ⌋ {σ} {η} e = eq-⌊⌋ (fundC τ e)
fundC (Π {notLabel = nl}) {σ} {η} e = sound-Π {nl = nl}
fundC Σ {σ} {η} e = sound-Σ
fundC (τ₁ <$> τ₂) {σ} {η} e with eval τ₂ η | fundC τ₂ e 
... | row (n , P) oρ | xs , oxs , eq , rel = 
  map (map₂ (_·_ (subₖ σ τ₁))) xs , 
  fromWitness (map-map₂ xs (_·_ (subₖ σ τ₁)) (toWitness oxs)) , 
  eq-trans 
    (eq-<$> eq-refl eq) 
  (eq-trans eq-map 
  (eq-row reflᵣ)) , 
  map-over-⇑Row (subₖ σ τ₁) (eval τ₁ η) xs n P (fundC τ₁ e) rel
... | l ▹ τ | υ , eq , rel = 
  subₖ σ τ₁ · υ , 
  eq-trans 
    (eq-<$> eq-refl eq) 
  (eq-trans 
    eq-▹$ 
  eq-refl) , 
  subst-⟦⟧≋ 
    (eq-· (inst (renₖ-id (subₖ σ τ₁))) eq-refl) 
    (fundC τ₁ e id rel)
fundC  {Δ₂ = Δ₂} ( _<$>_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {σ} {η} e | (ρ₂ ∖ ρ₁) {nr} | υ₂ , υ₁ , eq , rel₂ , rel₁ = 
  _ , _ , 
  eq-trans 
    (eq-<$> eq-refl eq) 
  eq-<$>-∖ , 
  cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) _ _ (fundC τ₁ e) rel₂ , 
  cong-<$>⟦⟧≋ (subₖ σ τ₁) (eval τ₁ η) _ _ (fundC τ₁ e) rel₁
fundC (τ₁ <$> τ₂) {σ} {η} e | φ <$> n | (f , eq-f , rel-f) with eval τ₁ η | fundC τ₁ e
... | F | rel-F = cong-<$>⟦⟧≋ (subₖ σ τ₁) F (subₖ σ τ₂) (φ <$> n) rel-F (f , eq-f , rel-f)
fundC (⦅ xs ⦆ oxs) {σ} {η} e with fundCRow xs e
fundC (⦅ [] ⦆ tt) {σ} {η} e | tt = [] , tt , eq-refl , tt
fundC (⦅ (l , τ) ∷ xs ⦆ oxs) {σ} {η} e | ((refl , ih-τ) , ih-xs) = 
  (l , subₖ σ τ) ∷ subRowₖ σ xs ,
  fromWitness (orderedSubRowₖ σ ((l , τ) ∷ xs) (toWitness oxs)) , 
  eq-refl , 
  (refl , ih-τ) , 
  ih-xs
fundC (ρ₂ ∖ ρ₁) {σ} {η} e = {!   !} 
-- with eval ρ₂ η | fundC ρ₂ e 
-- fundC (ρ₂ ∖ ρ₁) {σ} {η} e | φ <$> n | ih₁@(f , eq-f , rel-f) with eval ρ₁ η | fundC ρ₁ e 
-- ... | φ₂ <$> n₂   | ih₂@(g , eq-g , rel-g) = 
--   _ , _ , eq-refl , ih₁ , ih₂
-- ... | l ▹ τ  | ih₂@(υ , eq , rel) = 
--   _ , _ , eq-refl , ih₁ , ih₂
-- ... | row ρ x₂ | ih₂ = 
--   _ , _ , eq-refl , ih₁ , ih₂
-- ... | c ∖ c₁   | ih' = {!   !}
-- fundC (ρ₂ ∖ ρ₁) {σ} {η} e | l ▹ τ | ih₁@(υ , eq , rel) with eval ρ₁ η | fundC ρ₁ e 
-- ... | φ <$> n    | ih₂@(f , eq-f , rel-f) = 
--   _ , _ , eq-refl , ih₁ , ih₂ 
--   --  eq-∖ eq (reifyconsistentKripkeNE-≡t eq-f rel-f) , 
--   --   (eq-refl , rel) , (f , eq-sym (reifyconsistentKripkeNE-≡t eq-refl rel-f) , rel-f)
-- ... | x₂ ▹ x₃  | ih' = {!   !} -- eq-∖ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
-- ... | row ρ x₂ | ih' = {!   !} -- eq-∖ eq (eq-trans (ih' .fst) (eq-row reflᵣ)) , (eq-refl , rel) , (eq-row reflᵣ , (ih' .snd))
-- ... | c ∖ c₁   | ih' = {!   !} -- eq-∖ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
-- fundC (ρ₂ ∖ ρ₁) {σ} {η} e | row (n , P) oP | ih with eval ρ₁ η | fundC ρ₁ e 
-- ... | φ <$> n    | (f , eq-f , rel-f) = {!   !}
--   -- eq-∖ (eq-trans (ih .fst) (eq-row reflᵣ)) (reifyconsistentKripkeNE-≡t eq-f rel-f) , 
--   -- ((eq-row reflᵣ , (ih .snd)) , f , eq-sym (reifyconsistentKripkeNE-≡t eq-refl rel-f) , rel-f)
-- ... | x₂ ▹ x₃  | ih' = {!   !} -- eq-∖ (eq-trans (ih .fst) (eq-row reflᵣ)) (ih' .fst) , ((eq-row reflᵣ , (ih .snd)) , (eq-refl , (ih' .snd)))
-- ... | row (m , Q) oQ | ih' = {!   !}
--   -- eq-trans 
--   --   (eq-∖ (ih .fst) (ih' .fst)) 
--   --   (eq-trans 
--   --     (eq-compl {ozs = fromWitness (ordered-∖s {xs = ⇑Row (reifyRow (n , P))}
--   --               {ys = ⇑Row (reifyRow (m , Q))} (Ordered⇑ (reifyRow' n P) (reifyRowOrdered (n , P) oP)))}) 
--   --     (eq-row (reify-⟦⟧r≋ (cong-compl⟦⟧≋ (ih .snd) (ih' .snd))))) , 
--   -- refl-⟦⟧r≋ (cong-compl⟦⟧≋ (ih .snd) (ih' .snd))
-- ... | c ∖ c₁   | ih' = {!   !} -- eq-∖ (eq-trans (ih .fst) (eq-row reflᵣ)) (ih' .fst) , ((eq-row reflᵣ , (ih .snd)) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
-- fundC (ρ₂ ∖ ρ₁) {σ} {η} e | c ∖ c₁ | ih with eval ρ₁ η | fundC ρ₁ e 
-- ... | φ <$> n    | (f , eq-f , rel-f) = {!   !}
--   -- eq-∖ (ih .fst) (reifyconsistentKripkeNE-≡t eq-f rel-f) , 
--   -- ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (f , eq-sym (reifyconsistentKripkeNE-≡t eq-refl rel-f) , rel-f))
-- ... | x₂ ▹ x₃  | ih' = {!   !} -- eq-∖ (ih .fst) (ih' .fst) , ((eq-refl , (ih .snd)) , (eq-refl , (ih' .snd)))
-- ... | row ρ x₂ | ih' = {!   !} -- eq-trans (eq-∖ (ih .fst) (ih' .fst)) (eq-∖ eq-refl (eq-row reflᵣ)) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-row reflᵣ , (ih' .snd)))
-- ... | c ∖ c₁   | ih' = {!   !} -- eq-∖ (ih .fst) (ih' .fst) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
-- fundC (l ▹ τ) {σ} {η} e with eval l η | fundC l e
-- ... | ne x₁ | ih = {!   !} -- (eq-▹ ih (reify-⟦⟧≋ (fundC τ e))) , refl-⟦⟧≋ (fundC τ e)
-- ... | lab l' | ih = {!   !} 

-- eq-trans (eq-▹ eq-refl (reify-⟦⟧≋ (fundC τ e))) (eq-labTy ih) , 
--                     (refl , (refl-⟦⟧≋ (fundC τ e))) , 
--                     tt

--------------------------------------------------------------------------------
-- Fundamental theorem when substitution is the identity

⊢⟦_⟧≋ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≋ eval τ idEnv
⊢⟦ τ ⟧≋ = subst-⟦⟧≋ (inst (subₖ-id τ)) (fundC τ idSR)

--------------------------------------------------------------------------------
-- Consistency claim  

Consistency : Set 
Consistency = ∀ {Δ₁ κ} → (τ : Type Δ₁ κ) → τ ≡t ⇑ (⇓ τ) 

consistency : Consistency
consistency τ = reify-⟦⟧≋ (⊢⟦ τ ⟧≋)

 --------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ τ₂ then the embedding of τ₁ is equivalent to τ₂

embed-≡t : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ τ₂) → ⇑ τ₁ ≡t τ₂
embed-≡t {τ₁ = τ₁} {τ₂} refl = eq-sym (consistency τ₂) 

--------------------------------------------------------------------------------
-- Our definition of Consistency is equivalent to the converse of soundness

Completeness : Set 
Completeness = ∀ {Δ κ} → (τ₁ τ₂ : Type Δ κ) → ⇓ τ₁ ≡ ⇓ τ₂ → τ₁ ≡t τ₂

-- Consistency implies soundness-converse
Consistency→Completeness : Consistency → Completeness 
Consistency→Completeness consistency τ₁ τ₂ eq = eq-trans (consistency τ₁) (embed-≡t eq)

Completeness→Consistency : Completeness → Consistency
Completeness→Consistency ⇓-inj τ = (⇓-inj τ (⇑ (⇓ τ))) (sym (stability (⇓ τ)))

--------------------------------------------------------------------------------
-- ⇓ is injective w.r.t. type equivalence (converse of soundness lemma)

completeness : Completeness 
completeness = Consistency→Completeness consistency

-- A separate (and technically circular) proof of consistency
consistency₂ : Consistency
consistency₂ = Completeness→Consistency completeness

--------------------------------------------------------------------------------
-- consistency in lifted environments

consistency-liftsₖ : ∀ {Δ₁ κ} → (τ : Type (Δ₁ ,, κ₁) κ) → subₖ (liftsₖ `) τ ≡t ⇑ (reify (eval τ (lifte idEnv)))
consistency-liftsₖ τ = 
  reify-⟦⟧≋ (fundC τ (weaken-⟦⟧≋ {σ = `} {η = idEnv} idSR))
