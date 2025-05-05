{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.NBE where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Normal.Properties.Decidability

open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming


-- --------------------------------------------------------------------------------
-- -- reflection of neutral types & reification of semantic types
reflect : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ

reflect {κ = ★} τ            = ne τ
reflect {κ = L} τ            = ne τ
reflect {κ = R[ κ ]} τ       = left τ
reflect {κ = κ₁ `→ κ₂} τ     = λ ρ v → reflect (renₖNE ρ τ · reify v)

reifyKripke : KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} (` Z))))


reifyRow' : (n : ℕ) → (Fin n → NormalType Δ L × SemType Δ κ) → SimpleRow NormalType Δ R[ κ ]
reifyRow' zero P    = []
reifyRow' (suc n) P with P fzero
... | (l , τ) = (l , reify τ) ∷ reifyRow' n (P ∘ fsuc)

reifyRow : Row Δ R[ κ ] → SimpleRow NormalType Δ R[ κ ]
reifyRow (n , P) = reifyRow' n P

reifyRowOrdered : ∀ (ρ : Row Δ R[ κ ]) → OrderedRow ρ →  NormalOrdered (reifyRow ρ)
reifyRowOrdered' : ∀  (n : ℕ) → (P : Fin n → NormalType Δ L × SemType Δ κ) → 
                      OrderedRow (n , P) →  NormalOrdered (reifyRow (n , P))

reifyRowOrdered' zero P oρ = tt
reifyRowOrdered' (suc zero) P oρ = tt
reifyRowOrdered' (suc (suc n)) P (l₁<l₂ , ih) = l₁<l₂ , (reifyRowOrdered' (suc n) (P ∘ fsuc) ih)

reifyRowOrdered (n , P) oρ = reifyRowOrdered' n P oρ

reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} F = `λ (reify (F S (reflect (` Z))))
reify {κ = R[ κ ]} (left x) = ne x
reify {κ = R[ κ ]} (right  (ρ@(n , P) , q)) = ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ρ q))

--------------------------------------------------------------------------------
-- η normalization of neutral types

η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm = reify ∘ reflect

-- --------------------------------------------------------------------------------
-- -- Semantic environments

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

lifte : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
lifte {Δ₁} {Δ₂} {κ} η  = extende η' V
  where
    η' : Env Δ₁ (Δ₂ ,, κ)
    η' {κ'} v = (weakenSem {Δ = Δ₂} {κ₁ = κ'} {κ₂ = κ}) (η v)

    V  : SemType (Δ₂ ,, κ) κ
    V = reflect {κ = κ} (` Z)

idEnv : Env Δ Δ
idEnv = reflect ∘ `

-- --------------------------------------------------------------------------------
-- -- Semantic application

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
F ·V V = F id V

--------------------------------------------------------------------------------
-- -- Semantic complement

_∈Row_ : ∀ {m} → NormalType Δ L → (Q : Fin m → NormalType Δ L × SemType Δ κ) → Bool
_∈Row_ {m = zero} l Q = false
_∈Row_ {m = suc m} l Q with l ≡? Q fzero .fst
... | yes p = true
... | no  p =  l ∈Row (Q ∘ fsuc)

_∉Row_ : ∀ {m} → NormalType Δ L → (Q : Fin m → NormalType Δ L × SemType Δ κ) → Bool
_∉Row_ l Q = not (l ∈Row Q)

compl : ∀ {n m} → 
        (P : Fin n → NormalType Δ L × SemType Δ κ) 
        (Q : Fin m → NormalType Δ L × SemType Δ κ) → 
        Row Δ R[ κ ]
compl {n = zero} {m} P Q = εV
compl {n = suc n} {m} P Q with P fzero .fst ∈Row Q 
... | true = compl (P ∘ fsuc) Q 
... | false = (P fzero) ⨾⨾ (compl (P ∘ fsuc) Q)

--------------------------------------------------------------------------------
-- Semantic complement preserves well-ordering

lemma : ∀ {n m q} → 
          (P : Fin (suc n) → NormalType Δ L × SemType Δ κ)
          (Q : Fin m → NormalType Δ L × SemType Δ κ) → 
          (R : Fin (suc q) → NormalType Δ L × SemType Δ κ) → 
             OrderedRow (suc n , P) →
             compl (P ∘ fsuc) Q ≡ (suc q , R) → 
          P fzero .fst ≪ R fzero .fst
lemma {n = suc n} {q = q} P Q R oP eq₁ with P (fsuc fzero) .fst ∈Row Q 
lemma {κ = _} {suc n} {q = q} P Q R oP refl | false = oP .fst
... | true = ≪-trans (oP .fst) (lemma {n = n} (P ∘ fsuc) Q R (oP .snd) eq₁)

ordered-⨾⨾ : ∀ {n m} → 
                 (P : Fin (suc n) → NormalType Δ L × SemType Δ κ) 
                 (Q : Fin m → NormalType Δ L × SemType Δ κ) → 
                 OrderedRow (suc n , P) → 
                 OrderedRow (compl (P ∘ fsuc) Q) → OrderedRow (P fzero ⨾⨾ compl (P ∘ fsuc) Q)
ordered-⨾⨾ {n = n} P Q oP oC with compl (P ∘ fsuc) Q | inspect (compl (P ∘ fsuc)) Q
... | zero , R  | _        = tt
... | suc n , R | [[ eq ]] = lemma P Q R oP eq  , oC

ordered-compl :  ∀ {n m} → 
                 (P : Fin n → NormalType Δ L × SemType Δ κ) 
                 (Q : Fin m → NormalType Δ L × SemType Δ κ) → 
                 OrderedRow (n , P) → OrderedRow (m , Q) → OrderedRow (compl P Q)
ordered-compl {n = zero} P Q oρ₁ oρ₂ = tt
ordered-compl {n = suc n} P Q oρ₁ oρ₂ with P fzero .fst ∈Row Q
... | true = ordered-compl (P ∘ fsuc) Q (ordered-cut oρ₁) oρ₂
... | false = ordered-⨾⨾ P Q oρ₁ (ordered-compl (P ∘ fsuc) Q (ordered-cut oρ₁) oρ₂)

--------------------------------------------------------------------------------
-- Semantic complement on Rows
                
_─v_ : Row Δ R[ κ ] → Row Δ R[ κ ] → Row Δ R[ κ ]
(zero , P) ─v (zero , Q) = εV
(zero , P) ─v (suc m , Q) = εV
(suc n , P) ─v (zero , Q) = (suc n , P)
(suc n , P) ─v (suc m , Q) = compl P Q

ordered─v : ∀ (ρ₂ ρ₁ : Row Δ R[ κ ]) → OrderedRow ρ₂ → OrderedRow ρ₁ → OrderedRow (ρ₂ ─v ρ₁)
ordered─v (zero , P) (zero , Q) oρ₂ oρ₁ = tt
ordered─v (zero , P) (suc m , Q) oρ₂ oρ₁ = tt
ordered─v (suc n , P) (zero , Q) oρ₂ oρ₁ = oρ₂
ordered─v (suc n , P) (suc m , Q) oρ₂ oρ₁ = ordered-compl P Q oρ₂ oρ₁

--------------------------------------------------------------------------------
-- Semantic complement on SemTypes

_─V_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
left x ─V left y = left (x ─₁ (ne y))
left x ─V right (ρ , e) = left (x ─₁ ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ρ e)))
right (ρ , e) ─V left x = left (⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ρ e)) ─₂ x)
right (ρ₂ , q₂) ─V right (ρ₁ , q₁) = right ((ρ₂ ─v ρ₁) , ordered─v ρ₂ ρ₁ q₂ q₁)



--------------------------------------------------------------------------------
-- Testing compl operator

p : Fin 5 → NormalType ∅ L × SemType ∅ ★
p fzero = lab "a" , UnitNF
p (fsuc fzero) = lab "b" , UnitNF
p (fsuc (fsuc fzero)) = lab "c" , UnitNF
p (fsuc (fsuc (fsuc fzero))) = lab "e" , UnitNF
p (fsuc (fsuc (fsuc (fsuc fzero)))) = lab "f" , UnitNF

q : Fin 3 → NormalType ∅ L × SemType ∅ ★
q fzero = lab "b" , UnitNF
q (fsuc fzero) = lab "a" , UnitNF
q (fsuc (fsuc fzero)) = lab "d" , UnitNF

x : Bool
x =  _∈Row_  {Δ = ∅} {κ = ★} {m = 5} (lab "e") p

y : Row ∅ R[ ★ ]
y = compl {Δ = ∅} {κ = ★} q p

_ = {!compl {Δ = ∅} {κ = ★} p q!}


-- -- --------------------------------------------------------------------------------
-- -- -- Semantic lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_  F (left x) = left (reifyKripke F <$> x)
_<$>V_  F (right ((n , P), oρ)) = right ((n , overᵣ (F id) ∘ P) , orderedOverᵣ (F id) oρ) 

-- --------------------------------------------------------------------------------
-- -- Semantic flap

apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
apply a = λ ρ F → F ·V (renSem ρ a)

infixr 0 _<?>V_
_<?>V_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?>V a = apply a <$>V f


--------------------------------------------------------------------------------
-- Complement

-- _─V_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
-- left x ─V left x₁ = {!!}
-- left x ─V right y = {!!}
-- right y ─V left x = {!!}
-- right (zero , P) ─V right (zero , Q) = right εV
-- right (zero , P) ─V right (suc m , Q) = right εV
-- right (suc n , P) ─V right (zero , Q) = right (suc n , P)
-- right (suc n , P) ─V right (suc m , Q) = right ({!!} , {!!})
--   where
--     count : Fin (suc n) → Fin (suc m) → ℕ → ℕ
--     count i j k = {!fst (P i) ≟ ?!}

-- -- --------------------------------------------------------------------------------
-- -- -- (Generic) Semantic combinators for Π/Σ

record Xi : Set where 
  field
    Ξ★ : ∀ {Δ} → NormalType  Δ R[ ★ ] → NormalType Δ ★
    ΞL : ∀ {Δ} → NormalType Δ R[ L ] → NormalType Δ L
    ren-★ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ ★ ]) → renₖNF ρ (Ξ★ τ) ≡  Ξ★ (renₖNF ρ τ)
    ren-L : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ L ]) → renₖNF ρ (ΞL τ) ≡  ΞL (renₖNF ρ τ)

open Xi
ξ : ∀ {Δ} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = ★} Ξ x = Ξ .Ξ★ (reify x)
ξ {κ = L} Ξ x = Ξ .ΞL (reify x)
ξ {κ = κ₁ `→ κ₂} Ξ F = λ ρ v → ξ Ξ (renSem ρ F <?>V v)
ξ {κ = R[ κ ]} Ξ x = (λ ρ v → ξ Ξ v) <$>V x

Π-rec Σ-rec : Xi 
Π-rec = record
  {  Ξ★ = Π ; ΞL = ΠL ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }
Σ-rec = 
  record
  { Ξ★ = Σ ; ΞL = ΣL ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }

ΠV ΣV : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
ΠV = ξ Π-rec
ΣV = ξ Σ-rec

ξ-Kripke : Xi → KripkeFunction Δ R[ κ ] κ
ξ-Kripke Ξ ρ v = ξ Ξ v

Π-Kripke Σ-Kripke : KripkeFunction Δ R[ κ ] κ
Π-Kripke = ξ-Kripke Π-rec
Σ-Kripke = ξ-Kripke Σ-rec

--------------------------------------------------------------------------------
-- Type evaluation.

eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
evalPred : Pred Type Δ₁ R[ κ ] → Env Δ₁ Δ₂ → NormalPred Δ₂ R[ κ ]
evalRow        : SimpleRow Type Δ₁ R[ κ ] → Env Δ₁ Δ₂ → Row Δ₂ R[ κ ]
evalRowOrdered : (ρ : SimpleRow Type Δ₁ R[ κ ]) → (η : Env Δ₁ Δ₂) → Ordered ρ → OrderedRow (evalRow ρ η)


evalRow [] η = εV
evalRow ((l , τ) ∷ ρ) η = (eval l η , eval τ η) ⨾⨾ evalRow ρ η 

-- Throw a hook, a jab, and a boot
-- I sneak a *quick proof*, then I fire another boot
-- ⇓Row-isMap : ∀ (η : Env Δ₁ Δ₂) → (xs : SimpleRow Type Δ₁ R[ κ ])  → 
--                       reifyRow (evalRow xs η) ≡ map (λ τ → reify (eval τ η)) xs
-- ⇓Row-isMap η [] = refl
-- ⇓Row-isMap η (x ∷ xs) = cong₂ _∷_ refl (⇓Row-isMap η xs)


evalPred (ρ₁ · ρ₂ ~ ρ₃) η = reify (eval ρ₁ η) · reify (eval ρ₂ η) ~ reify (eval ρ₃ η)
evalPred (ρ₁ ≲ ρ₂) η = reify (eval ρ₁ η) ≲ reify (eval ρ₂ η)

eval {κ = κ} (` x) η = η x
eval {κ = κ} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval {κ = κ} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)

eval {κ = ★} (π ⇒ τ) η = evalPred π η ⇒ eval τ η
eval {Δ₁} {κ = ★} (`∀ τ) η = `∀ (eval τ (lifte η)) -- eval τ (lifte η)
eval {κ = ★} (μ τ) η = μ (reify (eval τ η))
eval {κ = ★} ⌊ τ ⌋ η = ⌊ reify (eval τ η) ⌋
eval (ρ₂ ─ ρ₁) η = eval ρ₂ η ─V eval ρ₁ η

----------------------------------------
-- Label evaluation.

eval {κ = L} (lab l) η = lab l

----------------------------------------
-- function evaluation.

eval {κ = κ₁ `→ κ₂} (`λ τ) η = λ ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)

----------------------------------------
-- Type constants

eval {κ = R[ κ ] `→ κ} Π η = Π-Kripke
eval {κ = R[ κ ] `→ κ} Σ η = Σ-Kripke
eval {κ = R[ κ ]} (f <$> a) η = (eval f η) <$>V (eval a η)
eval (⦅ ρ ⦆ oρ) η = right ((evalRow ρ η) , evalRowOrdered ρ η (toWitness oρ)) 

evalRowOrdered [] η oρ = tt
evalRowOrdered (x₁ ∷ []) η oρ = tt
evalRowOrdered ((lab l₁ , τ₁) ∷ (lab l₂ , τ₂) ∷ ρ) η (l₁<l₂ , oρ) with 
  evalRow ρ η | evalRowOrdered ((lab l₂ , τ₂) ∷ ρ) η oρ
... | zero , P | ih = l₁<l₂ , tt
... | suc n , P | ih₁ , ih₂ =  l₁<l₂ , ih₁ , ih₂


--------------------------------------------------------------------------------
-- Type normalization

-- Normalization algorithm
⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

⇓Pred : ∀ {Δ} → Pred Type Δ R[ κ ] → Pred NormalType Δ R[ κ ] 
⇓Pred π = evalPred π idEnv

⇓Row : ∀ {Δ} → SimpleRow Type Δ R[ κ ] → SimpleRow NormalType Δ R[ κ ] 
⇓Row ρ = reifyRow (evalRow ρ idEnv)

⇓NE : ∀ {Δ} → NeutralType Δ κ → NormalType Δ κ
⇓NE τ = reify (eval (⇑NE τ) idEnv)

-- Reabstraction of a NormalType to the semantic domain
↓ : NormalType Δ κ → SemType Δ κ 
↓ τ = eval (⇑ τ) idEnv
