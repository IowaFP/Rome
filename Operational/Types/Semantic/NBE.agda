{-# OPTIONS --safe #-}
module Rome.Operational.Types.Semantic.NBE where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
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
reflect {κ = R[ κ ]} ρ       = ne ρ
reflect {κ = κ₁ `→ κ₂} τ = λ ρ v → reflect (renₖNE ρ τ · reify v)

reifyKripke : KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} ((` Z)))))

reifyRow' : (n : ℕ) → (Fin n → Label × SemType Δ κ) → SimpleRow NormalType Δ R[ κ ]
reifyRow' zero P    = []
reifyRow' (suc n) P with P fzero
... | (l , τ) = (l , reify τ) ∷ reifyRow' n (P ∘ fsuc)

reifyRow : Row (SemType Δ κ) → SimpleRow NormalType Δ R[ κ ]
reifyRow (n , P) = reifyRow' n P

reifyRowOrdered : ∀ (ρ : Row (SemType Δ κ)) → OrderedRow ρ →  NormalOrdered (reifyRow ρ)
reifyRowOrdered' : ∀  (n : ℕ) → (P : Fin n → Label × SemType Δ κ) → 
                      OrderedRow (n , P) →  NormalOrdered (reifyRow (n , P))

reifyRowOrdered' zero P oρ = tt
reifyRowOrdered' (suc zero) P oρ = tt
reifyRowOrdered' (suc (suc n)) P (l₁<l₂ , ih) = l₁<l₂ , (reifyRowOrdered' (suc n) (P ∘ fsuc) ih)

reifyRowOrdered (n , P) oρ = reifyRowOrdered' n P oρ

reifyPreservesNR : ∀ (ρ₁ ρ₂ : RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
                     (nr : NotRow ρ₁ or NotRow ρ₂) → NotSimpleRow (reify ρ₁) or NotSimpleRow (reify ρ₂)

reifyPreservesNR' : ∀ (ρ₁ ρ₂ : RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
                     (nr : NotRow ρ₁ or NotRow ρ₂) → NotSimpleRow (reify ((ρ₁ ─ ρ₂) {nr}))

reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} F = `λ (reify (F S (reflect ((` Z)))))
-- reify {κ = R[ κ ]} (ne x) = ne x
reify {κ = R[ κ ]} (l ▹ τ) = (l ▹ₙ (reify τ))
reify {κ = R[ κ ]} (row ρ q) = ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ρ q))
reify {κ = R[ κ ]} (ne x) = ne x
reify {κ = R[ κ ]} (ne x ─ ρ₂) = (reify (ne x) ─ reify ρ₂) {nsr = tt}
reify {κ = R[ κ ]} ((l ▹ τ) ─ ρ) = (reify (l ▹ τ) ─ (reify ρ)) {nsr = tt}
reify {κ = R[ κ ]} (row ρ x ─ ne x₁) = (reify (row ρ x) ─ reify (ne x₁)) {nsr = tt}
reify {κ = R[ κ ]} (row ρ x ─ ρ'@(x₁ ▹ x₂)) = (reify (row ρ x) ─ reify ρ') {nsr = tt}
reify {κ = R[ κ ]} ((row ρ x ─ row ρ₁ x₁) {left ()})
reify {κ = R[ κ ]} ((row ρ x ─ row ρ₁ x₁) {right ()})
reify {κ = R[ κ ]} ((row ρ x ─ ρ'@((ρ₁ ─ ρ₂) {nr'})) {nr}) = ((reify (row ρ x)) ─ (reify ((ρ₁ ─ ρ₂) {nr'}))) {nsr = fromWitness (reifyPreservesNR (row ρ x) ρ' (right tt))}
reify {κ = R[ κ ]} ((((ρ₂ ─ ρ₁) {nr'}) ─ ρ) {nr}) = ((reify ((ρ₂ ─ ρ₁) {nr'})) ─ reify ρ) {fromWitness (reifyPreservesNR ((ρ₂ ─ ρ₁) {nr'}) ρ (left tt))}

reifyPreservesNR (ne x₁) ρ₂ (left x) = left tt
reifyPreservesNR (x₁ ▹ x₂) ρ₂ (left x) = left tt
reifyPreservesNR ((ρ₁ ─ ρ₃) {nr}) ρ₂ (left x) = left (reifyPreservesNR' ρ₁ ρ₃ nr)
reifyPreservesNR ρ₁ (ne x) (right y) = right tt
reifyPreservesNR ρ₁ (x ▹ x₁) (right y) = right tt
reifyPreservesNR ρ₁ ((ρ₂ ─ ρ₃) {nr}) (right y) = right (reifyPreservesNR' ρ₂ ρ₃ nr)

reifyPreservesNR' (ne x₁) ρ₂ (left x) = tt
reifyPreservesNR' (x₁ ▹ x₂) ρ₂ (left x) = tt
reifyPreservesNR' (ρ₁ ─ ρ₃) ρ₂ (left x) = tt
reifyPreservesNR' (ne x) ρ₂ (right y) = tt
reifyPreservesNR' (x ▹ x₁) ρ₂ (right y) = tt
reifyPreservesNR' (row ρ x) (ne x₁) (right y) = tt
reifyPreservesNR' (row ρ x) (x₁ ▹ x₂) (right y) = tt
reifyPreservesNR' (row ρ x) (ρ₂ ─ ρ₃) (right y) = tt
reifyPreservesNR' (ρ₁ ─ ρ₃) ρ₂ (right y) = tt

--------------------------------------------------------------------------------
-- η normalization of neutral types

η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm = reify ∘ reflect

-- --------------------------------------------------------------------------------
-- -- Semantic environments

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

idEnv : Env Δ Δ
idEnv = reflect ∘ `

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

lifte : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
lifte {Δ₁} {Δ₂} {κ} η  = extende (weakenSem ∘ η) (idEnv Z)

--------------------------------------------------------------------------------
-- Semantic application

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
F ·V V = F id V

--------------------------------------------------------------------------------
-- Semantic complement

_∈Row_ : ∀ {m} → (l : Label) → 
         (Q : Fin m → Label × SemType Δ κ) → 
         Set 
_∈Row_ {m = m} l Q = Σ[ i ∈ Fin m ] (l ≡ Q i .fst)

_∈Row?_ : ∀ {m} → (l : Label) → 
         (Q : Fin m → Label × SemType Δ κ) → 
         Dec (l ∈Row Q)
_∈Row?_ {m = zero} l Q = no λ { () }
_∈Row?_ {m = suc m} l Q with l ≟ Q fzero .fst
... | yes p = yes (fzero , p)
... | no  p with l ∈Row? (Q ∘ fsuc)
...        | yes (n , q) = yes ((fsuc n) , q) 
...        | no  q = no λ { (fzero , q') → p q' ; (fsuc n , q') → q (n , q') }

compl : ∀ {n m} → 
        (P : Fin n → Label × SemType Δ κ) 
        (Q : Fin m → Label × SemType Δ κ) → 
        Row (SemType Δ κ)
compl {n = zero} {m} P Q = εV
compl {n = suc n} {m} P Q with P fzero .fst ∈Row? Q 
... | yes _ = compl (P ∘ fsuc) Q 
... | no _ = (P fzero) ⨾⨾ (compl (P ∘ fsuc) Q)

-- --------------------------------------------------------------------------------
-- -- Semantic complement preserves well-ordering

open IsStrictPartialOrder (SPO) renaming (trans to <-trans)

lemma : ∀ {n m q} → 
          (P : Fin (suc n) → Label × SemType Δ κ)
          (Q : Fin m → Label × SemType Δ κ) → 
          (R : Fin (suc q) → Label × SemType Δ κ) → 
             OrderedRow (suc n , P) →
             compl (P ∘ fsuc) Q ≡ (suc q , R) → 
          P fzero .fst < R fzero .fst
lemma {n = suc n} {q = q} P Q R oP eq₁ with P (fsuc fzero) .fst ∈Row? Q 
lemma {κ = _} {suc n} {q = q} P Q R oP refl | no _ = oP .fst
... | yes _ = <-trans {i = P fzero .fst} {j = P (fsuc fzero) .fst} {k = R fzero .fst} (oP .fst) (lemma {n = n} (P ∘ fsuc) Q R (oP .snd) eq₁)

ordered-⨾⨾ : ∀ {n m} → 
                 (P : Fin (suc n) → Label × SemType Δ κ) 
                 (Q : Fin m → Label × SemType Δ κ) → 
                 OrderedRow (suc n , P) → 
                 OrderedRow (compl (P ∘ fsuc) Q) → OrderedRow (P fzero ⨾⨾ compl (P ∘ fsuc) Q)
ordered-⨾⨾ {n = n} P Q oP oC with compl (P ∘ fsuc) Q | inspect (compl (P ∘ fsuc)) Q
... | zero , R  | _        = tt
... | suc n , R | [[ eq ]] = lemma P Q R oP eq  , oC

ordered-compl :  ∀ {n m} → 
                 (P : Fin n → Label × SemType Δ κ) 
                 (Q : Fin m → Label × SemType Δ κ) → 
                 OrderedRow (n , P) → OrderedRow (m , Q) → OrderedRow (compl P Q)
ordered-compl {n = zero} P Q oρ₁ oρ₂ = tt
ordered-compl {n = suc n} P Q oρ₁ oρ₂ with P fzero .fst ∈Row? Q
... | yes _ = ordered-compl (P ∘ fsuc) Q (ordered-cut oρ₁) oρ₂
... | no _ = ordered-⨾⨾ P Q oρ₁ (ordered-compl (P ∘ fsuc) Q (ordered-cut oρ₁) oρ₂)

--------------------------------------------------------------------------------
-- Semantic complement on Rows
                
_─v_ : Row (SemType Δ κ) → Row (SemType Δ κ) → Row (SemType Δ κ)
(n , P) ─v (m , Q) = compl P Q

ordered─v : ∀ (ρ₂ ρ₁ : Row (SemType Δ κ)) → OrderedRow ρ₂ → OrderedRow ρ₁ → OrderedRow (ρ₂ ─v ρ₁)
ordered─v (n , P) (m , Q) oρ₂ oρ₁ = ordered-compl P Q oρ₂ oρ₁

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Semantic lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
NotRow<$> : ∀ {F : SemType Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : RowType Δ (λ Δ' → SemType Δ' κ₁) R[ κ₁ ]} → 
              NotRow ρ₂ or NotRow ρ₁ → NotRow (F <$>V ρ₂) or NotRow (F <$>V ρ₁)

F <$>V ne x = (λ {Δ'} r n → F r (reflect n) ) <$> x -- (reifyKripke F <$> x)
 -- (λ r n → F r (reflect n)) <$> x -- (λ r n → F r (reflect n)) <$> x ─ (row εV tt)
F <$>V (l ▹ τ) = l ▹ (F ·V τ)
F <$>V row (n , P) q = row (n , overᵣ (F id) ∘ P) (orderedOverᵣ (F id) q)
F <$>V ((ρ₂ ─ ρ₁) {nr}) = ((F <$>V ρ₂) ─ (F <$>V ρ₁)) {NotRow<$> nr}
F <$>V (G <$> n) = (λ {Δ'} r → F r ∘ G r) <$> n


NotRow<$> {F = F} {ne x₁} {ρ₁} (left x) = left tt
NotRow<$> {F = F} {x₁ ▹ x₂} {ρ₁} (left x) = left tt
NotRow<$> {F = F} {ρ₂ ─ ρ₃} {ρ₁} (left x) = left tt
NotRow<$> {F = F} {ρ₂} {ne x} (right y) = right tt
NotRow<$> {F = F} {ρ₂} {x ▹ x₁} (right y) = right tt
NotRow<$> {F = F} {ρ₂} {ρ₁ ─ ρ₃} (right y) = right tt


-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Semantic complement on SemTypes

_─V_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
row ρ₂ oρ₂ ─V row ρ₁ oρ₁ = row (ρ₂ ─v ρ₁) (ordered─v ρ₂ ρ₁ oρ₂ oρ₁)
ρ₂@(ne x) ─V ρ₁ = (ρ₂ ─ ρ₁) {nr = left tt}
ρ₂@(x ▹ x₁) ─V ρ₁ = (ρ₂ ─ ρ₁) {nr = left tt}
ρ₂@(row ρ x) ─V ρ₁@(ne x₁) = (ρ₂ ─ ρ₁) {nr = right tt}
ρ₂@(row ρ x) ─V ρ₁@(x₁ ▹ x₂) = (ρ₂ ─ ρ₁) {nr = right tt}
ρ₂@(row ρ x) ─V ρ₁@(_ ─ _) = (ρ₂ ─ ρ₁) {nr = right tt}
ρ@(ρ₂ ─ ρ₃) ─V ρ' = (ρ ─ ρ') {nr = left tt}

-- F <$> ρ₂ ─ (ρ₃ ─V ρ₁)

-- ne x ─V ρ = x ─₁ ρ
-- ρ ─V ne x = ρ ─₂ x
-- ρ ─V (x ▹ τ) = {!compl!} 
-- ρ ─V (ρ₂ ─₁ ρ₁) = {!!} -- ρ ─₁ (reflect ρ₂ ─V ρ₁) 
-- ρ ─V (ρ₂ ─₂ ρ₁) = {!!} 
-- row ρ x ─V row ρ₁ x₁ = {!!}

-- -- ne x ─V ρ = ? -- (ne x) ─ ρ
-- -- ρ₂ ─V ne x₂ = ρ₂ ─ (ne x₂)
-- -- (x ▹ x₁) ─V ρ = {!!} -- (x ▹ₙ (reify x₁)) ─₁ ρ
-- -- (x ─₁ ρ₂) ─V (x₁ ▹ x₂) = {!!}
-- -- (x ─₁ ρ₂) ─V row ρ x₁ = {!!}

-- --------------------------------------------------------------------------------
-- -- Semantic flap

apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
apply a = λ ρ F → F ·V (renSem ρ a)

infixr 0 _<?>V_
_<?>V_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?>V a = apply a <$>V f


--------------------------------------------------------------------------------
-- (Generic) Semantic combinators for Π/Σ

record Xi : Set where 
  field
    Ξ★ : ∀ {Δ} → NormalType  Δ R[ ★ ] → NormalType Δ ★
    ren-★ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ ★ ]) → renₖNF ρ (Ξ★ τ) ≡  Ξ★ (renₖNF ρ τ)

open Xi
ξ : ∀ {Δ} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = ★} Ξ x = Ξ .Ξ★ (reify x)
ξ {κ = L} Ξ x = lab "impossible"
ξ {κ = κ₁ `→ κ₂} Ξ F = λ ρ v → ξ Ξ (renSem ρ F <?>V v)
ξ {κ = R[ κ ]} Ξ x = (λ ρ v → ξ Ξ v) <$>V x

Π-rec Σ-rec : Xi 
Π-rec = record
  {  Ξ★ = Π ; ren-★ = λ ρ τ → refl }
Σ-rec = 
  record
  { Ξ★ = Σ ; ren-★ = λ ρ τ → refl  }

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

evalRow        : (ρ : SimpleRow Type Δ₁ R[ κ ]) → Env Δ₁ Δ₂ → Row (SemType Δ₂ κ)
evalRowOrdered : (ρ : SimpleRow Type Δ₁ R[ κ ]) → (η : Env Δ₁ Δ₂) → Ordered ρ → OrderedRow (evalRow ρ η)

evalRow [] η = εV 
evalRow ((l , τ) ∷ ρ) η = (l , (eval τ η)) ⨾⨾ evalRow ρ η 

⇓Row-isMap : ∀ (η : Env Δ₁ Δ₂) → (xs : SimpleRow Type Δ₁ R[ κ ])  → 
                      reifyRow (evalRow xs η) ≡ map (λ { (l , τ) → l , (reify (eval τ η)) }) xs
⇓Row-isMap η [] = refl
⇓Row-isMap η (x ∷ xs) = cong₂ _∷_ refl (⇓Row-isMap η xs)

evalPred (ρ₁ · ρ₂ ~ ρ₃) η = reify (eval ρ₁ η) · reify (eval ρ₂ η) ~ reify (eval ρ₃ η)
evalPred (ρ₁ ≲ ρ₂) η = reify (eval ρ₁ η) ≲ reify (eval ρ₂ η)

eval {κ = κ} (` x) η = η x
eval {κ = κ} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval {κ = κ} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)

eval {κ = ★} (π ⇒ τ) η = evalPred π η ⇒ eval τ η
eval {Δ₁} {κ = ★} (`∀ τ) η = `∀ (eval τ (lifte η)) 
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
eval (⦅ ρ ⦆ oρ) η = row (evalRow ρ η) (evalRowOrdered ρ η (toWitness oρ))
eval (l ▹ τ) η with eval l η 
... | ne x = (x ▹ eval τ η)
... | lab l₁ = row (⁅ (l₁ , eval τ η) ⁆) tt
evalRowOrdered [] η oρ = tt
evalRowOrdered (x₁ ∷ []) η oρ = tt
evalRowOrdered ((l₁ , τ₁) ∷ (l₂ , τ₂) ∷ ρ) η (l₁<l₂ , oρ) with 
  evalRow ρ η | evalRowOrdered ((l₂ , τ₂) ∷ ρ) η oρ
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

-- reabstraction
↑ : ∀ {Δ} → NormalType Δ κ → SemType Δ κ 
↑ τ = eval (⇑ τ) idEnv

--------------------------------------------------------------------------------
-- Testing compl operator

p : Fin 5 → Label × SemType ∅ ★
p fzero = "a" , UnitNF
p (fsuc fzero) = "b" , UnitNF
p (fsuc (fsuc fzero)) = "c" , UnitNF
p (fsuc (fsuc (fsuc fzero))) = "e" , UnitNF
p (fsuc (fsuc (fsuc (fsuc fzero)))) = "f" , UnitNF

q : Fin 3 → Label × SemType ∅ ★
q fzero = "b" , UnitNF
q (fsuc fzero) = "a" , UnitNF
q (fsuc (fsuc fzero)) = "d" , UnitNF

x : Dec (Σ-syntax (Fin 5) (λ i → "e" ≡ p i .fst))
x =  _∈Row?_  {Δ = ∅} {κ = ★} {m = 5} "e" p

y : Row (SemType ∅ ★)
y = compl {Δ = ∅} {κ = ★} p q

-- -- _ = reifyRow {κ = ★} y ≡  [ (lab "d" , UnitNF) ]
-- -- _ = refl
