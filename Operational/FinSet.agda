-- From "Dependently Typed Programming with Finite Sets", Firsto and Uustalu
-- https://firsov.ee/finset/finset.pdf
module Rome.Operational.FinSet where 

------------------------------------------------------------------------------------------------
-- 1. Introduction 

open import Rome.Operational.Prelude hiding (_∈_ ; ∥_∥ ; _∈?_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any.Properties
open import Data.List

module Pauli where 

    data Pauli : Set where 
        X : Pauli
        Y : Pauli 
        Z : Pauli 
        I : Pauli

    listPauli : List Pauli
    listPauli = X ∷ Y ∷ Z ∷ I ∷ []

    _≟P_ : ∀ (x y : Pauli) → Dec (x ≡ y) 
    X ≟P X = yes refl
    X ≟P Y = no (λ ())
    X ≟P Z = no (λ ())
    X ≟P I = no (λ ())
    Y ≟P X = no (λ ())
    Y ≟P Y = yes refl
    Y ≟P Z = no (λ ())
    Y ≟P I = no (λ ())
    Z ≟P X = no (λ ())
    Z ≟P Y = no (λ ())
    Z ≟P Z = yes refl
    Z ≟P I = no (λ ())
    I ≟P X = no (λ ())
    I ≟P Y = no (λ ())
    I ≟P Z = no (λ ())
    I ≟P I = yes refl

    

    allPauli : ∀ (x : Pauli) → x ∈ listPauli -- x ∈ listPauli
    allPauli X = here refl
    allPauli Y = there (here refl)
    allPauli Z = there (there (here refl))
    allPauli I = there (there (there (here refl)))

    _·_ : Pauli → Pauli → Pauli
    X · X = I
    X · Y = Z
    X · Z = Y
    Y · X = Z
    Y · Y = I
    Y · Z = X
    Z · X = Y
    Z · Y = X
    Z · Z = I
    x · I = x
    I · x = x

    ·-comm : (x1 x2 : Pauli) → x1 · x2 ≡ x2 · x1
    ·-comm X X = refl
    ·-comm X Y = refl
    ·-comm X Z = refl
    ·-comm X I = refl
    ·-comm Y X = refl
    ·-comm Y Y = refl
    ·-comm Y Z = refl
    ·-comm Y I = refl
    ·-comm Z X = refl
    ·-comm Z Y = refl
    ·-comm Z Z = refl
    ·-comm Z I = refl
    ·-comm I X = refl
    ·-comm I Y = refl
    ·-comm I Z = refl
    ·-comm I I = refl

    open import Data.Fin 
    f2p : Fin 4 → Pauli 
    f2p zero = X
    f2p (suc zero) = Y
    f2p (suc (suc zero)) = Z
    f2p (suc (suc (suc x))) = I

    p2f : Pauli → Fin 4 
    p2f X = zero
    p2f Y = suc zero 
    p2f Z = suc (suc zero) 
    p2f I = suc (suc (suc zero))
    
    f2p-surj : ∀ (x : Pauli) → f2p (p2f x) ≡ x
    f2p-surj X = refl
    f2p-surj Y = refl
    f2p-surj Z = refl
    f2p-surj I = refl

------------------------------------------------------------------------------------------------
-- 2. Basic Definitions

private
    variable
        X : Set 

All : (X : Set) → List X → Set
All X xs = (x : X) → x ∈ xs

elimDec : ∀ {A B : Set} → Dec A → (A → B) → (¬ A → B) → B 
elimDec (yes p) y n = y p 
elimDec (no p) y n = n p 


-- "Decidable" in agda std lib 
DecEq : (X : Set) → Set 
DecEq X = ∀ (x y : X) → Dec (x ≡ y)

-- Use Data.List.Membership.DecPropositional instead 
DecIn : (X : Set) → Set
DecIn X = (x : X) → (xs : List X) → Dec (x ∈ xs)

deq2din : ∀ X → DecEq X → DecIn X 
deq2din X d x [] = no (λ { () })
deq2din X d x (y ∷ xs) with d x y 
... | yes p = yes (here p)
... | no p  with deq2din X d x xs 
...         | yes q = yes (there q)
...         | no  q = no (λ { (here px) → p px
                            ; (there x) → q x })

_∈?_ : ∀ {X} {d : DecEq X} (x : X) → (xs : List X) → Dec (x ∈ xs)
_∈?_ {X} {d} x xs = deq2din X d x xs

din2deq : ∀ X → DecIn X → DecEq X                         
din2deq X i x y with i x (y ∷ [])  
... | yes (here px) = yes px 
... | no  p = no (λ { refl  → p  (here refl) }) 

-- A mere proposition has exactly one proof 
MProp : Set → Set 
MProp P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂ 

NoDup : List X → Set 
NoDup {X} xs = (x : X) → MProp (x ∈ xs)

Empty : (X : Set) → Set 
Empty X = All X [] 

NonEmpty : (X : Set) → Set 
NonEmpty X = X

NonEmptyToNegEmpty : NonEmpty X → (¬ Empty X) 
NonEmptyToNegEmpty x p with p x 
... | () 

-- Need some classical axiom here
NegEmptyToNonEmpty : (¬ Empty X) → NonEmpty X 
NegEmptyToNonEmpty p = {!   !}

-- I don't believe this is true unless X is nonempty
deq2dall : DecEq X → (xs : List X) → Dec (All X xs)
-- Can all (x : X) be in the empty list?
-- Yes if X is empty, no if X is nonempty.
deq2dall {X} d [] = {!  All !} 
deq2dall d (x ∷ xs) = {! deq2din _ d x  xs   !}

deq2dall' : DecEq X → NonEmpty X → (xs : List X) → Dec (All X xs)
deq2dall' {X} d ne [] = no (NonEmptyToNegEmpty ne)
deq2dall' {X} d ne (x ∷ xs) with deq2dall' d ne xs 
... | yes p = yes (λ x → there (p x))
... | no  p = no (λ allInXs → {! p  !})

-- no λ allInXs → p (λ y → help allInXs y)
--     where 
--         help : (allInXs : All X (x ∷ xs)) (y : X) → (Any (y ≡_) xs)
--         help allInXs y with allInXs y 
--         ... | here refl = {! allInXs y  !}
--         ... | there c = {!   !}


absurdAny : ∀ {A : Set} {x : X} {xs : List X} {p : x ∈ xs} → there p ≡ here refl → A 
absurdAny ()

de2dnd : DecEq X → (xs : List X) → Dec (NoDup xs)
de2dnd _≡?_ [] = yes (λ { x ()  })
de2dnd {X} _≡?_ (x ∷ xs) with _∈?_ {X} {_≡?_} x xs 
... | yes p = no (λ noDup → absurdAny (noDup x (there p) (here refl)))
... | no  p with (de2dnd _≡?_ xs) 
...         | yes noDup = yes (λ { y (here refl) (here refl) → refl
                             ; y (here refl) (there p₂) → ⊥-elim (p p₂)
                             ; y (there p₁) (here refl) → ⊥-elim (p p₁)
                             ; y (there p₁) (there p₂) → cong there (noDup y p₁ p₂) } ) 
...         | no  yesDup = no (λ noDup → yesDup (λ { y (here refl) (here refl) → refl
                                                   ; y (here refl) (there p₂) → there-injective (noDup y (there (here refl)) (there (there p₂)))
                                                   ; y (there p₁) (here refl) → there-injective (noDup y (there (there p₁)) (there (here refl)))
                                                   ; y (there p₁) (there p₂)  → there-injective (noDup y (there (there p₁)) (there (there p₂))) })) 

∥_∥ : Dec X → Set 
∥ yes p ∥ = ⊤ 
∥ no  p ∥ = ⊥ 

propSquash : (d : Dec X) → MProp ∥ d ∥ 
propSquash (yes p) = λ p₁ p₂ → refl
propSquash (no p) = λ ()

-- Analogous to to/fromWitness in stdlib 
fromSquash : (d : Dec X) → {∥ d ∥} → X 
fromSquash (yes p) {x} = p 

------------------------------------------------------------------------------------------------
-- 3. Finitness Constructively

-- A set is finite if its elements can be completely listed.
Listable : (X : Set) → Set 
Listable X = Σ[ xs ∈ List X ] (All X xs) 

-- Listability is equivalent to finite surjectivity 
FinSurj : (X : Set) → Set
FinSurj X = Σ[ n ∈ ℕ ] 
            Σ[ fromFin ∈ (Fin n → X) ] 
            Σ[ toFin   ∈ (X → Fin n) ] 
            ((x : X) → fromFin (toFin x) ≡ x)

BishopListable : (X : Set) → Set
BishopListable X = Σ[ xs ∈ List X ] (All X xs × NoDup xs)

-- Bishop listability is equivalent to finite bijectivity
FinBij : (X : Set) → Set
FinBij X = Σ[ n ∈ ℕ ] 
            Σ[ fromFin ∈ (Fin n → X) ] 
            Σ[ toFin   ∈ (X → Fin n) ] 
            (((x : X) → fromFin (toFin x) ≡ x) 
            × 
            ((i : Fin n) → toFin (fromFin i) ≡ i))

-- it is less obvious that all four notions are equivalent...
-- one can define: 
listable-to-DecEq : Listable X → DecEq X
listable-to-DecEq = {!   !}

-- and some other garbage to define a bi-implication:
-- Listable X ↔ BishopListable X

------------------------------------------------------------------------------------------------
-- 3. Listable subsets 

listableJunkSub : (U : Set) → (U → Set) → Set 
listableJunkSub U P = Σ[ xs ∈ List U ] 
                      ((x : U) → P x → x ∈ xs)

ListableSub : (U : Set) → (U → Set) → Set 
ListableSub U P = Σ[ xs ∈ List U ] 
                  ((x : U) → P x → x ∈ xs) × 
                  ((x : U) → x ∈ xs → P x)                 

DecEmpty : (xs : List X) → Dec (∀ (x : X) → ¬ (x ∈ xs))
DecEmpty [] = yes (λ { x () })
DecEmpty (x ∷ xs) = no (λ p → p x (here refl))

emptySubset? : {U : Set}{P : U → Set} (p : ListableSub U P) → 
         Dec (∀ (x : U) → ¬ (x ∈ fst p))   
emptySubset? {U} {P} (xs , _) = DecEmpty xs

-- this seems more interesting 

emptySubset?' : {U : Set}{P : U → Set} (p : ListableSub U P) → 
         Dec (∀ (x : U) → Empty (P x))   
emptySubset?' {U} {P} (xs , intoList , fromList) = {!   !}
  