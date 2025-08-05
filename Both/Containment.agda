{-# OPTIONS --safe #-}
module Rome.Both.Containment where

open import Rome.Both.Prelude

private
    variable
        A B C : Set
------------------------------------------------------------------------------
-- Definition of containment and containment over a disjoint sum

_⊆_ : List A → List A → Set
_⊆_ {A} xs ys = ∀ (x : A) → x ∈ xs → x ∈ ys

_⊆[_⊹_] : List A → List A → List A → Set
_⊆[_⊹_] {A} xs ys zs = ∀ (x : A) → x ∈ xs → x ∈ ys or x ∈ zs

-- --------------------------------------------------------------------------------
-- List inclusion forms a pre-order

⊆-refl : ∀ {xs : List A} →
         xs ⊆ xs
⊆-refl x x∈xs = x∈xs

⊆-trans : ∀ {xs ys zs : List A} →
          xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans i₁ i₂ = λ x → i₂ x ∘ i₁ x

-- --------------------------------------------------------------------------------
-- related elements are mapped together

map-∈ :  ∀ {xs : List A} {x : A} →
             (f : A → B) →
             x ∈ xs →
             f x ∈ map f xs
map-∈ f (here refl) = here refl
map-∈ f (there x∈xs) = there (map-∈ f x∈xs)

-- --------------------------------------------------------------------------------
-- Helper absurd eliminators

∈-elim : ∀ {x : A} →
          x ∈ [] → C
∈-elim ()

absurd-left-elim : ∀ {x : A} → x ∈ [] or B → B
absurd-left-elim (right y) = y

absurd-right-elim : ∀ {x : B} → A or x ∈ [] → A
absurd-right-elim (left x) = x

-- --------------------------------------------------------------------------------
-- map f is monotonic over _⊆_

⊆-map : ∀  {xs ys : List A} →
             (f : A → B) →
             xs ⊆ ys →
             map f xs ⊆ map f ys

⊆-map {xs = []} {[]} f i = λ { x () }
⊆-map {xs = []} {x ∷ ys} f i = λ { x () }
⊆-map {xs = x ∷ xs} {[]} f i = ∈-elim (i x (here refl))
⊆-map {xs = x ∷ xs} {y ∷ ys} f i z (here refl) = map-∈ f (i x (here refl))
⊆-map {xs = x ∷ xs} {y ∷ ys} f i z (there z∈fxs) = ⊆-map f (λ x₁ z₁ → i x₁ (there z₁)) z z∈fxs

-- --------------------------------------------------------------------------------
-- map f is monotonic over disjoint inclusion maps

⊆-map-or : ∀ {xs ys zs : List A} →
             (f : A → B) →
             xs ⊆[ ys ⊹ zs ] →
             map f xs ⊆[ map f ys ⊹ map f zs ]
⊆-map-or {xs = x ∷ xs} {[]} {zs} f i fx fx∈ with i x (here refl)
... | right y = right (⊆-map f (λ x x∈xs → absurd-left-elim (i x x∈xs)) fx fx∈)
⊆-map-or {xs = x ∷ xs} {y ∷ ys} {[]} f i fx fx∈ with i x (here refl)
... | left h = left (⊆-map f (λ x x∈xs → absurd-right-elim (i x x∈xs)) fx fx∈)
⊆-map-or {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} f i fx (here refl) with i x (here refl)
... | left x∈yys  = left (map-∈ f x∈yys)
... | right x∈zzs = right (map-∈ f x∈zzs)
⊆-map-or {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} f i fx (there fx∈) = ⊆-map-or f (λ x₁ z₁ → i x₁ (there z₁)) fx fx∈

------------------------------------------------------------------------------
-- IsMap asserts that a function is extensionally equivalent to a map

IsMap : ∀ (f* : List A → List B) → (f : A → B) → Set
IsMap {A} f* f = ∀ (xs : List A) → f* xs ≡ map f xs

-- --------------------------------------------------------------------------------
-- Containment is preserved by f* if f* is a map

⊆-cong : ∀ {xs ys : List A} →
            (f : A → B) (f* : List A → List B) →
            IsMap f* f →
            xs ⊆ ys →
            f* xs ⊆ f* ys
⊆-cong {xs = xs} {ys} f f* isMap i rewrite isMap xs | isMap ys = ⊆-map f i

⊆-cong-or : ∀ {xs ys zs : List A} →
            (f : A → B) (f* : List A → List B) →
            IsMap f* f →
            xs ⊆[ ys ⊹ zs ] →
            f* xs ⊆[ f* ys ⊹ f* zs ]
⊆-cong-or {xs = xs} {ys} {zs} f f* isMap i rewrite isMap xs | isMap ys | isMap zs = ⊆-map-or f i

-----------------------------------------------------------------------------------------
-- substitution of the membership relation

∈-subst₁ : ∀ {x y : A} {xs : List A} → x ∈ xs → x ≡ y → y ∈ xs
∈-subst₁ i refl = i

∈-subst₂ : ∀ {x : A} {xs ys : List A} → x ∈ xs → xs ≡ ys → x ∈ ys
∈-subst₂ i refl = i

-----------------------------------------------------------------------------------------
-- left truncation of an inclusion

truncate-⊆ : ∀ {x : A} → 
             {xs ys : List A } → 
             (x ∷ xs) ⊆ ys → 
             xs ⊆ ys 
truncate-⊆ {x = x} {xs} {ys} i = λ a → i a ∘ there 

truncate-⊆-or : ∀ {z : A} → 
             {xs ys zs : List A } → 
             (z ∷ zs) ⊆[ xs ⊹ ys ] → 
             zs ⊆[ xs ⊹ ys ] 
truncate-⊆-or {z = z} i = λ a → i a ∘ there

--------------------------------------------------------------------------------
-- A tail is contained by itself

tail-⊆ : ∀ {x : A} {xs : List A} → 
         xs ⊆ (x ∷ xs)
tail-⊆ {x} {xs} a a∈xs = there a∈xs 
