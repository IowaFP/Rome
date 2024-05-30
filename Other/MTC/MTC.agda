{- 

Some thoughts and code from:
- Modular type-safety proofs in Agda. Christopher Schwaab & Jeremy G. Siek. PLVP 2013.
  https://dl.acm.org/doi/pdf/10.1145/2428116.2428120
- Intrinsically-Typed Definitional Interpreters à la Carte. Rest et al. 2022.
  https://dl.acm.org/doi/pdf/10.1145/3563355
- Generic datatypes à la carte. Steven Keuchel and Tom Schrijvers. 2013. 
  https://dl.acm.org/doi/pdf/10.1145/2502488.2502491


I am more familiar with Ben's Metatheory à la carte [Delaware POPL '13], in Coq,
which uses an impredicative encoding of the LFP operator. As Agda does not
(safely) permit impredicativity, I thought such an approach would be impossible
here. Surprisingly not---so, there appears to be some trickery afoot.  

We start with Schwaab's approach. -}
--------------------------------------------------------------------------------
module MTC where


open import Agda.Primitive
open import Function using (_∘_)

open import Data.Product using (_×_; _,_)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)

infixl 6 _⊕_
infixr 7 _⊗_
data Functor : Set1 where
  Id : Functor
  Const : Set → Functor
  _⊕_ : Functor → Functor → Functor
  _⊗_ : Functor → Functor → Functor

--------------------------------------------------------------------------------
-- Here is the trick---we consider not arbitrary F : Set → Set,
-- but only polynomial functors, guaranteed to be strictly positive.

[_] : Functor → Set → Set
[ Id ] B = B
[ Const C ] B = C
[ F ⊕ G ] B = [ F ] B or [ G ] B
[ F ⊗ G ] B = [ F ] B × [ G ] B  

fmap : {A B : Set} → (F : Functor) → (A → B) → [ F ] A → [ F ] B
fmap Id f a = f a
fmap (Const C) f c = c
fmap (F ⊕ G) f (left x) = left (fmap F f x)
fmap (F ⊕ G) f (right y) = right (fmap G f y)
fmap (F ⊗ G) f (x , y) = (fmap F f x) , fmap G f y

--------------------------------------------------------------------------------
-- F-Algebras
FAlg : (F : Functor) (A : Set) → Set
FAlg F A = [ F ] A → A

π₁ : {F G : Functor} {A : Set} → FAlg (F ⊕ G) A → FAlg F A
π₁ ϕ = {!!}

π₂ : {F G : Functor} {A : Set} → FAlg (F ⊕ G) A → FAlg G A
π₂ ϕ = {!!}

MAlg : (F : Functor) (A : Set) → Set₁
MAlg F A = (∀ (R : Set) → (R → A) → [ F ] R → A)



--------------------------------------------------------------------------------
-- LFP 

data μ_ (F : Functor) : Set where
  In : [ F ] (μ F) → μ F

--------------------------------------------------------------------------------
-- 

cata : ∀ {F : Functor} {A : Set} → FAlg F A → μ F → A
cata {Id} ϕ (In x) = cata ϕ x
cata {Const B} ϕ (In x) = ϕ x
-- Need to establish Algebra fusion laws?
cata {F ⊕ G} ϕ (In (left x)) = {!!}
cata {F ⊕ G} ϕ (In (right y)) = {!!}
cata {F ⊗ G} ϕ (In (x , y)) = {!!}

-- mcata : ∀ {F : Functor} {A : Set} → MAlg F A → μ F → A
-- mcata {Id} ϕ (In x) = mcata ϕ x
-- mcata {Const B} ϕ (In x) = {!!}
-- mcata {F ⊕ G} ϕ (In x) = {!!}
-- mcata {F ⊗ G} ϕ (In x) = {!!}


-- Keuchel & Schrijvers instead invent the Strictly-Positive Functor (SPF) typeclass,
-- which has fold *as a field*:
--
-- class PFunctor f ⇒ SPF (f :: ∗ → ∗) where
--   type FixF :: ∗
--   inF :: f (FixF f ) → FixF f
--   outF :: FixF f → f (FixF f )
--   fold :: Algebra f a → FixF f → a
--
-- So we have not a catamorphism for any F, but only those F that tell us what
-- their catamorphism is.  This is also somewhat unsatisfactory. While elegant
-- and (to me) quite fascinating, I do not suspect either of these encodings to
-- be less tedious than copy + paste. The most recent paper ---
-- Intrinsically-Typed Definitional Interpreters à la Carte, Van Der Rest, et al
-- seems more promising, but it decomposes datatypes even more abstractly into
-- signatures à la universal algebra:

--   record Signature : Set where
--     constructor _⊲_
--     field 
--       Symbols : Set
--       Arity : Symbols → N
-- 
-- I find this exceptionally cool, but impractical---we have not even
-- gotten to the complexity of indexed data types, which is *all* of our
-- intrinsically typed structures. 
--
--   record ISignature (I : Set) : Set1 where
--     constructor _◮_
--     field 
--       ISymbols : I → Set
--       Indices : {i : I} → ISymbols i → List 
--
-- Above is the (universal algebraic) signature of indexed data types...  So,
-- all of our ASTs would become ISignatures.  To beat the dead horse: very cool,
-- but not better than copy + paste. Ironically, this conclusion---that no
-- encoding would feel satisfactory--is precisely what lead me to consider
-- instead row type systems... 


