--------------------------------------------------------------------------------
-- Bi-implication (_⇔_)
--------------------------------------------------------------------------------
--
-- Why roll your own?
--
-- The standard library (Function.Equivalence) defines bi-implication over
-- setoid equivalence. To an Agda expert this is maybe advantageous.  To me,
-- this is unnecessary, as the equivalence relation I am reasoning over is
-- equality. The setoid business leads to (i) longer proofs (ii) hard-to-parse
-- goals.

-- N.B. It is of course possible I went looking in the wrong area of StdLib.
--------------------------------------------------------------------------------

module PreROmega.Lib.Biimplication where

open import Function using (_∘_)

record Equivalence {From To : Set} : Set  where
  field
    to   : From → To
    from : To → From

infix 3 _⇔_

_⇔_ : Set → Set → Set
From ⇔ To = Equivalence {From} {To}

equivalence : ∀ {From To : Set}  →
              (From → To) → (To → From) → From ⇔ To
equivalence to from = record
  { to   = to
  ; from = from
  }

------------------------------------------------------------------------
-- Equivalence is an equivalence relation

-- reflexivity
refl : ∀ {A : Set} → A ⇔ A
refl = record
  { to   = λ x → x
  ; from = λ x → x
  }

-- symmetry
sym : ∀ {From To : Set} →
      From ⇔ To →
      To ⇔ From
sym eq = record
  { from       = to
  ; to         = from
  } where open Equivalence eq

-- transitivity
trans : ∀ {A B C : Set} →
      A ⇔ B →
      B ⇔ C →
      A ⇔ C
trans
  (record { to = AtoB ; from = BtoA })
  (record { to = BtoC ; from = CtoB })
  = record {
      to =  BtoC ∘ AtoB ;
      from = BtoA ∘ CtoB
    }
