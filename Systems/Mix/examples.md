Let's consider some example translations.

## Primitives
### Concatenation

```agda
concat : ∀ (z₁ z₂ z₃ : R[★]). z₁ · z₂ ~ z₃ ⇒ Π z₁ → Π z₂ → Π z₃
concat = Λ z₁ z₂ z₃ : R[ ★ ]. 
	     ƛ p : z₁ · z₂ ~ z₃.
		 λ (r : Π z₁) (v : Π z₂).
		 r ++ v.
```		 

↝

```agda
with kind:
  concat : ∀ⁱ n. ★
and type:
  concat : ∀ⁱ m n l. 
           ∀ (z₁ : Ix m  → ★) ∀ (z₂ : Ix n → ★).∀ (z₃ : Ix l → ★).
             ⟦ z₁ · z₂ ~ z₃ ⟧ → 
             (∀ (i : Ix m) → z₁ i)
             (∀ (i : Ix n) → z₂ i)
             ∀ (i : Ix l).   z₃ i
For less writing, let's assume we are working in a row theory
in which the meaning of row concatenation is a map from indices 
in z₁ and z₂ to z₃. Then:

  ⟦ z₁ · z₂ ~ z₃ ⟧ = 
  ∀ i : Ix l.
  ∃ j : Ix m. (z₁ j = z₃ i)
   Or
  ∃ j : Ix n. (z₂ j = z₃ i)	
  


Then we have the term:
  concat = λⁱ m n n. 
           Λ (z₁ : Ix m  → ★). Λ (z₂ : Ix n → ★). Λ (z₃ : Ix l → ★).
	       λ p : ⟦ z₁ · z₂ ~ z₃ ⟧. 
     	   λ (r : (∀ (i : Ix m) → z₁ i)). 
		   λ (v : (∀ (i : Ix n) → z₂ i)).
		   Λ (i : Ix l).
		   -- (N.b. need term level discrimination on existential types.)
		   case p i of        
		     -- Need J eliminator *that can write eq : z₁ i = z₃ i.
		     left  (j , eq) → J (r j) eq
			 right (j , eq) → J (v j) eq
		   
```
