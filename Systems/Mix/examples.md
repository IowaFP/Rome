Let's consider some example translations of Rω types and terms to (what we
imagine will be) the recursive index calculus.

## Primitives
### Concatenation

```agda
concat : ★
concat : ∀ (z₁ z₂ z₃ : R[★]). z₁ · z₂ ~ z₃ ⇒ Π z₁ → Π z₂ → Π z₃
concat = Λ z₁ z₂ z₃ : R[ ★ ]. 
	     ƛ p : z₁ · z₂ ~ z₃.
		 λ (r : Π z₁) (v : Π z₂).
		 r ++ v.
```		 

And, to Mix:

```agda
  concat : Π (z₁ : (Σ m : Nat. Ix m → ★)).
           Π (z₂ : (Σ n : Nat. Ix n → ★)).
           Π (z₃ : (Σ l : Nat. Ix l → ★)).
             ⟦ z₁ · z₂ ~ z₃ ⟧ → 
             (∀ (i : Ix z₁.1) → z₁.2 i)
             (∀ (i : Ix z₂.1) → z₂.2 i)
             ∀ (i : Ix z₃.1).   z₃.2 i
```			 

where 
```
  ⟦ z₁ · z₂ ~ z₃ ⟧ = 
  ∀ i : Ix z₃.1.
  ∃ j : Ix z₃.1. (z₁.2 j = z₃.2 i)
   Or
  ∃ j : Ix z₂.1. (z₂.2 j = z₃.2 i)	
```


Then we have the term:
```
  concat = λ z₁ : (Σ m : Nat. Ix m → ★)).
           λ z₂ : (Σ n : Nat. Ix n → ★)).
           λ z₃ : (Σ l : Nat. Ix l → ★)).
		   λ P : ⟦ z₁ · z₂ ~ z₃ ⟧.
		   λ r : (Π (i : Ix z₁.1) → z₁.2 i).
		   λ v : (Π (i : Ix z₂.1) → z₂.2 i).
		   λ i : Ix z₃.1.
           case P i of
	         left  (j , eq) → J (r j) eq
			 right (j , eq) → J (v j) eq
```
