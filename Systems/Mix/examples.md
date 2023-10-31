# Translating Rω terms to Ix

## Kinds

Introduce sorts 𝓤₁ and 𝓤₂ to Ix such that `𝓤₁ : 𝓤₂` and `τ : 𝓤₁` for all "small types" τ. I'll decide what this means later---I am for now just trying to avoid `★ : ★`.

### Types & type constructors

Rω kinds denote to Ix types.

```
⟦ ★ ⟧ = 𝓤₁
```

Where we let 𝓤₁ and 𝓤₂ exist in the type AST.

### Label kinds

Simply let

```
⟦ L ⟧ = ⊤
```

where 
```
tt : ⊤ : 𝓤₁
```

(Although this may need to be 𝓤₂?)


### Row Kinds

Let `Π τ. υ` be a meta-synonym for `Π _ : τ. υ` and `Row` be a meta-synonym defined as:

```
Row κ = (Σ i : Nat. Π _ : Ix i. κ).
```

Then 
```
⟦ R[ ⋆ ] ⟧ = Row 𝓤₁
⟦ R[ κ₁ → κ₂ ] ⟧ = Row (Π ⟦ κ₁ ⟧. ⟦ κ₂ ⟧)
```

e.g.

```
⟦ R[ ★ → ★ ] ⟧ = (∃ i : Nat. Π Ix i. Π 𝓤₁. 𝓤₁)
```

I think any higher order business, like the type above, must have type 𝓤₂. So, as is standard, quantification over 𝓤₁ bumps the level to 𝓤₂. I do not know if we need to permit quantification over 𝓤₂.

## Types
...

## Predicates
...

### Containment
Suppose the Rω rows `ρ₁ ρ₂ : R[ κ ]` translate to

```agda
  (z₁ z₂ : Row ⟦ κ ⟧).
```

Then

```
  ⟦ ρ₁ ≲ ρ₂ ⟧ = 
  Π (i : Ix z₁.1). Σ (j : Ix z₂.1). (z₁.2 i ~ z₂.2 j)
```

N.b. Type equality in Ix must be higher order. Consider
```
(z₁.2 i ~ z₂.2 j)
``` 
when `z₁` and `z₂` have type `Row (Π 𝓤₁. 𝓤₁)`. So we need some notion of functional equivalence for predicate decidability.


### Combination
Suppose the Rω rows `ρ₁ ρ₂ ρ₃ : R[ κ ]` translate to

```agda
  (z₁ z₂ z₃ : Row ⟦ κ ⟧).
```

Then

```
  ⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧ = 
  all z₃ from z₁ or z₂
  ×
  (z₁ ≲ z₃)
  ×
  (z₂ ≲ z₃)
```

where

```agda
  all_from_or_ =
  λ z₁ z₂ z₃ : Row ⟦ κ ⟧.
  ∀ i : Ix z₃.1.
  ∃ j : Ix z₃.1. (z₁.2 j ~ z₃.2 i)
   Or
  ∃ j : Ix z₂.1. (z₂.2 j ~ z₃.2 i)	
```

## Terms

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
