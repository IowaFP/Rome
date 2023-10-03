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
concat : ∀ n : ℕ. (z₁ z₂ z₃ : Σ[ n ∈ ℕ ](Fin n → Type)).
	     (∀ (i : Fin n) → 
		 (can inject from left to right) × (can inject from right to left) 
		 
```

A thing to note: Rωμ will have types. μix will have types. Rows, in μix, are finite mappings
to types. To which types do we denote, here?

```

Kinds  κ  ::= Type ∣ Fin n | ...
Types τ υ ::= α ∣ (→) ∣ λα:κ. τ ∣ τ υ | ⊤
            ∣ ∀α:κ. τ 
			∣ ∀ (i : Fin n). τ   -- Quantification over finite indices.
			∣ ∃ (i : Fin n). τ
			| τ ≡ υ 
terms M N ::= x ∣ λ x : τ. M ∣ M N ∣ Λ α : κ. M ∣ M 			

```


		 

## Wand's Problem

Consider, in Rω:

w : ∀ (z₁ z₂ z₃ : R[★]) (t : ★) (l : L)
      z₁ + z₂ ~ z₃ , {l ▹ t} ≲ z₃ ⇒
