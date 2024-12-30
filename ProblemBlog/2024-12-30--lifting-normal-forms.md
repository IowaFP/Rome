# Row computation _from the left_

We are in a pickle in which neutral forms are not normal. Some examples may be rectified syntactically; some may not. 

## The okay 

Let F : ★ → ★ and τ : ★ and consider first:

```
F · (ℓ ▹ τ)
```

This is ill-kinded, and so we lift F.

```
  (F ↑)  · (ℓ ▹ τ)
↝ (ℓ ▹ F τ)
```

Now F : R[ ★ ] → R[ ★ ] and (ℓ ▹ τ) : R[ ★ ] and so all is well-kinded. More importantly,  (F ↑)  · (ℓ ▹ τ) is syntactically identifiable, which gives us some wiggle room to assert that it is neither neutral nor normal. I suspect we would like to switch back to application-style lifting, for the following reason: it should be the case that (F ↑) is neutral, in which case (F ↑)  · (ℓ ▹ τ) becomes neutral. If we instead mark lifting with application, we get:

```
  ⌈ F ⌉· (ℓ ▹ τ)
↝ (ℓ ▹ F τ)
```

and now it is quite clear that ⌈ F ⌉· (ℓ ▹ τ) is not neutral---it's not strictly an application!

## The bad

Okay. Now let F : R[ ★ ] → R[ ★ ] and let τ : ★. Then:

```
F · (ℓ ▹ τ)
```

is certainly well kinded and certainly should reduce. Yet it is in neutral form! I'm left to conclude (from this example and some others) that we must be careful to partition our types based on "maybe row kinded" and "not row kinded". Here is the rule for declaring neutral applications:

```agda
  _·_ : 
      
      NeutralType Δ (κ₁ `→ κ) → 
      NormalType Δ κ₁ → 
      ---------------------------
      NeutralType Δ κ
```

We may instead want this to be:

```agda
data NeutralType ... where
  ...
  
  _·_ :
      
      NoRows (κ₁ `→ κ) →
      NeutralType Δ (κ₁ `→ κ) → 
      NormalType Δ κ₁ → 
      ---------------------------
      NeutralType Δ κ
```

Or something to that effect. A predicate like `NoRows` is kind of stupid, but it gets the point across. Better might be to stratify our kind system.

``` agda
data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  
data RowKind : Set where
  ι    : Kind → RowKind
  R[_] : RowKind → RowKind
```

Here ι injects/instantiates regular kinds to RowKind and R[_] builds row kinds. You may still have nested rows this way, e.g.:

```
R[ R[ ι ★ ] ]
```

If you want to remove nested rows entirely (a radical simplification that (i) makes the work less interesting but (ii) makes the mechanization much easier), you could instead stratify according to:

```agda
data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  
data RowKind : Set where
  ι    : Kind → RowKind
  R[_] : Kind → RowKind
```


