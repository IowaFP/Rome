## Problems. Dec 18, 2024


### In need of more reductions
We should expect that (F ↑) · (l ▹ τ) is not in normal form, however it is if we
classify _↑ as a congruence rule for forming neutral types:

  ```agda
    _↑ : 

      NeutralType Δ (κ₁ `→ κ₂) →
      ------------------------------
      NeutralType Δ (R[ κ₁ ] `→ R[ κ₂ ])
  ```
  
### The normality of F (μ F) as a type
I've changed the definition of μ to take F : Set → Set rather than be a binding
site---but we later want terms to be indexed by NormalTypes, and F (μ F) is
not necessarily in normal form (it is so only if F is neutral). Consider a
term indexed by F (μ F) for F := λ X. (1 + X). So F (μ F) == 1 + (μ F). This
could be resolved by changing μ back to a binding site---but this messes up
the presentation of types in Rome such as μ (Σ (Z ▹ λ X. ⊤, S ▹ λ X. X)).
  
### Uninhabitable types

Chapmen et al determine that the strongest property they want normalization to
have is *stability*, which implies idempotency and surjectivity. Below, ⇓
normalizes from Type to NormalType and ⇑ retracts NormalTypes back to
Types. (For bonus points, what categorical relationship is *stability* stating ⇑
and ⇓ have as arrows?)  

```agda 
stability : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → reflect (⇑NE τ) idEnv ≡ reflectNE τ
idempotency : ∀ (τ : Types.Type Δ κ) → (⇑ (⇓ (⇑ (⇓ τ)))) ≡ ⇑ (⇓ τ) 
idempotency τ rewrite stability (⇓ τ) = refl 
surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ) 
surjectivity τ = ⟨ ⇑ τ , stability τ ⟩
``` 

Satisfying this property is the criteria I am using to specify that we have
accurately characterized both (i) normal forms of types in Rome and (ii) the
semantic domain into which types are reflected. I think that nonsensical types
forms some crud in the waters that will block stability. So I need/want a way to
rule out the formation of e.g.

Π Π (ℓ₁ ▹ ℓ₂ ▹ τ)) 

and possibly many other types. Or, I should force that nonsense normalizes to
not nonsense---e.g., that

  Π Π (ℓ₁ ▹ ℓ₂ ▹ τ)
  
reduces to

  Π (ℓ₁ ▹ (Π (ℓ₂ ▹ τ)).
  
I suspect I want my normal forms of records to be Π x for neutral term x and Π
(ℓ ▹ τ) for τ normal otherwise.  I would like a row to be either a variable or
of the form (ℓ ▹ τ).
