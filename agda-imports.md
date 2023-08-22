Reference to oft-imported imports whose locations I usually forget.

## Levels

```agda
open import Agda.Primitive
```

## Decidability

```agda
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
```

## Eq & Eq Reasoning

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
```

## Data Types

```agda
open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.String
open import Dat.Maybe using (Maybe ; just ; nothing)
```

## Monadic business

Typically import `*.Categorical`, e.g.,
```agda
open import Data.Maybe
open import Data.Maybe.Categorical
```

