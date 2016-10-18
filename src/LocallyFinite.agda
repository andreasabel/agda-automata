open import Library

module LocallyFinite
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A; refl to ≈refl)) where

open import Language decA

-- Do all nodes of a trie satisfy a predicate?

record All (P : Lang ∞ → Set) (ℓ : Lang ∞) : Set where
  coinductive
  field here : P ℓ
        δ    : (a : A) → All P (Lang.δ ℓ a)

-- A tree is locally finite if on any path it only has finitely many subtrees

_Or_ : (P : Lang ∞ → Set) (ℓ : Lang ∞) → Lang ∞ → Set
(P Or ℓ) k = P k ⊎ (k ≅ ℓ)

data LocallyFinite' (P : Lang ∞ → Set) (ℓ : Lang ∞) : Set where
  now   : All P ℓ → LocallyFinite' P ℓ
  later : ((a : A) → LocallyFinite' (P Or ℓ) (Lang.δ ℓ a)) → LocallyFinite' P ℓ

LocallyFinite : Lang ∞ → Set
LocallyFinite = LocallyFinite' (λ ℓ → ⊥)

record LocallyInfinite' (P : Lang ∞ → Set) (ℓ : Lang ∞) : Set where
  coinductive
  field notNow       : ¬ (P ℓ)
        counterChild : A
        notLater     : LocallyInfinite' (P Or ℓ) (Lang.δ ℓ counterChild)
open LocallyInfinite'

inf-not-fin : ∀{P ℓ} → LocallyInfinite' P ℓ → ¬ (LocallyFinite' P ℓ)
inf-not-fin p (now q)   = notNow p (All.here q)
inf-not-fin p (later q) = inf-not-fin (notLater p) (q (counterChild p))

-- The opposite direction is not provable constructively
-- as we would have to guess the infinite counterexample.
--
-- not-fin-inf : ∀{P ℓ} → ¬ (LocallyFinite' P ℓ) → LocallyInfinite' P ℓ

LessThenBs : (a b : A) (n : ℕ) (ℓ : Lang ∞) → Set
LessThenBs a b zero ℓ = ⊥
LessThenBs a b (suc n) = LessThenBs a b n Or thenbs a b n

lemma : ∀{a b} n m → ¬ (LessThenBs a b n (thenbs a b (m + n)))
lemma zero    m p = p
lemma (suc n) m (inj₁ p) = {!lemma n (suc m) {! p !}!}--  ¬ (LessThenBs .a .b n (thenbs .a .b (suc n)))
lemma (suc n) m (inj₂ p) = {!!} -- ¬ (thenbs .a .b (m + suc n) ≅ thenbs .a .b n)

lemma' : ∀{a b} n → ¬ (LessThenBs a b n (thenbs a b n))
lemma' zero p = p
lemma' (suc n) (inj₁ p) = {!!}--  ¬ (LessThenBs .a .b n (thenbs .a .b (suc n)))
lemma' (suc n) (inj₂ p) = {!!} -- ¬ (thenbs .a .b (suc n) ≅ thenbs .a .b n)

thm : ∀ a b n → LocallyInfinite' (LessThenBs a b n) (thenbs a b n)
notNow (thm a b n) p = {!!}
counterChild (thm a b n) = a
notLater (thm a b n) with a ≟ a
notLater (thm a b n) | yes p = thm a b (suc n)
notLater (thm a b n) | no ¬p = ⊥-elim (¬p ≈refl)
