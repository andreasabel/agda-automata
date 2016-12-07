{-# OPTIONS --allow-unsolved-metas #-}

open import Library

module _ (A : Set) where

infix   1 _≅_
infix   2 _∋_
infixl  4 _∪_
infixl  6 _·_
infixr 15 _*

-- Altenkirch, Representation of first-order function types as terminal coalgebras
-- Hinze, Generalizing generalized tries
--
--   (List A → Bool)
--     ≅ (1 + A × List A) → Bool
--     ≅ (1 → Bool) × (A × List A) → Bool
--     ≅ Bool × (A → (List A → Bool))
--
--   Trie A ≅ Bool × (A → Trie A)
--
--   (μ X. 1 + A × X) → Bool ≅ ν Y. Bool × (A → Y)
--

-- A decidable language is a decidable set of words aka dictionary aka trie.

record Lang : Set where
  coinductive
  field ν : Bool
        δ : (a : A) → Lang
open Lang

-- Word membership (by induction on word)

_∋_ : Lang → (List A → Bool)
l ∋ []     = ν l
l ∋ a ∷ as = δ l a ∋ as

-- Language from word membership (by coinduction)

trie : (List A → Bool) → Lang
ν (trie mem)   = mem []
δ (trie mem) a = trie λ as → mem (a ∷ as)

-- This makes Lang isomophic to (List A → Bool)

-- Constructions of language

-- empty language

∅ : Lang
ν ∅   = false
δ ∅ a = ∅

-- language consisting of the empty word

ε : Lang
ν ε   = true
δ ε a = ∅

-- union of languages

_∪_ : (k l : Lang) → Lang
ν (k ∪ l)   = ν k ∨ ν l
δ (k ∪ l) a = δ k a ∪ δ l a

-- concatenation of languages

{-# TERMINATING #-}
_·_ : (k l : Lang) → Lang
ν (k · l)   = ν k ∧ ν l
δ (k · l) a = if ν k then (δ k a · l) ∪ δ l a else (δ k a · l)

-- Kleene star

{-# TERMINATING #-}
_* : Lang → Lang
ν (l *) = true
δ (l *) a = δ l a · (l *)


-- Bisimilarity

record _≅_ (l k : Lang) : Set where
  coinductive
  field
    ≅ν : ν l ≡ ν k
    ≅δ : (a : A) → δ l a ≅ δ k a
open _≅_ public

-- Equivalence relation laws

≅refl : ∀{l} → l ≅ l
≅ν ≅refl = refl
≅δ ≅refl a = ≅refl

≅sym : ∀{k l} (p : l ≅ k) → k ≅ l
≅ν (≅sym p)   = sym (≅ν p)
≅δ (≅sym p) a = ≅sym (≅δ p a)

≅trans : ∀{k l m} (p : k ≅ l) (q : l ≅ m) → k ≅ m
≅ν (≅trans p q) = trans (≅ν p) (≅ν q)
≅δ (≅trans p q) a = ≅trans (≅δ p a) (≅δ q a)

-- Setoid

≅isEquivalence : IsEquivalence _≅_
IsEquivalence.refl  ≅isEquivalence = ≅refl
IsEquivalence.sym   ≅isEquivalence = ≅sym
IsEquivalence.trans ≅isEquivalence = ≅trans

Bis : Setoid lzero lzero
Setoid.Carrier       Bis = Lang
Setoid._≈_           Bis = _≅_
Setoid.isEquivalence Bis = ≅isEquivalence


union-cong : ∀{k k' l l' : Lang} (p : k ≅ k') (q : l ≅ l') → (k ∪ l) ≅ (k' ∪ l')
≅ν (union-cong p q) rewrite ≅ν p | ≅ν q = refl
≅δ (union-cong p q) a = union-cong (≅δ p a) (≅δ q a)


{-# TERMINATING #-}
dist : (k {l m} : Lang) → k · (l ∪ m) ≅ (k · l) ∪ (k · m)

≅ν (dist k) = ∧-∨-distribˡ (ν k) _ _

≅δ (dist k) a with ν k

≅δ (dist k {l} {m}) a | true = begin

    δ k a · (l ∪ m) ∪ (δ l a ∪ δ m a)         ≈⟨ union-cong (dist (δ k a)) {!!} ⟩
    (δ k a · l ∪ δ k a · m) ∪ (δ l a ∪ δ m a) ≈⟨ {!!} ⟩
    (δ k a · l ∪ δ l a) ∪ (δ k a · m ∪ δ m a)
  ∎
  where open EqR Bis

≅δ (dist k) a | false = dist (δ k a)
