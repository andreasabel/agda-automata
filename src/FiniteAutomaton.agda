open import Library

module _
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA hiding (ν; δ)

-- Automaton

-- Following Rutten, we only represent the fixed parts of the automaton
-- (acceptance condition and transition function).
-- The state the automaton is in (like the initial state) is represented
-- outside.

record DAut (S : Set) : Set where
  field
    ν : (s : S) → Bool
    δ : (s : S) (a : A) → S

-- Language accepted by an automaton

module _ {S} (da : DAut S) (open DAut da) where

  -- Word acceptance from a state

  accept : (s : S) (as : List A) → Bool
  accept s [] = ν s
  accept s (a ∷ as) = accept (δ s a) as

  -- Language accepted by a state.
  -- The terminal morphism.

  acclang : ∀{i} (s : S) → Lang i
  Lang.ν (acclang s) = ν s
  Lang.δ (acclang s) a = acclang (δ s a)

-- An automaton recognizing the empty language

∅A : DAut ⊤
DAut.ν ∅A s = false
DAut.δ ∅A s a = _

-- An automaton recognizing the trivial language

allA : DAut ⊤
DAut.ν allA s = true
DAut.δ allA s a = _

-- An automaton recognizing only the empty word.  (Or nothing.)

εA : DAut Bool
DAut.ν εA b = b
DAut.δ εA b a = false

-- An automaton recognizing a single word consisting of a single character.
-- nothing is the error state, just false the initial state, just true the accepting state.

charA' : (a : A) → DAut (Maybe Bool)
DAut.ν (charA' a) (just b) = b
DAut.ν (charA' a) nothing = false
DAut.δ (charA' a) (just false) x with a ≟ x
DAut.δ (charA' a) (just false) x | yes p = just true
DAut.δ (charA' a) (just false) x | no ¬p = nothing
DAut.δ (charA' a) (just true) x = nothing
DAut.δ (charA' a) nothing _ = nothing

data 3States : Set where
  init acc err : 3States

charA : (a : A) → DAut 3States
DAut.ν (charA a) init = false
DAut.ν (charA a) acc = true
DAut.ν (charA a) err = false
DAut.δ (charA a) init a₁ = if ⌊ a ≟ a₁ ⌋ then acc else err
DAut.δ (charA a) acc a₁ = err
DAut.δ (charA a) err a₁ = err

-- The complement automaton

complA : ∀{S} (da : DAut S) → DAut S
DAut.ν (complA da) s = not (DAut.ν da s)
DAut.δ (complA da) s a = DAut.δ da s a

-- A product automaton recognizing intersection

_⊗_ : ∀{S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) → DAut (S₁ × S₂)
DAut.ν (da₁ ⊗ da₂) (s₁ , s₂)   = DAut.ν da₁ s₁ ∧ DAut.ν da₂ s₂
DAut.δ (da₁ ⊗ da₂) (s₁ , s₂) a = DAut.δ da₁ s₁ a , DAut.δ da₂ s₂ a

-- A product automaton recognizing union

_⊕_ : ∀{S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) → DAut (S₁ × S₂)
DAut.ν (da₁ ⊕ da₂) (s₁ , s₂)   = DAut.ν da₁ s₁ ∨ DAut.ν da₂ s₂
DAut.δ (da₁ ⊕ da₂) (s₁ , s₂) a = DAut.δ da₁ s₁ a , DAut.δ da₂ s₂ a

-- Automaton composition is not trivial for DFAs.
-- It is easy for NFAs.  It is also easy to compose a DFA with an NFA.

-- Abstract automaton composition

acomposeA : ∀{S₁ S₂} (da₁ : DAut S₁) (f : S₂ → S₂) (da₂ : DAut S₂) → DAut (S₁ × S₂)
DAut.ν (acomposeA da₁ f da₂) (s₁ , s₂)   = DAut.ν da₁ s₁ ∨ DAut.ν da₂ s₂
DAut.δ (acomposeA da₁ f da₂) (s₁ , s₂) a = DAut.δ da₁ s₁ a , (if DAut.ν da₁ s₁ then f s₂' else s₂')
  where s₂' = DAut.δ da₂ s₂ a

-- Finite powerset automaton with lists (alt: finite sets).

powA : ∀{S} (da : DAut S) → DAut (List S)
DAut.ν (powA da) ss   = List.any (DAut.ν da) ss
DAut.δ (powA da) ss a = List.map (λ s → DAut.δ da s a) ss

-- Automaton composition
-- We need an initial state of the second automaton to glue them together.
-- We could also allow a list of initial states of the second automaton.

composeA : ∀{S₁ S₂} (da₁ : DAut S₁) (s₀ : S₂) (da₂ : DAut S₂) → DAut (S₁ × List S₂)
composeA da₁ s₀ da₂ = acomposeA da₁ (_∷_ s₀) (powA da₂)

composeA' : ∀{S₁ S₂} (da₁ : DAut S₁) (s₀ : S₂) (da₂ : DAut S₂) → DAut (S₁ × List S₂)
DAut.ν (composeA' da₁ s₀ da₂) (s₁ , s₂)   = DAut.ν da₁ s₁ ∨ List.any (DAut.ν da₂) s₂
DAut.δ (composeA' da₁ s₀ da₂) (s₁ , s₂) a = DAut.δ da₁ s₁ a , (if DAut.ν da₁ s₁ then s₀ ∷ ss else ss)
  where ss = List.map (λ s → DAut.δ da₂ s a) s₂

-- WRONG:
-- composeA' : ∀{S₁ S₂} (da₁ : DAut S₁) (s₀ : S₂) (da₂ : DAut S₂) → DAut (S₁ ⊎ (S₁ × S₂))
-- DAut.ν (composeA' da₁ s₀ da₂) (inj₁ s₁) = DAut.ν da₁ s₁
-- DAut.ν (composeA' da₁ s₀ da₂) (inj₂ (s₁ , s₂)) = DAut.ν da₁ s₁ ∨ DAut.ν da₂ s₂
-- DAut.δ (composeA' da₁ s₀ da₂) (inj₁ s₁) a = if DAut.ν da₁ s₁ then inj₂ (DAut.δ da₁ s₁ a , s₀) else inj₁ (DAut.δ da₁ s₁ a)
-- DAut.δ (composeA' da₁ s₀ da₂) (inj₂ (s₁ , s₂)) a = inj₂ (DAut.δ da₁ s₁ a , DAut.δ da₂ s₂ a)

-- Finite automata

DFAut : (n : ℕ) → Set
DFAut n = DAut (Fin n)

-- Powerset automaton

powDFA : ∀{n} (dfa : DFAut n) → DAut (Vec Bool n)
DAut.ν (powDFA dfa) s = Vec.any (Vec.zipWith _∧_ s (Vec.tabulate (DAut.ν dfa)))
DAut.δ (powDFA dfa) s a = Vec.∨-permute s (λ i → DAut.δ dfa i a)
