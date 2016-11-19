{-# OPTIONS --allow-unsolved-metas #-}

open import Library

module Automaton
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

  -- Lifting to lists
  νs : (ss : List S) → Bool
  νs ss = List.any ν ss

  δs : (ss : List S) (a : A) → List S
  δs ss a = List.map (λ s → δ s a) ss

open DAut public using (νs; δs)

-- Language accepted by an automaton

module _ {S} (da : DAut S) (open DAut da) where

  -- Word acceptance from a state

  accept : (s : S) (as : List A) → Bool
  accept s [] = ν s
  accept s (a ∷ as) = accept (δ s a) as

  -- Language accepted by a state.
  -- The terminal morphism aka coiteration.

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
DAut.ν (acomposeA da₁ f da₂) (s₁ , s₂)   = DAut.ν da₁ s₁ ∧ DAut.ν da₂ (f s₂) ∨ DAut.ν da₂ s₂
DAut.δ (acomposeA da₁ f da₂) (s₁ , s₂) a = DAut.δ da₁ s₁ a , DAut.δ da₂ s₂' a
  where s₂' = if DAut.ν da₁ s₁ then f s₂ else s₂

-- Finite powerset automaton with lists (alt: finite sets).

powA : ∀{S} (da : DAut S) → DAut (List S)
DAut.ν (powA da) ss   = DAut.νs da ss
DAut.δ (powA da) ss a = DAut.δs da ss a

-- Automaton composition
-- We need an initial state of the second automaton to glue them together.
-- We could also allow a list of initial states of the second automaton.

composeA : ∀{S₁ S₂} (da₁ : DAut S₁) (s₀ : S₂) (da₂ : DAut S₂) → DAut (S₁ × List S₂)
composeA da₁ s₀ da₂ = acomposeA da₁ (_∷_ s₀) (powA da₂)

composeA' : ∀{S₁ S₂} (da₁ : DAut S₁) (s₀ : S₂) (da₂ : DAut S₂) → DAut (S₁ × List S₂)
DAut.ν (composeA' da₁ s₀ da₂) (s₁ , ss₂)   = (DAut.ν da₁ s₁ ∧ DAut.ν da₂ s₀) ∨ DAut.νs da₂ ss₂
DAut.δ (composeA' da₁ s₀ da₂) (s₁ , ss₂) a = DAut.δ da₁ s₁ a , DAut.δs da₂ (if DAut.ν da₁ s₁ then s₀ ∷ ss₂ else ss₂) a


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

------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------

-- Automaton for empty language is correct

∅A-correct : ∀{i} → acclang ∅A _ ≅⟨ i ⟩≅ ∅
≅ν ∅A-correct = refl
≅δ ∅A-correct a = ∅A-correct

-- Automaton for single character language is correct

charA-err-correct : ∀{i a} → acclang (charA a) err ≅⟨ i ⟩≅ ∅
≅ν charA-err-correct = refl
≅δ charA-err-correct _ = charA-err-correct

charA-acc-correct : ∀{i a} → acclang (charA a) acc ≅⟨ i ⟩≅ ε
≅ν charA-acc-correct = refl
≅δ charA-acc-correct _ = charA-err-correct

charA-correct : ∀{i} (a : A) → acclang (charA a) init ≅⟨ i ⟩≅ char a
≅ν (charA-correct a) = refl
≅δ (charA-correct a) a₁ with a ≟ a₁
≅δ (charA-correct a) a₁ | yes p = charA-acc-correct
≅δ (charA-correct a) a₁ | no ¬p = charA-err-correct

-- Union automaton is correct

unionA-correct : ∀{i S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) (s₁ : S₁) (s₂ : S₂) →
  acclang da₁ s₁ ∪ acclang da₂ s₂ ≅⟨ i ⟩≅ acclang (da₁ ⊕ da₂) (s₁ , s₂)
≅ν (unionA-correct da₁ da₂ s₁ s₂) = refl
≅δ (unionA-correct da₁ da₂ s₁ s₂) a = unionA-correct da₁ da₂ (DAut.δ da₁ s₁ a) (DAut.δ da₂ s₂ a)

-- Power construction preserves semantics

powA-nil : ∀{i S} (da : DAut S) → acclang (powA da) [] ≅⟨ i ⟩≅ ∅
≅ν (powA-nil da)   = refl
≅δ (powA-nil da) a = powA-nil da

powA-cons : ∀{i S} (da : DAut S) {s : S} {ss : List S} →
  acclang (powA da) (s ∷ ss) ≅⟨ i ⟩≅ acclang da s ∪ acclang (powA da) ss
≅ν (powA-cons da) = refl
≅δ (powA-cons da) a = powA-cons da -- (DAut.δ da s a) (DAut.δ (powA da) ss a)

powA-correct : ∀{i S} (da : DAut S) (s : S) → acclang (powA da) (s ∷ []) ≅⟨ i ⟩≅ acclang da s
≅ν (powA-correct da s) with DAut.ν da s
... | true = refl
... | false = refl
≅δ (powA-correct da s) a = powA-correct da (DAut.δ da s a)

fact : ∀ a {b c} → (a ∧ (b ∨ c)) ∨ c ≡ (a ∧ b) ∨ c
fact a {b} {c} = begin
  (a ∧ (b ∨ c)) ∨ c       ≡⟨ ∨-∧-distribʳ c a _ ⟩
  (a ∨ c) ∧ ((b ∨ c) ∨ c) ≡⟨ ∧-cong (refl {x = (a ∨ c)}) (∨-assoc b c c) ⟩
  (a ∨ c) ∧ (b ∨ (c ∨ c)) ≡⟨ ∧-cong (refl {x = a ∨ c}) (∨-cong (refl {x = b}) (∨-idem c)) ⟩
  (a ∨ c) ∧ (b ∨ c)       ≡⟨ sym (∨-∧-distribʳ c a b) ⟩
  (a ∧ b) ∨ c
  ∎ where open ≡-Reasoning

composeA-gen : ∀{i S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) (s₁ : S₁) (s₂ : S₂) (ss : List S₂) →
  acclang (composeA da₁ s₂ da₂) (s₁ , ss) ≅⟨ i ⟩≅ acclang da₁ s₁ · acclang da₂ s₂ ∪ acclang (powA da₂) ss
≅ν (composeA-gen da₁ da₂ s₁ s₂ ss) = fact (DAut.ν da₁ s₁)
≅δ (composeA-gen da₁ da₂ s₁ s₂ ss) a with DAut.ν da₁ s₁

... | true  = begin

    acclang (acomposeA da₁ (_∷_ s₂) (powA da₂))
      (DAut.δ da₁ s₁ a , DAut.δ da₂ s₂ a ∷ DAut.δs da₂ ss a)

  ≈⟨  composeA-gen da₁ da₂ (DAut.δ da₁ s₁ a) s₂ (DAut.δs da₂ (s₂ ∷ ss) a) ⟩

    acclang da₁ (DAut.δ da₁ s₁ a) · acclang da₂ s₂ ∪
      acclang (powA da₂) (δs da₂ (s₂ ∷ ss) a)

  ≈⟨  union-congʳ (powA-cons da₂) ⟩

     acclang da₁ (DAut.δ da₁ s₁ a) · acclang da₂ s₂ ∪
      (acclang da₂ (DAut.δ da₂ s₂ a) ∪ acclang (powA da₂) (DAut.δs da₂ ss a))

  ≈⟨  ≅sym (union-assoc _) ⟩

     acclang da₁ (DAut.δ da₁ s₁ a) · acclang da₂ s₂ ∪
      acclang da₂ (DAut.δ da₂ s₂ a) ∪ acclang (powA da₂) (DAut.δs da₂ ss a)

  ∎ where open EqR (Bis _)

... | false = composeA-gen da₁ da₂ (DAut.δ da₁ s₁ a) s₂ (DAut.δs da₂ ss a)


composeA-correct : ∀{i S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) (s₁ : S₁) (s₂ : S₂) →

  acclang (composeA da₁ s₂ da₂) (s₁ , []) ≅⟨ i ⟩≅ acclang da₁ s₁ · acclang da₂ s₂

composeA-correct da₁ da₂ s₁ s₂ = begin
  acclang (composeA da₁ s₂ da₂) (s₁ , [])                 ≈⟨  composeA-gen da₁ da₂ s₁ s₂ [] ⟩
  acclang da₁ s₁ · acclang da₂ s₂ ∪ acclang (powA da₂) [] ≈⟨ union-congʳ (powA-nil da₂) ⟩
  acclang da₁ s₁ · acclang da₂ s₂ ∪ ∅                     ≈⟨ union-comm _ _ ⟩
  ∅ ∪ acclang da₁ s₁ · acclang da₂ s₂                     ≈⟨ union-emptyˡ ⟩
  acclang da₁ s₁ · acclang da₂ s₂
  ∎ where open EqR (Bis _)

-- Conversion
------------------------------------------------------------------------

-- We can convert the state set to an isomorphic one.

convA : ∀{S S'} (iso : S ↔ S') (da : DAut S) → DAut S'
DAut.ν (convA iso da) s' = DAut.ν da (Inverse.from iso Π.⟨$⟩ s' )
DAut.δ (convA iso da) s' a = Inverse.to iso Π.⟨$⟩ (DAut.δ da) (Inverse.from iso Π.⟨$⟩ s') a

-- Conversion does not change the semantics.

-- The recognized language from each state is still the same
-- (when starting from the corresponding state).

convA-correct : ∀{i S S'} (iso : S ↔ S') (da : DAut S) (let da' = convA iso da) (s : S)
  → acclang da s ≅⟨ i ⟩≅ acclang da' (Inverse.to iso Π.⟨$⟩ s)
≅ν (convA-correct iso da s)   rewrite _InverseOf_.left-inverse-of (Inverse.inverse-of iso) s
  = refl
≅δ (convA-correct iso da s) a rewrite _InverseOf_.left-inverse-of (Inverse.inverse-of iso) s
  = convA-correct iso da (DAut.δ da s a)


-- Finite automata

powDFA-correct : ∀{i n} (da : DFAut n) (ss : List (Fin n)) →
  acclang (powDFA da) (Vec.elemSet ss) ≅⟨ i ⟩≅ acclang (powA da) ss
≅ν (powDFA-correct da ss) = {!!}
≅δ (powDFA-correct da ss) a = {!!}
