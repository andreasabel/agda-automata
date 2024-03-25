{-# OPTIONS --sized-types --allow-unsolved-metas #-}

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

  lang : ∀{i} (s : S) → Lang i
  Lang.ν (lang s) = ν s
  Lang.δ (lang s) a = lang (δ s a)

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


-- Kleene star

-- 1. add initial state to the final states
-- 2. from each final state we can also make the transitions from the initial state

module Star (decS : DecSetoid lzero lzero) where
  open DecSetoid decS public using () renaming (Carrier to S) -- ; _≟_ to
  open DecSetoid decS renaming (_≟_ to _==_; refl to reflS)

  _≡ˢ_ : (s₁ s₂ : S) → Bool
  s₁ ≡ˢ s₂ = ⌊  s₁ == s₂ ⌋

  diag : ∀ s → (s ≡ˢ s) ≡ true
  diag s with s == s
  ... | yes q = refl
  ... | no  q = ⊥-elim (q reflS)

  -- Make a new initial state which is also final.
  -- The new accepting state is `nothing` and has the transitions from s₀.
  acceptingInitial : (s₀ : S) (da : DAut S) → DAut (Maybe S)
  DAut.ν (acceptingInitial s₀ da) nothing      =  true
  DAut.ν (acceptingInitial s₀ da) (just s)     =  DAut.ν da s
  DAut.δ (acceptingInitial s₀ da) nothing   a  =  just (DAut.δ da s₀ a)
  DAut.δ (acceptingInitial s₀ da) (just s)  a  =  just (DAut.δ da s a)

  finalToInitial : (da : DAut (Maybe S)) → DAut (List (Maybe S))
  DAut.ν (finalToInitial da) ss   = DAut.νs da ss
  DAut.δ (finalToInitial da) ss a =
    let ss' = DAut.δs da ss a
    in  if DAut.νs da ss then DAut.δ da nothing a ∷ ss' else ss'

  starA : (s₀ : S) (da : DAut S) → DAut (List (Maybe S))
  starA s₀ da = finalToInitial (acceptingInitial s₀ da)


------------------------------------------------------------------------
-- Proofs
------------------------------------------------------------------------

-- Automaton for empty language is correct

∅A-correct : ∀{i} → lang ∅A _ ≅⟨ i ⟩≅ ∅
≅ν ∅A-correct = refl
≅δ ∅A-correct a = ∅A-correct

-- Automaton for single character language is correct

charA-err-correct : ∀{i a} → lang (charA a) err ≅⟨ i ⟩≅ ∅
≅ν charA-err-correct = refl
≅δ charA-err-correct _ = charA-err-correct

charA-acc-correct : ∀{i a} → lang (charA a) acc ≅⟨ i ⟩≅ ε
≅ν charA-acc-correct = refl
≅δ charA-acc-correct _ = charA-err-correct

charA-correct : ∀{i} (a : A) → lang (charA a) init ≅⟨ i ⟩≅ char a
≅ν (charA-correct a) = refl
≅δ (charA-correct a) a₁ with a ≟ a₁
≅δ (charA-correct a) a₁ | yes p = charA-acc-correct
≅δ (charA-correct a) a₁ | no ¬p = charA-err-correct

-- Union automaton is correct

unionA-correct : ∀{i S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) (s₁ : S₁) (s₂ : S₂) →
  lang da₁ s₁ ∪ lang da₂ s₂ ≅⟨ i ⟩≅ lang (da₁ ⊕ da₂) (s₁ , s₂)
≅ν (unionA-correct da₁ da₂ s₁ s₂) = refl
≅δ (unionA-correct da₁ da₂ s₁ s₂) a = unionA-correct da₁ da₂ (DAut.δ da₁ s₁ a) (DAut.δ da₂ s₂ a)

-- Power construction preserves semantics

powA-nil : ∀{i S} (da : DAut S) → lang (powA da) [] ≅⟨ i ⟩≅ ∅
≅ν (powA-nil da)   = refl
≅δ (powA-nil da) a = powA-nil da

powA-cons : ∀{i S} (da : DAut S) {s : S} {ss : List S} →
  lang (powA da) (s ∷ ss) ≅⟨ i ⟩≅ lang da s ∪ lang (powA da) ss
≅ν (powA-cons da) = refl
≅δ (powA-cons da) a = powA-cons da -- (DAut.δ da s a) (DAut.δ (powA da) ss a)

powA-correct : ∀{i S} (da : DAut S) (s : S) → lang (powA da) (s ∷ []) ≅⟨ i ⟩≅ lang da s
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
  lang (composeA da₁ s₂ da₂) (s₁ , ss) ≅⟨ i ⟩≅ lang da₁ s₁ · lang da₂ s₂ ∪ lang (powA da₂) ss
≅ν (composeA-gen da₁ da₂ s₁ s₂ ss) = fact (DAut.ν da₁ s₁)
≅δ (composeA-gen da₁ da₂ s₁ s₂ ss) a with DAut.ν da₁ s₁

... | true  = begin

    lang (acomposeA da₁ (_∷_ s₂) (powA da₂))
      (DAut.δ da₁ s₁ a , DAut.δ da₂ s₂ a ∷ DAut.δs da₂ ss a)

  ≈⟨  composeA-gen da₁ da₂ (DAut.δ da₁ s₁ a) s₂ (DAut.δs da₂ (s₂ ∷ ss) a) ⟩

    lang da₁ (DAut.δ da₁ s₁ a) · lang da₂ s₂ ∪
      lang (powA da₂) (δs da₂ (s₂ ∷ ss) a)

  ≈⟨  union-congʳ (powA-cons da₂) ⟩

     lang da₁ (DAut.δ da₁ s₁ a) · lang da₂ s₂ ∪
      (lang da₂ (DAut.δ da₂ s₂ a) ∪ lang (powA da₂) (DAut.δs da₂ ss a))

  ≈⟨  ≅sym (union-assoc _) ⟩

     lang da₁ (DAut.δ da₁ s₁ a) · lang da₂ s₂ ∪
      lang da₂ (DAut.δ da₂ s₂ a) ∪ lang (powA da₂) (DAut.δs da₂ ss a)

  ∎ where open EqR (Bis _)

... | false = composeA-gen da₁ da₂ (DAut.δ da₁ s₁ a) s₂ (DAut.δs da₂ ss a)


composeA-correct : ∀{i S₁ S₂} (da₁ : DAut S₁) (da₂ : DAut S₂) (s₁ : S₁) (s₂ : S₂) →

  lang (composeA da₁ s₂ da₂) (s₁ , []) ≅⟨ i ⟩≅ lang da₁ s₁ · lang da₂ s₂

composeA-correct da₁ da₂ s₁ s₂ = begin
  lang (composeA da₁ s₂ da₂) (s₁ , [])                 ≈⟨  composeA-gen da₁ da₂ s₁ s₂ [] ⟩
  lang da₁ s₁ · lang da₂ s₂ ∪ lang (powA da₂) [] ≈⟨ union-congʳ (powA-nil da₂) ⟩
  lang da₁ s₁ · lang da₂ s₂ ∪ ∅                     ≈⟨ union-comm _ _ ⟩
  ∅ ∪ lang da₁ s₁ · lang da₂ s₂                     ≈⟨ union-emptyˡ ⟩
  lang da₁ s₁ · lang da₂ s₂
  ∎ where open EqR (Bis _)


module StarCorrect (decS : DecSetoid lzero lzero) where
  open Star decS


  acceptingInitial-just : ∀{i} (s₀ : S) (da : DAut S) {s : S} →

    lang (acceptingInitial s₀ da) (just s) ≅⟨ i ⟩≅ lang da s

  ≅ν (acceptingInitial-just s₀ da) = refl
  ≅δ (acceptingInitial-just s₀ da) a = acceptingInitial-just s₀ da

  acceptingInitial-nothing :  ∀{i} (s₀ : S) (da : DAut S) →

    lang (acceptingInitial s₀ da) nothing ≅⟨ i ⟩≅ ε ∪ lang da s₀

  ≅ν (acceptingInitial-nothing s₀ da)   = refl
  ≅δ (acceptingInitial-nothing s₀ da) a = begin

      lang (acceptingInitial s₀ da) (just (DAut.δ da s₀ a))

    ≈⟨ acceptingInitial-just _ _ ⟩

      lang da (DAut.δ da s₀ a)

    ≈⟨ ≅sym union-emptyˡ ⟩

      ∅ ∪ lang da (DAut.δ da s₀ a)

    ∎ where open EqR (Bis _)

  starA-lemma :  ∀{i} (da : DAut S) (s₀ : S) (ss : List (Maybe S)) →

    lang (starA s₀ da) ss ≅⟨ i ⟩≅ lang (powA (acceptingInitial s₀ da)) ss · (lang da s₀) *

  ≅ν (starA-lemma da s₀ ss) = sym (∧-true _)
  ≅δ (starA-lemma da s₀ ss) a with DAut.νs (acceptingInitial s₀ da) ss
  ≅δ (starA-lemma da s₀ ss) a | false = starA-lemma da s₀ (DAut.δs (acceptingInitial s₀ da) ss a)
  ≅δ (starA-lemma da s₀ ss) a | true = begin

        lang (starA s₀ da) ss'

      ≈⟨ starA-lemma da s₀ ss' ⟩

        lang (powA (acceptingInitial s₀ da)) ss' · lang da s₀ *

      ≈⟨ concat-congˡ (begin

          lang (powA (acceptingInitial s₀ da)) ss'

        ≈⟨ powA-cons _ ⟩

          lang (acceptingInitial s₀ da) (just (DAut.δ da s₀ a))
            ∪
          lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)

        ≈⟨ union-congˡ (acceptingInitial-just _ _) ⟩

          lang da (DAut.δ da s₀ a)
            ∪
          lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)

        ≈⟨ union-comm _ _ ⟩

          lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)
            ∪
          lang da (DAut.δ da s₀ a)

        ∎ ) ⟩

        (lang (powA (acceptingInitial s₀ da)) (DAut.δs (acceptingInitial s₀ da) ss a)
          ∪ lang da (DAut.δ da s₀ a)) · lang da s₀ *

      ≈⟨ concat-union-distribˡ _ ⟩

        lang (powA (acceptingInitial s₀ da)) (DAut.δs (acceptingInitial s₀ da) ss a)
          · lang da s₀ *
        ∪ lang da (DAut.δ da s₀ a)
          · lang da s₀ *

      ∎ where
        open EqR (Bis _)
        ss' = (just (DAut.δ da s₀ a) ∷ DAut.δs (acceptingInitial s₀ da) ss a)

  starA-correct : ∀{i} (da : DAut S) (s₀ : S) →
    lang (starA s₀ da) (nothing ∷ []) ≅⟨ i ⟩≅ (lang da s₀) *

  starA-correct da s₀ = begin

      lang (starA s₀ da) (nothing ∷ [])

    ≈⟨  starA-lemma da s₀ (nothing ∷ []) ⟩

      lang (powA (acceptingInitial s₀ da)) (nothing ∷ [])
        · lang da s₀ *

    ≈⟨ concat-congˡ (powA-correct _ _) ⟩

      lang (acceptingInitial s₀ da) nothing
        · lang da s₀ *

    ≈⟨ concat-congˡ (acceptingInitial-nothing _ _) ⟩

      (ε ∪ lang da s₀) · lang da s₀ *

    ≈⟨ concat-maybe-star _ ⟩

      lang da s₀ *

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
  → lang da s ≅⟨ i ⟩≅ lang da' (Inverse.to iso Π.⟨$⟩ s)
≅ν (convA-correct iso da s)   rewrite _InverseOf_.left-inverse-of (Inverse.inverse-of iso) s
  = refl
≅δ (convA-correct iso da s) a rewrite _InverseOf_.left-inverse-of (Inverse.inverse-of iso) s
  = convA-correct iso da (DAut.δ da s a)
