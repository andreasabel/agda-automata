\AgdaHide{
\begin{code}
\end{code}
}
\AgdaHide{
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

open import Library

module Automaton
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA

-- Automaton

-- Following Rutten, we only represent the fixed parts of the automaton
-- (acceptance condition and transition function).
-- The state the automaton is in (like the initial state) is represented
-- outside.
\end{code}
}
\newcommand{\aDA}{
\begin{code}

record DA (S : Set) : Set where
  field  ν  :  (s : S) → Bool
         δ  :  (s : S) (a : A) → S

  νs : ∀{i} (ss : List i S) → Bool
  νs ss = List.any ν ss

  δs : ∀{i} (ss : List i S) (a : A) → List i S
  δs ss a = List.map (λ s → δ s a) ss

\end{code}
}
\AgdaHide{
\begin{code}


-- Language accepted by an automaton

module Acc {S} (da : DA S) (open DA da) where

  -- Word acceptance from a state

  accept : ∀{i} (s : S) (as : List i A) → Bool
  accept s [] = ν s
  accept s (a ∷ as) = accept (δ s a) as

  -- Language accepted by a state.
  -- The terminal morphism aka coiteration.

  acclang : ∀{i} (s : S) → Lang i
  Lang.ν (acclang s) = ν s
  Lang.δ (acclang s) a = acclang (δ s a)

\end{code}
}
\newcommand{\aacclang}{
\begin{code}

lang : ∀{i} {S} (da : DA S) (s : S) → Lang i
Lang.ν (lang da s)    =  DA.ν da s
Lang.δ (lang da s) a  =  lang da (DA.δ da s a)

\end{code}
}
\AgdaHide{
\begin{code}
open DA public
\end{code}
}

% -- An automaton recognizing the empty language

\newcommand{\aemptyA}{
\begin{code}

∅A : DA ⊤
ν  ∅A  s     =  false
δ  ∅A  s  a  =  s

\end{code}
}
\AgdaHide{
\begin{code}

-- An automaton recognizing the trivial language

allA : DA ⊤
ν allA s    = true
δ allA s a  = s

-- An automaton recognizing only the empty word.  (Or nothing.)
\end{code}
}
\newcommand{\aepsA}{
\begin{code}

εA : DA Bool
ν  εA  b     =  b
δ  εA  b  a  =  false

\end{code}
}
\AgdaHide{
\begin{code}

-- An automaton recognizing a single word consisting of a single character.
-- nothing is the error state, just false the initial state, just true the accepting state.

charA' : (a : A) → DA (Maybe Bool)
ν (charA' a) (just b) = b
ν (charA' a) nothing = false
δ (charA' a) (just false) x with a ≟ x
δ (charA' a) (just false) x | yes p = just true
δ (charA' a) (just false) x | no ¬p = nothing
δ (charA' a) (just true) x = nothing
δ (charA' a) nothing _ = nothing

\end{code}
}
\newcommand{\acharA}{
\begin{code}

data 3States : Set where
  init acc err : 3States

charA : (a : A) → DA 3States
ν  (charA a)  init     =  false
ν  (charA a)  acc      =  true
ν  (charA a)  err      =  false
δ  (charA a)  init  x  =
  if ⌊ a ≟ x ⌋ then acc else err
δ  (charA a)  acc   x  =  err
δ  (charA a)  err   x  =  err

\end{code}
}
\AgdaHide{
\begin{code}
-- The complement automaton

\end{code}
}
\newcommand{\acomplA}{
\begin{code}

complA : ∀{S} (da : DA S) → DA S
ν  (complA da)  s     =  not (ν da s)
δ  (complA da)  s  a  =  δ da s a

\end{code}
}
\AgdaHide{
\begin{code}

-- A product automaton recognizing intersection

_⊗_ : ∀{S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) → DA (S₁ × S₂)
ν  (da₁ ⊗ da₂) (s₁ , s₂)   = ν da₁ s₁ ∧ ν da₂ s₂
δ  (da₁ ⊗ da₂) (s₁ , s₂) a = δ da₁ s₁ a , δ da₂ s₂ a

-- A product automaton recognizing union

\end{code}
}
\newcommand{\aunionA}{
\begin{code}

_⊕_ : ∀{S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) → DA (S₁ × S₂)
ν  (da₁ ⊕ da₂)  (s₁ , s₂)     =  ν da₁ s₁    ∨  ν da₂ s₂
δ  (da₁ ⊕ da₂)  (s₁ , s₂)  a  =  δ da₁ s₁ a  ,  δ da₂ s₂ a

\end{code}
}
\AgdaHide{
\begin{code}

-- Automaton composition is not trivial for DFAs.
-- It is easy for NFAs.  It is also easy to compose a DFA with an NFA.

-- Abstract automaton composition

\end{code}
}
\AgdaHide{
\begin{code}

acomposeA' : ∀{S₁ S₂} (da₁ : DA S₁) (f : S₂ → S₂) (da₂ : DA S₂) → DA (S₁ × S₂)
ν (acomposeA' da₁ f da₂) (s₁ , s₂)   = ν da₁ s₁ ∧ ν da₂ (f s₂) ∨ ν da₂ s₂
δ (acomposeA' da₁ f da₂) (s₁ , s₂) a = δ da₁ s₁ a , δ da₂ s₂' a
  where s₂' = if ν da₁ s₁ then f s₂ else s₂

\end{code}
}
\AgdaHide{
\begin{code}

-- Finite powerset automaton with lists (alt: finite sets).

\end{code}
}
\newcommand{\apowA}{
\begin{code}

powA : ∀{S} (da : DA S) → DA (List ∞ S)
ν  (powA da)  ss     =  νs da ss
δ  (powA da)  ss  a  =  δs da ss a

\end{code}
}
\AgdaHide{
\begin{code}

-- Automaton composition
-- We need an initial state of the second automaton to glue them together.
-- We could also allow a list of initial states of the second automaton.

\end{code}
}
\AgdaHide{
\begin{code}

composeA' : ∀{S₁ S₂} (da₁ : DA S₁) (s₀ : S₂) (da₂ : DA S₂) → DA (S₁ × List ∞ S₂)
composeA' da₁ s₀ da₂ = acomposeA' da₁ (_∷_ s₀) (powA da₂)

\end{code}
}
\newcommand{\acomposeA}{
\begin{code}

composeA : ∀{S₁ S₂}
  (da₁ : DA S₁) (s₂ : S₂) (da₂ : DA S₂) → DA (S₁ × List ∞ S₂)

\end{code}
}
\newcommand{\acomposeAnu}{
\begin{code}

ν  (composeA da₁ s₂ da₂)  (s₁ , ss₂)     =
  (ν da₁ s₁ ∧ ν da₂ s₂) ∨ νs da₂ ss₂

\end{code}
}
\newcommand{\acomposeAdelta}{
\begin{code}

δ  (composeA da₁ s₂ da₂)  (s₁ , ss₂)  a  =
  δ da₁ s₁ a , δs da₂ (if ν da₁ s₁ then s₂ ∷ ss₂ else ss₂) a

\end{code}
}
\AgdaHide{
\begin{code}


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
  acceptingInitial : (s₀ : S) (da : DA S) → DA (Maybe S)
  ν (acceptingInitial s₀ da) nothing      =  true
  ν (acceptingInitial s₀ da) (just s)     =  ν da s
  δ (acceptingInitial s₀ da) nothing   a  =  just (δ da s₀ a)
  δ (acceptingInitial s₀ da) (just s)  a  =  just (δ da s a)

  finalToInitial : (da : DA (Maybe S)) → DA (List ∞ (Maybe S))
  ν (finalToInitial da) ss   = νs da ss
  δ (finalToInitial da) ss a =
    let ss' = δs da ss a
    in  if νs da ss then δ da nothing a ∷ ss' else ss'

  starA : (s₀ : S) (da : DA S) → DA (List ∞ (Maybe S))
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

unionA-correct : ∀{i S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) (s₁ : S₁) (s₂ : S₂) →
  lang da₁ s₁ ∪ lang da₂ s₂ ≅⟨ i ⟩≅ lang (da₁ ⊕ da₂) (s₁ , s₂)
≅ν (unionA-correct da₁ da₂ s₁ s₂) = refl
≅δ (unionA-correct da₁ da₂ s₁ s₂) a = unionA-correct da₁ da₂ (δ da₁ s₁ a) (δ da₂ s₂ a)

-- Power construction preserves semantics

\end{code}
}
\newcommand{\apowAnil}{
\begin{code}

powA-nil : ∀{i S} (da : DA S) →

  lang (powA da) [] ≅⟨ i ⟩≅ ∅

≅ν  (powA-nil da)     = refl
≅δ  (powA-nil da)  a  = powA-nil da

\end{code}
}
\newcommand{\apowAcons}{
\begin{code}

powA-cons : ∀{i S} (da : DA S) {s : S} {ss : List ∞ S} →

  lang (powA da) (s ∷ ss) ≅⟨ i ⟩≅ lang da s ∪ lang (powA da) ss

≅ν  (powA-cons da)     = refl
≅δ  (powA-cons da)  a  = powA-cons da

\end{code}
}
\newcommand{\apowAcorrect}{
\begin{code}

powA-correct : ∀{i S} (da : DA S) (s : S) → lang (powA da) (s ∷ []) ≅⟨ i ⟩≅ lang da s
≅ν (powA-correct da s) with ν da s
... | true = refl
... | false = refl
≅δ (powA-correct da s) a = powA-correct da (δ da s a)

\end{code}
}
\AgdaHide{
\begin{code}

fact : ∀ a {b c} → (a ∧ (b ∨ c)) ∨ c ≡ (a ∧ b) ∨ c
fact a {b} {c} = begin
  (a ∧ (b ∨ c)) ∨ c       ≡⟨ ∨-∧-distribʳ c a _ ⟩
  (a ∨ c) ∧ ((b ∨ c) ∨ c) ≡⟨ ∧-cong (refl {x = (a ∨ c)}) (∨-assoc b c c) ⟩
  (a ∨ c) ∧ (b ∨ (c ∨ c)) ≡⟨ ∧-cong (refl {x = a ∨ c}) (∨-cong (refl {x = b}) (∨-idem c)) ⟩
  (a ∨ c) ∧ (b ∨ c)       ≡⟨ sym (∨-∧-distribʳ c a b) ⟩
  (a ∧ b) ∨ c
  ∎ where open ≡-Reasoning

composeA'-gen : ∀{i S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) (s₁ : S₁) (s₂ : S₂) (ss : List ∞ S₂) →
  lang (composeA' da₁ s₂ da₂) (s₁ , ss) ≅⟨ i ⟩≅ lang da₁ s₁ · lang da₂ s₂ ∪ lang (powA da₂) ss
≅ν (composeA'-gen da₁ da₂ s₁ s₂ ss) = fact (ν da₁ s₁)
≅δ (composeA'-gen da₁ da₂ s₁ s₂ ss) a with ν da₁ s₁

... | true  = begin

    lang (acomposeA' da₁ (_∷_ s₂) (powA da₂))
      (δ da₁ s₁ a , δ da₂ s₂ a ∷ δs da₂ ss a)

  ≈⟨  composeA'-gen da₁ da₂ (δ da₁ s₁ a) s₂ (δs da₂ (s₂ ∷ ss) a) ⟩

    lang da₁ (δ da₁ s₁ a) · lang da₂ s₂ ∪
      lang (powA da₂) (δs da₂ (s₂ ∷ ss) a)

  ≈⟨  union-congʳ (powA-cons da₂) ⟩

     lang da₁ (δ da₁ s₁ a) · lang da₂ s₂ ∪
      (lang da₂ (δ da₂ s₂ a) ∪ lang (powA da₂) (δs da₂ ss a))

  ≈⟨  ≅sym (union-assoc _) ⟩

     lang da₁ (δ da₁ s₁ a) · lang da₂ s₂ ∪
      lang da₂ (δ da₂ s₂ a) ∪ lang (powA da₂) (δs da₂ ss a)

  ∎ where open EqR (Bis _)

... | false = composeA'-gen da₁ da₂ (δ da₁ s₁ a) s₂ (δs da₂ ss a)


composeA'-correct : ∀{i S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) (s₁ : S₁) (s₂ : S₂) →

  lang (composeA' da₁ s₂ da₂) (s₁ , []) ≅⟨ i ⟩≅ lang da₁ s₁ · lang da₂ s₂

composeA'-correct da₁ da₂ s₁ s₂ = begin
  lang (composeA' da₁ s₂ da₂) (s₁ , [])                 ≈⟨  composeA'-gen da₁ da₂ s₁ s₂ [] ⟩
  lang da₁ s₁ · lang da₂ s₂ ∪ lang (powA da₂) [] ≈⟨ union-congʳ (powA-nil da₂) ⟩
  lang da₁ s₁ · lang da₂ s₂ ∪ ∅                     ≈⟨ union-comm _ _ ⟩
  ∅ ∪ lang da₁ s₁ · lang da₂ s₂                     ≈⟨ union-emptyˡ ⟩
  lang da₁ s₁ · lang da₂ s₂
  ∎ where open EqR (Bis _)


-- correctness of composition

\end{code}
}
\newcommand{\acomposeAgen}{
\begin{code}

composeA-gen : ∀{i S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) →
  ∀ (s₁ : S₁) (s₂ : S₂) (ss : List ∞ S₂) →

    lang (composeA da₁ s₂ da₂) (s₁ , ss)
  ≅⟨ i ⟩≅
    lang da₁ s₁ · lang da₂ s₂ ∪ lang (powA da₂) ss

\end{code}
}
\newcommand{\acomposeAgenproof}{
\begin{code}

≅ν (composeA-gen da₁ da₂ s₁ s₂ ss) = refl
≅δ (composeA-gen da₁ da₂ s₁ s₂ ss) a with ν da₁ s₁
... | false = composeA-gen da₁ da₂ (δ da₁ s₁ a) s₂ (δs da₂ ss a)

... | true  = begin

    lang (composeA da₁ s₂ da₂)
      (δ da₁ s₁ a , δ da₂ s₂ a ∷ δs da₂ ss a)

  ≈⟨  composeA-gen da₁ da₂ (δ da₁ s₁ a) s₂ (δs da₂ (s₂ ∷ ss) a) ⟩

    lang da₁ (δ da₁ s₁ a) · lang da₂ s₂ ∪
      lang (powA da₂) (δs da₂ (s₂ ∷ ss) a)

  ≈⟨  union-congʳ (powA-cons da₂) ⟩

     lang da₁ (δ da₁ s₁ a) · lang da₂ s₂ ∪
      (lang da₂ (δ da₂ s₂ a) ∪ lang (powA da₂) (δs da₂ ss a))

  ≈⟨  ≅sym (union-assoc _) ⟩

     lang da₁ (δ da₁ s₁ a) · lang da₂ s₂ ∪
      lang da₂ (δ da₂ s₂ a) ∪ lang (powA da₂) (δs da₂ ss a)

  ∎ where open EqR (Bis _)

\end{code}
}

% composeA-correct : ∀{i S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) (s₁ : S₁) (s₂ : S₂) →

\newcommand{\acomposeAcorrect}{
\begin{code}

composeA-correct : ∀{i S₁ S₂} (da₁ : DA S₁) (da₂ : DA S₂) s₁ s₂ →

  lang (composeA da₁ s₂ da₂) (s₁ , []) ≅⟨ i ⟩≅ lang da₁ s₁ · lang da₂ s₂

\end{code}
}
\AgdaHide{
\begin{code}

composeA-correct da₁ da₂ s₁ s₂ = begin
    lang (composeA da₁ s₂ da₂) (s₁ , [])            ≈⟨  composeA-gen da₁ da₂ s₁ s₂ [] ⟩
    lang da₁ s₁ · lang da₂ s₂ ∪ lang (powA da₂) []  ≈⟨ union-congʳ (powA-nil da₂) ⟩
    lang da₁ s₁ · lang da₂ s₂ ∪ ∅                   ≈⟨ union-comm _ _ ⟩
    ∅ ∪ lang da₁ s₁ · lang da₂ s₂                   ≈⟨ union-emptyˡ ⟩
    lang da₁ s₁ · lang da₂ s₂
  ∎ where open EqR (Bis _)

\end{code}
}
\AgdaHide{
\begin{code}


module StarCorrect (decS : DecSetoid lzero lzero) where
  open Star decS

  acceptingInitial-just : ∀{i} (s₀ : S) (da : DA S) {s : S} →

    lang (acceptingInitial s₀ da) (just s) ≅⟨ i ⟩≅ lang da s

  ≅ν (acceptingInitial-just s₀ da) = refl
  ≅δ (acceptingInitial-just s₀ da) a = acceptingInitial-just s₀ da

  acceptingInitial-nothing :  ∀{i} (s₀ : S) (da : DA S) →

    lang (acceptingInitial s₀ da) nothing ≅⟨ i ⟩≅ ε ∪ lang da s₀

  ≅ν (acceptingInitial-nothing s₀ da)   = refl
  ≅δ (acceptingInitial-nothing s₀ da) a = begin

      lang (acceptingInitial s₀ da) (just (δ da s₀ a))

    ≈⟨ acceptingInitial-just _ _ ⟩

      lang da (δ da s₀ a)

    ≈⟨ ≅sym union-emptyˡ ⟩

      ∅ ∪ lang da (δ da s₀ a)

    ∎ where open EqR (Bis _)

  starA-lemma :  ∀{i} (da : DA S) (s₀ : S) (ss : List ∞ (Maybe S)) →

    lang (starA s₀ da) ss ≅⟨ i ⟩≅ lang (powA (acceptingInitial s₀ da)) ss · (lang da s₀) *

  ≅ν (starA-lemma da s₀ ss) = sym (∧-true _)
  ≅δ (starA-lemma da s₀ ss) a with νs (acceptingInitial s₀ da) ss
  ≅δ (starA-lemma da s₀ ss) a | false = starA-lemma da s₀ (δs (acceptingInitial s₀ da) ss a)
  ≅δ (starA-lemma da s₀ ss) a | true = begin

        lang (starA s₀ da) ss'

      ≈⟨ starA-lemma da s₀ ss' ⟩

        lang (powA (acceptingInitial s₀ da)) ss' · lang da s₀ *

      ≈⟨ concat-congˡ (begin

          lang (powA (acceptingInitial s₀ da)) ss'

        ≈⟨ powA-cons _ ⟩

          lang (acceptingInitial s₀ da) (just (δ da s₀ a))
            ∪
          lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)

        ≈⟨ union-congˡ (acceptingInitial-just _ _) ⟩

          lang da (δ da s₀ a)
            ∪
          lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)

        ≈⟨ union-comm _ _ ⟩

          lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)
            ∪
          lang da (δ da s₀ a)

        ∎ ) ⟩

        (lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)
          ∪ lang da (δ da s₀ a)) · lang da s₀ *

      ≈⟨ concat-union-distribˡ _ ⟩

        lang (powA (acceptingInitial s₀ da)) (δs (acceptingInitial s₀ da) ss a)
          · lang da s₀ *
        ∪ lang da (δ da s₀ a)
          · lang da s₀ *

      ∎ where
        open EqR (Bis _)
        ss' = (just (δ da s₀ a) ∷ δs (acceptingInitial s₀ da) ss a)

  starA-correct : ∀{i} (da : DA S) (s₀ : S) →
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

convA : ∀{S S'} (iso : S ↔ S') (da : DA S) → DA S'
ν (convA iso da) s' = ν da (Inverse.from iso Π.⟨$⟩ s' )
δ (convA iso da) s' a = Inverse.to iso Π.⟨$⟩ (δ da) (Inverse.from iso Π.⟨$⟩ s') a

-- Conversion does not change the semantics.

-- The recognized language from each state is still the same
-- (when starting from the corresponding state).

convA-correct : ∀{i S S'} (iso : S ↔ S') (da : DA S) (let da' = convA iso da) (s : S)
  → lang da s ≅⟨ i ⟩≅ lang da' (Inverse.to iso Π.⟨$⟩ s)
≅ν (convA-correct iso da s)   rewrite _InverseOf_.left-inverse-of (Inverse.inverse-of iso) s
  = refl
≅δ (convA-correct iso da s) a rewrite _InverseOf_.left-inverse-of (Inverse.inverse-of iso) s
  = convA-correct iso da (δ da s a)
\end{code}
}
