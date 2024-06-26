\AgdaHide{
\begin{code}

\end{code}
\begin{code}

{-# OPTIONS --sized-types #-}

open import Library

module Language
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_; _≈_) renaming (Carrier to A)) where

infix   1 _≅⟨_⟩≅_
infix   2 _∋_
infixl  4 _∪_
infixl  5 _∩_
infixl  6 _·_
infixr 15 _^_
infixr 15 _*
infixr 15 _⁺

-- Coalgebra L → Bool × (A → L)
--
-- E.g.  (List A → Bool) → Bool × (A → List A → Bool)
-- which is  (1 + A × List A) → Bool
--
-- In general,
--   (List A → B)
--     ≅ (1 + A × List A) → B
--     ≅ (1 → B) × (A × List A) → B
--     ≅ B × (A → (List A → B))
--
--   (μ X. 1 + A × X) → B ≅ ν Y. B × (A → Y)
--
-- Altenkirch, Representation of first-order function types as terminal coalgebras
-- Hinze, Generalizing generalized tries

-- A decidable language is a decidable set of words aka dictionary aka trie.

\end{code}
}
\newcommand{\aLang}{
\begin{code}

record Lang i : Set where
  coinductive
  field  ν  :  Bool
         δ  :  ∀{j : Size< i} → A → Lang j

\end{code}
}
\AgdaHide{
\begin{code}
open Lang

-- Examples for sized typing:
--
-- delta2 : ∀{i} → Lang (↑ (↑ i)) → A → Lang i
-- delta2 l a = δ (δ l a) a
--
-- half : ∀{i} → Lang ∞ → Lang i
-- ν (half l) = ν l
-- δ (half l) x = half (δ (δ l x) x)

\end{code}
}

% Word membership

\newcommand{\ani}{
\begin{code}

_∋_ : ∀{i} → Lang i → List i A → Bool
l  ∋  []      =  ν l
l  ∋  a ∷ as  =  δ l a ∋ as

\end{code}
}

% Language from word membership

\newcommand{\alang}{
\begin{code}

trie : ∀{i} (f : List i A → Bool) → Lang i
ν (trie f)    =  f []
δ (trie f) a  =  trie (λ as → f (a ∷ as))

\end{code}
}

% This makes Lang isomophic to (List A → Bool)

% Constructions of language

% empty language

\newcommand{\aempty}{
\begin{code}

∅ : ∀{i} → Lang i
ν ∅    =  false
δ ∅ x  =  ∅

\end{code}
}

% language consisting of the empty word

\newcommand{\aeps}{
\begin{code}

ε : ∀{i} → Lang i
ν ε    =  true
δ ε x  =  ∅

\end{code}
}

% language consisting of a single single-character word

\newcommand{\acharp}{
\begin{code}

char′ : ∀{i} (a : A) → Lang i

ν (char′ a)    =  false
δ (char′ a) x  with a ≟ x
... | yes _   =  ε
... | no  _   =  ∅

\end{code}
}

\newcommand{\achar}{
\begin{code}

char : ∀{i} (a : A) → Lang i

ν  (char a)     =  false
δ  (char a)  x  =  if  ⌊ a ≟ x ⌋  then  ε  else  ∅

\end{code}
}

% Language complement

\newcommand{\acompl}{
\begin{code}

compl : ∀{i} (l : Lang i) → Lang i
ν (compl l)    =  not    (ν l)
δ (compl l) x  =  compl  (δ l x)

\end{code}
}

\AgdaHide{
\begin{code}

-- trivial language (containing every word)

all : ∀{i} → Lang i
ν all    =  true
δ all x  =  all

-- intersection of languages

_∩_ : ∀{i} (k l : Lang i) → Lang i
ν (k ∩ l)    =  ν k    ∧  ν l
δ (k ∩ l) x  =  δ k x  ∩  δ l x
\end{code}
}

%  union of languages

\newcommand{\aunion}{
\begin{code}

_∪_ : ∀{i} (k l : Lang i) → Lang i
ν (k ∪ l)    =  ν k    ∨  ν l
δ (k ∪ l) x  =  δ k x  ∪  δ l x

\end{code}
}

\AgdaHide{
\begin{code}
module ConcatExplIf where
\end{code}
}

\newcommand{\aconcatexplif}{
\begin{code}

  _·_ : ∀{i} (k l : Lang i) → Lang i

  δ (_·_{i} k l) {j} x =
    let  k′l : Lang j
         k′l = _·_{j} (δ k {j} x) l
    in   if  ν k  then  _∪_{j} k′l (δ l {j} x)  else  k′l

\end{code}
}
\AgdaHide{
\begin{code}
  ν (_·_ {j} k l)        =  ν k ∧ ν l
\end{code}
}

% concatenation of languages

\AgdaHide{
\begin{code}
module ConcatIf where
\end{code}
}

\newcommand{\aconcatif}{
\begin{code}

  _·_ : ∀{i} (k l : Lang i) → Lang i
  ν (k · l)    =  ν k ∧ ν l
  δ (k · l) x  =  let  k′l = δ k x · l  in  if  ν k  then  k′l ∪ δ l x  else  k′l

\end{code}
}

\AgdaHide{
\begin{code}
module ConcatExpl where
\end{code}
}

\newcommand{\aconcatexpl}{
\begin{code}

  _·_ : ∀{i} (k l : Lang i) → Lang i

  δ (_·_{i} k l) {j} x =
    applyWhen {A = Lang j}
      (ν k)
      (λ (k′l : Lang j) →  _∪_{j} k′l (δ l {j} x))
      (_·_{j} (δ k {j} x) l)

\end{code}
}
\AgdaHide{
\begin{code}
  ν (_·_ {j} k l)        =  ν k ∧ ν l
\end{code}
}

% concatenation of languages

\newcommand{\aconcat}{
\begin{code}

_·_ : ∀{i} (k l : Lang i) → Lang i
ν (k · l)    =  ν k ∧ ν l
δ (k · l) x  =  applyWhen (ν k) (_∪ δ l x) (δ k x · l)

\end{code}
}

\AgdaHide{
\begin{code}
-- δ (k · l) x = let k′l = δ k x · l in
--   if ν k then k′l ∪ δ l x else k′l
-- δ (k · l) x = if ν k then k′l ∪ δ l x else k′l
--   where k′l = δ k x · l
-- OR: δ (k · l) x = (δ k x · l) ∪ (if ν k then δ l x else ∅)

\end{code}
}

% Kleene star

\newcommand{\astar}{
\begin{code}

_* : ∀{i} (l : Lang i) → Lang i
ν (l *)    =  true
δ (l *) x  =  δ l x · (l *)

\end{code}
}

% Kleene plus

\newcommand{\aplus}{
\begin{code}

_⁺ : ∀{i} (l : Lang i) → Lang i
l ⁺ = l · l *

\end{code}
}

\AgdaHide{
\begin{code}

-- Exponentiation

_^_ : ∀{i} (l : Lang i) (n : ℕ) → Lang i
l ^ zero  = ε
l ^ suc n = l · l ^ n

-- Examples

aⁿbⁿ! : ∀{i} (a b : A) (n : ℕ) → Lang i
aⁿbⁿ! a b n = char a ^ n · char b ^ n

data ThisThatElse (a b x : A) : Set where
  this : (p : x ≈ a) → ThisThatElse a b x
  that : (p : x ≈ b) → ThisThatElse a b x
  else : (¬this : ¬ (x ≈ a)) (¬that : ¬(x ≈ b)) → ThisThatElse a b x

thisThatElse : (a b x : A) → ThisThatElse a b x
thisThatElse a b x with x ≟ a
thisThatElse a b x | yes p = this p
thisThatElse a b x | no ¬p with x ≟ b
thisThatElse a b x | no ¬p | yes p = that p
thisThatElse a b x | no ¬p | no ¬q = else ¬p ¬q

-- Finish with n bs more than as coming now.
thenbs : ∀{i} (a b : A) (n : ℕ) → Lang i
ν (thenbs a b n)   = zero? n
δ (thenbs a b n) x = case (thisThatElse a b x) of \
  { (this p) → thenbs a b (suc n)
  ; (that p) → char b ^ n
  ; _        → ∅
  }

-- -- Does not reduce, see issue #...!
-- thenbs : ∀{i} (a b : A) (n : ℕ) → Lang i
-- ν (thenbs a b zero)    = true
-- ν (thenbs a b (suc _)) = false
-- δ (thenbs a b n)       x with thisThatElse a b x
-- δ (thenbs a b n)       x | this p = thenbs a b (suc n)
-- δ (thenbs a b (suc n)) x | that p = char b ^ n
-- δ (thenbs a b n)       x | _      = ∅

aⁿbⁿ : ∀{i} (a b : A) → Lang i
aⁿbⁿ a b = thenbs a b zero

\end{code}
}


% -- Language equality

\newcommand{\abisim}{
\begin{code}

record _≅⟨_⟩≅_ (l : Lang ∞) i (k : Lang ∞) : Set where
  coinductive
  field  ≅ν  :  ν l ≡ ν k
         ≅δ  :  ∀{j : Size< i} (a : A) → δ l a ≅⟨ j ⟩≅ δ k a

\end{code}
}
\AgdaHide{
\begin{code}
open _≅⟨_⟩≅_ public

_≅_ : ∀ (l k : Lang ∞) → Set
l ≅ k = l ≅⟨ ∞ ⟩≅ k

\end{code}
}

% -- Equivalence relation laws

\newcommand{\arefl}{
\begin{code}

≅refl : ∀{i} {l : Lang ∞} → l ≅⟨ i ⟩≅ l
≅ν  ≅refl    =  refl
≅δ  ≅refl a  =  ≅refl

\end{code}
}

\newcommand{\asym}{
\begin{code}

≅sym : ∀{i} {k l : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → k ≅⟨ i ⟩≅ l
≅ν  (≅sym p)    =  sym   (≅ν p)
≅δ  (≅sym p) a  =  ≅sym  (≅δ p a)

\end{code}
}

\newcommand{\atrans}{
\begin{code}

≅trans  :  ∀{i} {k l m : Lang ∞}
           (p : k ≅⟨ i ⟩≅ l) (q : l ≅⟨ i ⟩≅ m) → k ≅⟨ i ⟩≅ m
≅ν  (≅trans p q)    =  trans   (≅ν p)    (≅ν q)
≅δ  (≅trans p q) a  =  ≅trans  (≅δ p a)  (≅δ q a)

\end{code}
}

\AgdaHide{
\begin{code}

-- Congruence law (UNPROVABLE)

-- ≅cong : ∀{i} (f : Lang ∞ → Lang ∞) {k l : Lang ∞} (p : l ≅⟨ i ⟩≅ k) →
--   f l ≅⟨ i ⟩≅ f k
-- ≅ν (≅cong f p)  =  {!≅ν p!}
-- ≅δ (≅cong f p) a  =  {!!}

-- Setoid
\end{code}
}

% IsEquivalence.refl   (≅isEquivalence i)  =  ≅refl
% IsEquivalence.sym    (≅isEquivalence i)  =  ≅sym
% IsEquivalence.trans  (≅isEquivalence i)  =  ≅trans

\newcommand{\asetoid}{
\begin{code}

≅isEquivalence : ∀(i : Size) → IsEquivalence _≅⟨ i ⟩≅_
≅isEquivalence i = record { refl = ≅refl; sym = ≅sym; trans = ≅trans }

Bis : ∀(i : Size) → Setoid _ _
Setoid.Carrier        (Bis i)  =  Lang ∞
Setoid._≈_            (Bis i)  =  _≅⟨ i ⟩≅_
Setoid.isEquivalence  (Bis i)  =  ≅isEquivalence i

\end{code}
}

\newcommand{\atransp}{
\begin{code}

≅trans′  :  ∀ i (k l m : Lang ∞)
            (p : k ≅⟨ i ⟩≅ l) (q : l ≅⟨ i ⟩≅ m) → k ≅⟨ i ⟩≅ m
≅trans′ i k l m p q = begin
  k  ≈⟨ p ⟩
  l  ≈⟨ q ⟩
  m  ∎ where open EqR (Bis i)

\end{code}
}

\AgdaHide{
\begin{code}

-- Complement laws

compl-empty : ∀{i} → compl ∅ ≅⟨ i ⟩≅ all
≅ν  compl-empty    =  refl
≅δ  compl-empty a  =  compl-empty

compl-top : ∀{i} → compl all ≅⟨ i ⟩≅ ∅
≅ν  compl-top    =  refl
≅δ  compl-top a  =  compl-top

compl-cong : ∀{i}{l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → compl l ≅⟨ i ⟩≅ compl k
≅ν  (compl-cong p) rewrite ≅ν p  =  refl
≅δ  (compl-cong p) a             =  compl-cong (≅δ p a)

-- Intersection laws

inter-assoc : ∀{i} (k {l m} : Lang ∞) → (k ∩ l) ∩ m ≅⟨ i ⟩≅ k ∩ (l ∩ m)
≅ν  (inter-assoc k)    =   ∧-assoc (ν k) _ _
≅δ  (inter-assoc k) a  =  inter-assoc _

inter-comm : ∀{i} (l {k} : Lang ∞) → l ∩ k ≅⟨ i ⟩≅ k ∩ l
≅ν  (inter-comm l)    =  ∧-comm (ν l) _
≅δ  (inter-comm l) a  =  inter-comm (δ l a)

inter-idem : ∀{i} (l : Lang ∞) → l ∩ l ≅⟨ i ⟩≅ l
≅ν  (inter-idem l)    =  ∧-idem (ν l)
≅δ  (inter-idem l) a  =  inter-idem (δ l a)

inter-empty : ∀{i} {l : Lang ∞} → ∅ ∩ l ≅⟨ i ⟩≅ ∅
≅ν  inter-empty    =  refl
≅δ  inter-empty a  =  inter-empty

inter-top : ∀{i} {l : Lang ∞} → all ∩ l ≅⟨ i ⟩≅ l
≅ν  inter-top    =  refl
≅δ  inter-top a  =  inter-top

inter-congˡ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → l ∩ m ≅⟨ i ⟩≅ k ∩ m
≅ν  (inter-congˡ p) rewrite ≅ν p  =  refl
≅δ  (inter-congˡ p) a  =  inter-congˡ (≅δ p a)

inter-congʳ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → m ∩ l ≅⟨ i ⟩≅ m ∩ l
≅ν  (inter-congʳ p) rewrite ≅ν p  =  refl
≅δ  (inter-congʳ p) a  =  inter-congʳ (≅δ p a)
\end{code}
}

% -- Union laws

\newcommand{\aunionassoc}{
\begin{code}

union-assoc : ∀{i} (k {l m} : Lang ∞) → (k ∪ l) ∪ m ≅⟨ i ⟩≅ k ∪ (l ∪ m)
≅ν  (union-assoc k)    =  ∨-assoc (ν k) _ _
≅δ  (union-assoc k) a  =  union-assoc (δ k a)
\end{code}
}

% -- Union laws

\newcommand{\aunioncomm}{
\begin{code}

union-comm : ∀{i} (l k : Lang ∞) → l ∪ k ≅⟨ i ⟩≅ k ∪ l
≅ν  (union-comm l k)    =  ∨-comm (ν l) _
≅δ  (union-comm l k) a  =  union-comm (δ l a) (δ k a)
\end{code}
}

% -- Union laws

\newcommand{\aunionidem}{
\begin{code}

union-idem : ∀{i} (l : Lang ∞) → l ∪ l ≅⟨ i ⟩≅ l
≅ν  (union-idem l)    =  ∨-idem _
≅δ  (union-idem l) a  =  union-idem (δ l a)
\end{code}
}

% -- Union laws

\newcommand{\aunionemptyl}{
\begin{code}

union-emptyˡ : ∀{i} {l : Lang ∞} → ∅ ∪ l ≅⟨ i ⟩≅ l
≅ν  union-emptyˡ    =  refl
≅δ  union-emptyˡ a  =  union-emptyˡ

\end{code}
}

% -- Union laws

\newcommand{\aunionemptyr}{
\begin{code}

union-emptyʳ : ∀{i} {l : Lang ∞} → l ∪ ∅ ≅⟨ i ⟩≅ l
≅ν  union-emptyʳ    =  ∨-false _
≅δ  union-emptyʳ a  =  union-emptyʳ

\end{code}
}

% -- Union laws

\AgdaHide{
\begin{code}

union-top : ∀{i} {l : Lang ∞} → all ∪ l ≅⟨ i ⟩≅ all
≅ν  union-top    =  refl
≅δ  union-top a  =  union-top

union-congˡ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → l ∪ m ≅⟨ i ⟩≅ k ∪ m
≅ν  (union-congˡ p) rewrite ≅ν p  =  refl
≅δ  (union-congˡ p) a  =  union-congˡ (≅δ p a)

union-congʳ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → m ∪ l ≅⟨ i ⟩≅ m ∪ k
≅ν  (union-congʳ p) rewrite ≅ν p  =  refl
≅δ  (union-congʳ p) a  =  union-congʳ (≅δ p a)
\end{code}
}

% union congruence

\newcommand{\aunioncong}{
\begin{code}

union-cong : ∀{i}{k k′ l l′ : Lang ∞}
  (p : k ≅⟨ i ⟩≅ k′) (q : l ≅⟨ i ⟩≅ l′) → k ∪ l ≅⟨ i ⟩≅ k′ ∪ l′
≅ν  (union-cong p q)    =  cong₂ _∨_   (≅ν p)    (≅ν q)
≅δ  (union-cong p q) a  =  union-cong  (≅δ p a)  (≅δ q a)

\end{code}
}
% ≅ν  (union-cong p q) rewrite ≅ν p | ≅ν q  =  refl


\AgdaHide{
\begin{code}


-- Language union forms an idempotent commutative monoid.

union-icm : (i : Size) → IdempotentCommutativeMonoid _ _
union-icm i = record
  { Carrier  =  Lang ∞
  ; _≈_      =  λ l l′ → l ≅⟨ i ⟩≅ l′
  ; _∙_      =  _∪_
  ; ε        =  ∅
  ; isIdempotentCommutativeMonoid  =  record
    { isCommutativeMonoid          =  record
      { isMonoid                   =  record
        { isSemigroup              =  record
          { isMagma                =  record
            { isEquivalence        =  ≅isEquivalence i
            ; ∙-cong               =  union-cong
            }
          ; assoc                  =  λ x y z → union-assoc x
          }
        ; identity                 =  (λ l → union-emptyˡ) , (λ l → union-emptyʳ)
        }
      ; comm                       =  union-comm
      }
    ; idem                         =  union-idem
    }
  }

-- Specialized laws for union

union-swap23 : ∀{i} (k {l m} : Lang ∞) →
  (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ l
union-swap23 {i} k {l} {m} = prove 3 ((x ⊕ y) ⊕ z) ((x ⊕ z) ⊕ y) (k ∷ l ∷ m ∷ [])
  where
  open ICMSolver (union-icm i)
  x  =  var zero
  y  =  var (suc zero)
  z  =  var (suc (suc zero))

union-swap24 : ∀{i} {k l m n : Lang ∞} →
  (k ∪ l) ∪ (m ∪ n) ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ n)
union-swap24 {i} {k} {l} {m} {n} = prove 4 ((x ⊕ y) ⊕ (z ⊕ u)) ((x ⊕ z) ⊕ (y ⊕ u)) (k ∷ l ∷ m ∷ n ∷ [])
  where
  open ICMSolver (union-icm i)
  x  =  var zero
  y  =  var (suc zero)
  z  =  var (suc (suc zero))
  u  =  var (suc (suc (suc zero)))
\end{code}
}
\newcommand{\aunionuniondistr}{
\begin{code}

union-union-distr : ∀{i} (k {l m} : Lang ∞) →
  (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ m)

\end{code}
}
\AgdaHide{
\begin{code}
union-union-distr {i} k {l} {m} = prove 3 ((x ⊕ y) ⊕ z) ((x ⊕ z) ⊕ (y ⊕ z)) (k ∷ l ∷ m ∷ [])
  where
  open ICMSolver (union-icm i)
  x  =  var zero
  y  =  var (suc zero)
  z  =  var (suc (suc zero))

-- Long manual proof:

-- union-union-distr : ∀{i} (k {l m} : Lang ∞) →
--   (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ m)
-- union-union-distr k {l} {m} = begin
--     (k ∪ l) ∪ m
--   ≈⟨ {!!} ⟩
--     (k ∪ l) ∪ (m ∪ m)
--   ≈⟨ {!!} ⟩
--     ((k ∪ l) ∪ m) ∪ m
--   ≈⟨ {!!} ⟩
--     (k ∪ (l ∪ m)) ∪ m
--   ≈⟨ {!!} ⟩
--     (k ∪ (m ∪ l)) ∪ m
--   ≈⟨ {!!} ⟩
--     ((k ∪ m) ∪ l) ∪ m
--   ≈⟨ {!!} ⟩
--     (k ∪ m) ∪ (l ∪ m)
--   ∎
--   where open EqR (Bis _)

-- Concatenation laws

-- Concatenation distributes over union
\end{code}
}
\newcommand{\aconcatuniondistribl}{
\begin{code}

concat-union-distribˡ : ∀{i} (k {l m} : Lang ∞) →
  (k ∪ l) · m ≅⟨ i ⟩≅ (k · m) ∪ (l · m)

\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-union-distribˡ k) = ∧-∨-distribʳ _ (ν k) _
≅δ (concat-union-distribˡ k {l} {m}) a with ν k | ν l

... | true | true = begin

    (δ k a ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ (δ k a)) ⟩
    (δ k a · m ∪ δ l a · m) ∪ δ m a
  ≈⟨ union-union-distr _ ⟩
    (δ k a · m ∪ δ m a) ∪ (δ l a · m ∪ δ m a)
  ∎ where open EqR (Bis _)

... | true | false = begin

    (δ k a ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ (δ k a)) ⟩
    (δ k a · m ∪ δ l a · m) ∪ δ m a
  ≈⟨ union-swap23 _ ⟩
    δ k a · m ∪ δ m a ∪ δ l a · m
  ∎ where open EqR (Bis _)

... | false | true =  begin

    (δ k a ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ (δ k a)) ⟩
    (δ k a · m ∪ δ l a · m) ∪ δ m a
  ≈⟨ union-assoc _ ⟩
    δ k a · m ∪ (δ l a · m ∪ δ m a)
  ∎ where open EqR (Bis _)

... | false | false = concat-union-distribˡ (δ k a)
\end{code}
}

% ≅δ (concat-union-distribʳ k {l} {m}) a | true = begin
%   --   δ (k · (l ∪ m)) a
%   -- ≡⟨⟩
%     δ k a · (l ∪ m) ∪ (δ l a ∪ δ m a)
%   ≈⟨ union-congˡ (concat-union-distribʳ (δ k a)) ⟩
%     (δ k a · l ∪ δ k a · m) ∪ (δ l a ∪ δ m a)
%   ≈⟨ union-swap24 ⟩
%     (δ k a · l ∪ δ l a) ∪ (δ k a · m ∪ δ m a)
%   -- ≡⟨⟩
%   --   δ ((k · l) ∪ (k · m)) a
%   ∎
%   where open EqR (Bis _)

\newcommand{\aconcatuniondistribr}{
\begin{code}
concat-union-distribʳ : ∀{i} (k {l m} : Lang ∞) →
  k · (l ∪ m) ≅⟨ i ⟩≅ (k · l) ∪ (k · m)

≅ν (concat-union-distribʳ k) = ∧-∨-distribˡ (ν k) _ _
≅δ (concat-union-distribʳ k) a with ν k

≅δ (concat-union-distribʳ k {l} {m}) a | true = begin
    δ k a · (l ∪ m) ∪ (δ l a ∪ δ m a)
  ≈⟨ union-congˡ (concat-union-distribʳ (δ k a)) ⟩
    (δ k a · l ∪ δ k a · m) ∪ (δ l a ∪ δ m a)
  ≈⟨ union-swap24 ⟩
    (δ k a · l ∪ δ l a) ∪ (δ k a · m ∪ δ m a)
  ∎
  where open EqR (Bis _)

≅δ (concat-union-distribʳ k) a | false = concat-union-distribʳ (δ k a)
\end{code}
}

% -- Concatenation is congruence

\newcommand{\aconcatcongl}{
\begin{code}

concat-congˡ : ∀{i} {m l k : Lang ∞}
  → l        ≅⟨ i ⟩≅  k
  → l  ·  m  ≅⟨ i ⟩≅  k  ·  m
\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-congˡ p) rewrite ≅ν p = refl
≅δ (concat-congˡ {l = l}{k = k} p) a with ν l | ν k | ≅ν p
≅δ (concat-congˡ p) a | false | false | refl = concat-congˡ (≅δ p a)
≅δ (concat-congˡ p) a | true  | true  | refl = union-congˡ (concat-congˡ (≅δ p a)) --
≅δ (concat-congˡ p) a | false | true  | ()
≅δ (concat-congˡ p) a | true  | false | ()

\end{code}
}
\newcommand{\aconcatcongr}{
\begin{code}

concat-congʳ : ∀{i} {m l k : Lang ∞}
  →       l  ≅⟨ i ⟩≅        k
  → m  ·  l  ≅⟨ i ⟩≅  m  ·  k

\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-congʳ p) rewrite ≅ν p = refl
≅δ (concat-congʳ {m = m} p) a with ν m
≅δ (concat-congʳ p) a | false = concat-congʳ p
≅δ (concat-congʳ p) a | true  = union-cong (concat-congʳ p) (≅δ p a)

-- TODO
-- concat-cong : ∀{i}{k k′ l l′ : Lang ∞} (p : k ≅⟨ i ⟩≅ k′) (q : l ≅⟨ i ⟩≅ l′) → k · l ≅⟨ i ⟩≅ k′ · l′
-- ≅ν (concat-cong p q) rewrite ≅ν p | ≅ν q = refl
-- ≅δ (concat-cong p q) a = {!TODO!} -- concat-cong (≅δ p a) (≅δ q a)

-- Associativity of concatenation
--
-- uses concat-union-distribˡ

\end{code}
}
\newcommand{\aconcatassoc}{
\begin{code}

concat-assoc : ∀{i} (k {l m} : Lang ∞) → (k · l) · m ≅⟨ i ⟩≅ k · (l · m)

\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-assoc k)   = ∧-assoc (ν k) _ _
≅δ (concat-assoc k) a with ν k
≅δ (concat-assoc k    ) a | false = concat-assoc (δ k a)
≅δ (concat-assoc k {l} {m}) a | true with ν l
... | true  = begin

    (δ k a · l ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ _) ⟩
    ((δ k a · l) · m ∪ δ l a · m) ∪ δ m a
  ≈⟨  union-assoc _ ⟩
    (δ k a · l) · m ∪ (δ l a · m ∪ δ m a)
  ≈⟨ union-congˡ (concat-assoc (δ k a)) ⟩
    δ k a · (l · m) ∪ (δ l a · m ∪ δ m a)
  ∎
  where open EqR (Bis _)

... | false = begin

    (δ k a · l ∪ δ l a) · m
  ≈⟨ concat-union-distribˡ _ ⟩
    (δ k a · l) · m ∪ δ l a · m
  ≈⟨ union-congˡ (concat-assoc (δ k a)) ⟩
    δ k a · (l · m) ∪ δ l a · m
  ∎
  where open EqR (Bis _)

\end{code}
}
\newcommand{\aconcatemptyl}{
\begin{code}

concat-emptyˡ  : ∀{i} l → ∅ · l ≅⟨ i ⟩≅ ∅
\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-emptyˡ l) = refl
≅δ (concat-emptyˡ l) a = concat-emptyˡ l

\end{code}
}
\newcommand{\aconcatemptyr}{
\begin{code}
concat-emptyʳ  : ∀{i} l → l · ∅ ≅⟨ i ⟩≅ ∅
\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-emptyʳ l) = ∧-false (ν l)
≅δ (concat-emptyʳ l) a with ν l
... | false = concat-emptyʳ (δ l a)
... | true = begin
    δ l a · ∅ ∪ ∅
  ≈⟨  union-emptyʳ ⟩
    δ l a · ∅
  ≈⟨  concat-emptyʳ (δ l a) ⟩
    ∅
  ∎ where open EqR (Bis _)
\end{code}
}
\newcommand{\aconcatunitl}{
\begin{code}

concat-unitˡ   : ∀{i} l → ε · l ≅⟨ i ⟩≅ l
\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-unitˡ l) = refl
≅δ (concat-unitˡ l) a = begin
    ∅ · l ∪ δ l a
  ≈⟨ union-congˡ (concat-emptyˡ l) ⟩
    ∅  ∪ δ l a
  ≈⟨ union-emptyˡ ⟩
    δ l a
  ∎ where open EqR (Bis _)
\end{code}
}
\newcommand{\aconcatunitr}{
\begin{code}
concat-unitʳ   : ∀{i} l → l · ε ≅⟨ i ⟩≅ l
\end{code}
}
\AgdaHide{
\begin{code}
≅ν (concat-unitʳ l)    = ∧-true _
≅δ (concat-unitʳ l) a  with ν l
... | false  =  concat-unitʳ (δ l a)
... | true   =  begin
    δ l a · ε ∪ ∅
  ≈⟨  union-emptyʳ ⟩
    δ l a · ε
  ≈⟨  concat-unitʳ (δ l a) ⟩
    δ l a
  ∎ where open EqR (Bis _)
\end{code}
}
\AgdaHide{
\begin{code}

-- Specialized laws for union and concat

union-concat-empty : ∀{i l l′} → ∅ · l ∪ l′ ≅⟨ i ⟩≅ l′
≅ν union-concat-empty = refl
≅δ union-concat-empty a = union-concat-empty


-- Laws of the Kleene star

\end{code}
}
\newcommand{\astarempty}{
\begin{code}

star-empty : ∀{i} → ∅ * ≅⟨ i ⟩≅ ε

\end{code}
}
\AgdaHide{
\begin{code}
≅ν star-empty = refl
≅δ star-empty a = concat-emptyˡ _

\end{code}
}
\AgdaHide{
\begin{code}
star-unit : ∀{i} → ε * ≅⟨ i ⟩≅ ε
\end{code}
}
\AgdaHide{
\begin{code}
≅ν star-unit = refl
≅δ star-unit a = concat-emptyˡ _

\end{code}
}
\AgdaHide{
\begin{code}
\end{code}
}
\newcommand{\astarconcatidem}{
\begin{code}

star-concat-idem : ∀{i} (l : Lang ∞) → l * · l * ≅⟨ i ⟩≅ l *
≅ν (star-concat-idem l)    =  refl
≅δ (star-concat-idem l) a  =  begin
    δ l a · l * · l * ∪ δ l a · l *
  ≈⟨ union-congˡ (concat-assoc _) ⟩
    δ l a · (l * · l *) ∪ δ l a · l *
  ≈⟨ union-congˡ (concat-congʳ (star-concat-idem _)) ⟩
    δ l a · l * ∪ δ l a · l *
  ≈⟨ union-idem _ ⟩
    δ l a · l *
  ∎ where open EqR (Bis _)

\end{code}
}
\AgdaHide{
\begin{code}
\end{code}
}
\newcommand{\astaridem}{
\begin{code}

star-idem : ∀{i} (l : Lang ∞) → (l *) * ≅⟨ i ⟩≅ l *
≅ν (star-idem l)    =  refl
≅δ (star-idem l) a  =  begin
  δ l a · l * · (l *) *  ≈⟨ concat-congʳ (star-idem l) ⟩
  δ l a · l * · l *      ≈⟨ concat-assoc (δ l a) ⟩
  δ l a · (l * · l *)    ≈⟨ concat-congʳ (star-concat-idem l) ⟩
  δ l a · l *
  ∎ where open EqR (Bis _)

\end{code}
}

% -- Recursion equation for the Kleene star

\newcommand{\astarrec}{
\begin{code}

star-rec : ∀{i} (l : Lang ∞) → l * ≅⟨ i ⟩≅ ε ∪ l ⁺

\end{code}
}
\AgdaHide{
\begin{code}
≅ν (star-rec l) = refl
≅δ (star-rec l) a with ν l
... | true  = begin
    δ l a · l *
  ≈⟨ ≅sym (union-idem _) ⟩
    (δ l a · l * ∪ δ l a · l *)
  ≈⟨ ≅sym union-emptyˡ ⟩
    ∅ ∪ (δ l a · l * ∪ δ l a · l *)
  ∎
  where open EqR (Bis _)
... | false = ≅sym union-emptyˡ

-- Kleene star absorbs ε

unit-union-star : ∀{i} (l : Lang ∞) → ε ∪ (l *) ≅⟨ i ⟩≅ (l *)
≅ν (unit-union-star l)   = refl
≅δ (unit-union-star l) a = union-emptyˡ

star-union-unit : ∀{i} (l : Lang ∞) → (l *) ∪ ε ≅⟨ i ⟩≅ (l *)
star-union-unit l = ≅trans (union-comm (l *) ε) (unit-union-star _)

empty-star-union-star : ∀{i} (l : Lang ∞) → (∅ *) ∪ (l *) ≅⟨ i ⟩≅ (l *)
≅ν (empty-star-union-star l)   = refl
≅δ (empty-star-union-star l) a =  ≅trans (union-congˡ (concat-emptyˡ _)) union-emptyˡ

star-union-empty-star : ∀{i} (l : Lang ∞) → (l *) ∪ (∅ *) ≅⟨ i ⟩≅ (l *)
star-union-empty-star l = ≅trans (union-comm (l *) (∅ *)) (empty-star-union-star _)


-- Star composed with some language
-- r*·a = r·r*·a + a

\end{code}
}
\newcommand{\astarconcat}{
\begin{code}
star-concat : ∀{i} (k {m} : Lang ∞) → k * · m ≅⟨ i ⟩≅ k · (k * · m) ∪ m
\end{code}
}
\AgdaHide{
\begin{code}
≅ν (star-concat k {m}) = ∨-absorbs-∧ (ν k) (ν m) -- absorption A = (B ∧ A) ∨ A
≅δ (star-concat k {m}) a with ν k
... | false = union-congˡ (concat-assoc _)
... | true = begin
    δ k a · k * · m ∪ δ m a
  ≈⟨  prove 2 (x ⊕ y) ((x ⊕ (x ⊕ y)) ⊕ y) ((δ k a · k * · m) ∷ δ m a ∷ [])  ⟩
    δ k a · k * · m ∪ (δ k a · k * · m ∪ δ m a) ∪ δ m a
  ≈⟨ union-congˡ (union-congˡ (concat-assoc _)) ⟩
    δ k a · (k * · m) ∪ (δ k a · k * · m ∪ δ m a) ∪ δ m a
  ∎ where
    open EqR (Bis _)
    open ICMSolver (union-icm _)
    x y : Expr 2
    x = var zero
    y = var (suc zero)

-- Arden's rule
-- L = K·L + M  ==> L = K*·M    (unless ν k)

-- Show: δ L a = δ K a ∙ K* ∙ M ∪ δ M a
-- Hyp : δ L a = δ K a ∙ L      ∪ δ M a

\end{code}
}
\newcommand{\astarfromrec}{
\begin{code}

star-from-rec : ∀{i} (k {l m} : Lang ∞)
   → ν k ≡ false
   → l ≅⟨ i ⟩≅ k · l ∪ m
   → l ≅⟨ i ⟩≅ k * · m

≅ν (star-from-rec k n p) with ≅ν p
... | b rewrite n = b

≅δ (star-from-rec k {l} {m} n p) a with ≅δ p a
... | q rewrite n = begin
     δ l a
  ≈⟨ q ⟩
     δ k a · l ∪ δ m a
  ≈⟨ union-congˡ (concat-congʳ (star-from-rec k {l} {m} n p)) ⟩
     δ k a · (k * · m) ∪ δ m a
  ≈⟨ union-congˡ (≅sym (concat-assoc (δ k a))) ⟩
     δ k a · k * · m ∪ δ m a
  ∎ where open EqR (Bis _)

\end{code}
}

% \newcommand{\aplusdef}{
% \begin{code}
%
% plus-def : ∀{i} (l : Lang ∞) → l ⁺ ≅⟨ i ⟩≅ l · l *
% ≅ν (plus-def l) = sym (∧-true _)
% ≅δ (plus-def l) a with ν l
% ... | false  =  ≅refl
% ... | true   =  ≅sym (union-idem _)
%
% \end{code}
% }

%  -- specialized law used for power automaton construction

\AgdaHide{
\begin{code}
concat-maybe-star : ∀{i} (l : Lang ∞) →  (ε ∪ l) · l * ≅⟨ i ⟩≅ l *
≅ν (concat-maybe-star l) = refl
≅δ (concat-maybe-star l) a = begin
    (∅ ∪ δ l a) · l * ∪ δ l a · l *
  ≈⟨ union-congˡ (concat-congˡ union-emptyˡ) ⟩
    δ l a · l * ∪ δ l a · l *
  ≈⟨ union-idem _ ⟩
    δ l a · l *
  ∎ where open EqR (Bis _)

-- -}
-- -}
-- -}
\end{code}
}
