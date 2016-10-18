open import Library

module Trie where

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

record Trie i A B : Set where
  coinductive
  field
    ν : B   -- Label, e.g. Bool for formal languages or Maybe C for dictionaries.
    δ : ∀{j : Size< i} (a : A) → Trie j A B
open Trie public

-- Bisimilarity

infix   1 _≅⟨_⟩≅_

record _≅⟨_⟩≅_ {A B} (l : Trie ∞ A B) i (k : Trie ∞ A B) : Set where
  coinductive
  field
    ≅ν : ν l ≡ ν k
    ≅δ : ∀{j : Size< i} (a : A) → δ l a ≅⟨ j ⟩≅ δ k a
open _≅⟨_⟩≅_ public

_≅_ : ∀{A B} (l k : Trie ∞ A B) → Set
l ≅ k = l ≅⟨ ∞ ⟩≅ k

-- Equivalence relation laws

≅refl : ∀{i A B} {l : Trie ∞ A B} → l ≅⟨ i ⟩≅ l
≅ν ≅refl   = refl
≅δ ≅refl a = ≅refl

≅sym : ∀{i A B} {k l : Trie ∞ A B} (p : l ≅⟨ i ⟩≅ k) → k ≅⟨ i ⟩≅ l
≅ν (≅sym p)   = sym (≅ν p)
≅δ (≅sym p) a = ≅sym (≅δ p a)

≅trans : ∀{i A B} {k l m : Trie ∞ A B} (p : k ≅⟨ i ⟩≅ l) (q : l ≅⟨ i ⟩≅ m) → k ≅⟨ i ⟩≅ m
≅ν (≅trans p q)   = trans (≅ν p) (≅ν q)
≅δ (≅trans p q) a = ≅trans (≅δ p a) (≅δ q a)
-- Setoid

≅isEquivalence : ∀(i : Size) (A B : Set) → IsEquivalence (λ (l l' : Trie ∞ A B) → l ≅⟨ i ⟩≅ l')
IsEquivalence.refl  (≅isEquivalence i A B) = ≅refl
IsEquivalence.sym   (≅isEquivalence i A B) = ≅sym
IsEquivalence.trans (≅isEquivalence i A B) = ≅trans

Bis : ∀(i : Size) (A B : Set) → Setoid lzero lzero
Setoid.Carrier       (Bis i A B) = Trie ∞ A B
Setoid._≈_           (Bis i A B) = λ l k → l ≅⟨ i ⟩≅ k
Setoid.isEquivalence (Bis i A B) = ≅isEquivalence i A B

-- Lookup

subtrie : ∀{A B} → Trie ∞ A B → List A → Trie ∞ A B
subtrie t []       = t
subtrie t (a ∷ as) = subtrie (δ t a) as

lookup : ∀{A B} → Trie ∞ A B → List A → B
lookup t l = ν (subtrie t l)

-- Trie from function

trie : ∀{i A B} (mem : List A → B) → Trie i A B
ν (trie mem)   = mem []
δ (trie mem) a = trie λ as → mem (a ∷ as)

-- This makes Trie isomophic to (List A → Bool)

trie-lookup : ∀{i A B} (t : Trie ∞ A B) → trie (lookup t) ≅⟨ i ⟩≅ t
≅ν (trie-lookup t)   = refl
≅δ (trie-lookup t) a = trie-lookup (δ t a)

lookup-trie : ∀{A B} (f : List A → B) as → lookup (trie f) as ≡ f as
lookup-trie f [] = refl
lookup-trie f (a ∷ as) = lookup-trie (λ l → f (a ∷ l)) as

-- Constant trie definable as
-- trie (λ _ → b)

-- Mapping could be defined as
-- map f t = trie ∘ f ∘ lookup t

map : ∀{i A B C} (f : B → C) (t : Trie i A B) → Trie i A C
ν (map f t) = f (ν t)
δ (map f t) a = map f (δ t a)

-- Zipping

zipWith : ∀{i A B C D} (f : B → C → D) (t : Trie i A B) (u : Trie i A C) → Trie i A D
ν (zipWith f t u) = f (ν t) (ν u)
δ (zipWith f t u) a = zipWith f (δ t a) (δ u a)

{-

infixl  4 _∪_
infixl  5 _∩_
infixl  6 _·_
infixr 15 _^_
infixr 15 _*

-- empty trieuage

∅ : ∀{i} → Trie i
ν ∅   = false
δ ∅ x = ∅

-- trivial trieuage (containing every word)

all : ∀{i} → Trie i
ν all   = true
δ all x = all

-- trieuage consisting of the empty word

ε : ∀{i} → Trie i
ν ε   = true
δ ε x = ∅

-- trieuage consisting of a single single-character word

char : ∀{i} (a : A) → Trie i
ν (char a) = false
δ (char a) x with a ≟ x
... | yes _ = ε
... | no  _ = ∅

-- trieuage complement

compl_ : ∀{i} (l : Trie i) → Trie i
ν (compl l)   = not (ν l)
δ (compl l) x = compl δ l x

-- intersection of trieuages

_∩_ : ∀{i} (k l : Trie i) → Trie i
ν (k ∩ l)   = ν k ∧ ν l
δ (k ∩ l) x = δ k x ∩ δ l x

-- union of trieuages

_∪_ : ∀{i} (k l : Trie i) → Trie i
ν (k ∪ l)   = ν k ∨ ν l
δ (k ∪ l) x = δ k x ∪ δ l x

-- concatenation of trieuages

_·_ : ∀{i} (k l : Trie i) → Trie i
ν (k · l)   = ν k ∧ ν l
δ (k · l) x = let k'l = δ k x · l in
  if ν k then k'l ∪ δ l x else k'l
-- δ (k · l) x = if ν k then k'l ∪ δ l x else k'l
--   where k'l = δ k x · l
-- OR: δ (k · l) x = (δ k x · l) ∪ (if ν k then δ l x else ∅)

-- Kleene star

_* : ∀{i} (l : Trie i) → Trie i
ν (l *)   = true
δ (l *) x = δ l x · (l *)

-- Exponentiation

_^_ : ∀{i} (l : Trie i) (n : ℕ) → Trie i
l ^ zero  = ε
l ^ suc n = l · l ^ n

-- Examples

aⁿbⁿ! : ∀{i} (a b : A) (n : ℕ) → Trie i
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
thenbs : ∀{i} (a b : A) (n : ℕ) → Trie i
ν (thenbs a b n)   = zero? n
δ (thenbs a b n) x = case (thisThatElse a b x) of \
  { (this p) → thenbs a b (suc n)
  ; (that p) → char b ^ n
  ; _        → ∅
  }

-- -- Does not reduce, see issue #...!
-- thenbs : ∀{i} (a b : A) (n : ℕ) → Trie i
-- ν (thenbs a b zero)    = true
-- ν (thenbs a b (suc _)) = false
-- δ (thenbs a b n)       x with thisThatElse a b x
-- δ (thenbs a b n)       x | this p = thenbs a b (suc n)
-- δ (thenbs a b (suc n)) x | that p = char b ^ n
-- δ (thenbs a b n)       x | _      = ∅

aⁿbⁿ : ∀{i} (a b : A) → Trie i
aⁿbⁿ a b = thenbs a b zero

-- Trieuage equality

record _≅⟨_⟩≅_ (l : Trie ∞) i (k : Trie ∞) : Set where
  coinductive
  field
    ≅ν : ν l ≡ ν k
    ≅δ : ∀{j : Size< i} (a : A) → δ l a ≅⟨ j ⟩≅ δ k a
open _≅⟨_⟩≅_ public

_≅_ : ∀ (l k : Trie ∞) → Set
l ≅ k = l ≅⟨ ∞ ⟩≅ k

-- Equivalence relation laws

≅refl : ∀{i} {l : Trie ∞} → l ≅⟨ i ⟩≅ l
≅ν ≅refl   = refl
≅δ ≅refl a = ≅refl

≅sym : ∀{i} {k l : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → k ≅⟨ i ⟩≅ l
≅ν (≅sym p)   = sym (≅ν p)
≅δ (≅sym p) a = ≅sym (≅δ p a)

≅trans : ∀{i} {k l m : Trie ∞} (p : k ≅⟨ i ⟩≅ l) (q : l ≅⟨ i ⟩≅ m) → k ≅⟨ i ⟩≅ m
≅ν (≅trans p q)   = trans (≅ν p) (≅ν q)
≅δ (≅trans p q) a = ≅trans (≅δ p a) (≅δ q a)

-- Congruence law (UNPROVABLE)

-- ≅cong : ∀{i} (f : Trie ∞ → Trie ∞) {k l : Trie ∞} (p : l ≅⟨ i ⟩≅ k) →
--   f l ≅⟨ i ⟩≅ f k
-- ≅ν (≅cong f p) = {!≅ν p!}
-- ≅δ (≅cong f p) a = {!!}


-- Complement laws

compl-empty : ∀{i} → compl ∅ ≅⟨ i ⟩≅ all
≅ν compl-empty   = refl
≅δ compl-empty a = compl-empty

compl-top : ∀{i} → compl all ≅⟨ i ⟩≅ ∅
≅ν compl-top   = refl
≅δ compl-top a = compl-top

compl-cong : ∀{i}{l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → compl l ≅⟨ i ⟩≅ compl k
≅ν (compl-cong p) rewrite ≅ν p = refl
≅δ (compl-cong p) a = compl-cong (≅δ p a)

-- Intersection laws

inter-assoc : ∀{i} (k {l m} : Trie ∞) → (k ∩ l) ∩ m ≅⟨ i ⟩≅ k ∩ (l ∩ m)
≅ν (inter-assoc k)   =  ∧-assoc (ν k) _ _
≅δ (inter-assoc k) a = inter-assoc _

inter-comm : ∀{i} (l {k} : Trie ∞) → l ∩ k ≅⟨ i ⟩≅ k ∩ l
≅ν (inter-comm l)   = ∧-comm (ν l) _
≅δ (inter-comm l) a = inter-comm (δ l a)

inter-idem : ∀{i} (l : Trie ∞) → l ∩ l ≅⟨ i ⟩≅ l
≅ν (inter-idem l)   = ∧-idempotent (ν l)
≅δ (inter-idem l) a = inter-idem (δ l a)

inter-empty : ∀{i} {l : Trie ∞} → ∅ ∩ l ≅⟨ i ⟩≅ ∅
≅ν inter-empty   = refl
≅δ inter-empty a = inter-empty

inter-top : ∀{i} {l : Trie ∞} → all ∩ l ≅⟨ i ⟩≅ l
≅ν inter-top   = refl
≅δ inter-top a = inter-top

inter-congˡ : ∀{i}{m l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → l ∩ m ≅⟨ i ⟩≅ k ∩ m
≅ν (inter-congˡ p) rewrite ≅ν p = refl
≅δ (inter-congˡ p) a = inter-congˡ (≅δ p a)

inter-congʳ : ∀{i}{m l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → m ∩ l ≅⟨ i ⟩≅ m ∩ l
≅ν (inter-congʳ p) rewrite ≅ν p = refl
≅δ (inter-congʳ p) a = inter-congʳ (≅δ p a)

-- Union laws

union-assoc : ∀{i} (k {l m} : Trie ∞) → (k ∪ l) ∪ m ≅⟨ i ⟩≅ k ∪ (l ∪ m)
≅ν (union-assoc k)   = ∨-assoc (ν k) _ _
≅δ (union-assoc k) a = union-assoc _

union-comm : ∀{i} (l k : Trie ∞) → l ∪ k ≅⟨ i ⟩≅ k ∪ l
≅ν (union-comm l k)   = ∨-comm (ν l) _
≅δ (union-comm l k) a = union-comm (δ l a) (δ k a)

union-idem : ∀{i} {l : Trie ∞} → l ∪ l ≅⟨ i ⟩≅ l
≅ν union-idem   = ∨-idempotent _
≅δ union-idem a = union-idem

union-empty : ∀{i} {l : Trie ∞} → ∅ ∪ l ≅⟨ i ⟩≅ l
≅ν union-empty   = refl
≅δ union-empty a = union-empty

union-top : ∀{i} {l : Trie ∞} → all ∪ l ≅⟨ i ⟩≅ all
≅ν union-top   = refl
≅δ union-top a = union-top

union-congˡ : ∀{i}{m l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → l ∪ m ≅⟨ i ⟩≅ k ∪ m
≅ν (union-congˡ p) rewrite ≅ν p = refl
≅δ (union-congˡ p) a = union-congˡ (≅δ p a)

union-congʳ : ∀{i}{m l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → m ∪ l ≅⟨ i ⟩≅ m ∪ k
≅ν (union-congʳ p) rewrite ≅ν p = refl
≅δ (union-congʳ p) a = union-congʳ (≅δ p a)

union-cong : ∀{i}{k k' l l' : Trie ∞} (p : k ≅⟨ i ⟩≅ k') (q : l ≅⟨ i ⟩≅ l') → k ∪ l ≅⟨ i ⟩≅ k' ∪ l'
≅ν (union-cong p q) rewrite ≅ν p | ≅ν q = refl
≅δ (union-cong p q) a = union-cong (≅δ p a) (≅δ q a)

-- Trieuage union forms an idempotent commutative monoid.

union-icm : (i : Size) → IdempotentCommutativeMonoid _ _
union-icm i = record
  { Carrier = Trie ∞
  ; _≈_ = λ l l' → l ≅⟨ i ⟩≅ l'
  ; _∙_ = _∪_
  ; ε = ∅
  ; isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = ≅isEquivalence i
        ; assoc = λ x y z → union-assoc x
        ; ∙-cong = union-cong
        }
      ; identityˡ = λ l → union-empty
      ; comm = union-comm
      }
    ; idem = λ l → union-idem
    }
  }

-- Specialized laws for union

union-swap23 : ∀{i} (k {l m} : Trie ∞) →
  (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ l
union-swap23 {i} k {l} {m} = prove 3 ((x ⊕ y) ⊕ z) ((x ⊕ z) ⊕ y) (k ∷ l ∷ m ∷ [])
  where
  open ICMSolver (union-icm i)
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))

union-swap24 : ∀{i} {k l m n : Trie ∞} →
  (k ∪ l) ∪ (m ∪ n) ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ n)
union-swap24 {i} {k} {l} {m} {n} = prove 4 ((x ⊕ y) ⊕ (z ⊕ u)) ((x ⊕ z) ⊕ (y ⊕ u)) (k ∷ l ∷ m ∷ n ∷ [])
  where
  open ICMSolver (union-icm i)
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))
  u = var (suc (suc (suc zero)))

union-union-distr : ∀{i} (k {l m} : Trie ∞) →
  (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ m)
union-union-distr {i} k {l} {m} = prove 3 ((x ⊕ y) ⊕ z) ((x ⊕ z) ⊕ (y ⊕ z)) (k ∷ l ∷ m ∷ [])
  where
  open ICMSolver (union-icm i)
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))

-- Long manual proof:

-- union-union-distr : ∀{i} (k {l m} : Trie ∞) →
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

concat-union-distribˡ : ∀{i} (k {l m} : Trie ∞) → (k ∪ l) · m ≅⟨ i ⟩≅ (k · m) ∪ (l · m)
≅ν (concat-union-distribˡ k) = ∧-∨-distribʳ _ (ν k) _
≅δ (concat-union-distribˡ k {l} {m}) a with ν k | ν l

... | true | true = begin

    (δ k a ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ (δ k a)) ⟩
    (δ k a · m ∪ δ l a · m) ∪ δ m a
  ≈⟨ union-union-distr _ ⟩
    (δ k a · m ∪ δ m a) ∪ (δ l a · m ∪ δ m a)
  ∎
  where open EqR (Bis _)

... | true | false = begin

    (δ k a ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ (δ k a)) ⟩
    (δ k a · m ∪ δ l a · m) ∪ δ m a
  ≈⟨ union-swap23 _ ⟩
    δ k a · m ∪ δ m a ∪ δ l a · m
  ∎
  where open EqR (Bis _)

... | false | true =  begin

    (δ k a ∪ δ l a) · m ∪ δ m a
  ≈⟨ union-congˡ (concat-union-distribˡ (δ k a)) ⟩
    (δ k a · m ∪ δ l a · m) ∪ δ m a
  ≈⟨ union-assoc _ ⟩
    δ k a · m ∪ (δ l a · m ∪ δ m a)
  ∎
  where open EqR (Bis _)

... | false | false = concat-union-distribˡ (δ k a)


concat-union-distribʳ : ∀{i} (k {l m} : Trie ∞) → k · (l ∪ m) ≅⟨ i ⟩≅ (k · l) ∪ (k · m)
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

-- Concatenation is congruence

concat-congˡ : ∀{i}{m l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → l · m ≅⟨ i ⟩≅ k · m
≅ν (concat-congˡ p) rewrite ≅ν p = refl
≅δ (concat-congˡ {l = l}{k = k} p) a with ν l | ν k | ≅ν p
≅δ (concat-congˡ p) a | false | false | refl = concat-congˡ (≅δ p a)
≅δ (concat-congˡ p) a | true  | true  | refl = union-congˡ (concat-congˡ (≅δ p a)) --
≅δ (concat-congˡ p) a | false | true  | ()
≅δ (concat-congˡ p) a | true  | false | ()

concat-congʳ : ∀{i}{m l k : Trie ∞} (p : l ≅⟨ i ⟩≅ k) → m · l ≅⟨ i ⟩≅ m · k
≅ν (concat-congʳ p) rewrite ≅ν p = refl
≅δ (concat-congʳ {m = m} p) a with ν m
≅δ (concat-congʳ p) a | false = concat-congʳ p
≅δ (concat-congʳ p) a | true  = union-cong (concat-congʳ p) (≅δ p a)

-- TODO
-- concat-cong : ∀{i}{k k' l l' : Trie ∞} (p : k ≅⟨ i ⟩≅ k') (q : l ≅⟨ i ⟩≅ l') → k · l ≅⟨ i ⟩≅ k' · l'
-- ≅ν (concat-cong p q) rewrite ≅ν p | ≅ν q = refl
-- ≅δ (concat-cong p q) a = {!TODO!} -- concat-cong (≅δ p a) (≅δ q a)

-- Associativity of concatenation
--
-- uses concat-union-distribˡ

concat-assoc : ∀{i} (k {l m} : Trie ∞) → (k · l) · m ≅⟨ i ⟩≅ k · (l · m)
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

concat-emptyˡ : ∀{i} l → ∅ · l ≅⟨ i ⟩≅ ∅
≅ν (concat-emptyˡ l) = refl
≅δ (concat-emptyˡ l) a = concat-emptyˡ l

-- Laws of the Kleene star

star-empty : ∀{i} → ∅ * ≅⟨ i ⟩≅ ε
≅ν star-empty = refl
≅δ star-empty a = concat-emptyˡ _

star-unit : ∀{i} → ε * ≅⟨ i ⟩≅ ε
≅ν star-unit = refl
≅δ star-unit a = concat-emptyˡ _

star-concat-idem : ∀{i} (l : Trie ∞) → l * · l * ≅⟨ i ⟩≅ l *
≅ν (star-concat-idem l) = refl
≅δ (star-concat-idem l) a = begin
    δ l a · l * · l * ∪ δ l a · l *
  ≈⟨ union-congˡ (concat-assoc _) ⟩
    δ l a · (l * · l *) ∪ δ l a · l *
  ≈⟨ union-congˡ (concat-congʳ (star-concat-idem _)) ⟩
    δ l a · l * ∪ δ l a · l *
  ≈⟨ union-idem ⟩
    δ l a · l *
  ∎
  where open EqR (Bis _)

star-idem : ∀{i} (l : Trie ∞) → (l *) * ≅⟨ i ⟩≅ l *
≅ν (star-idem l) = refl
≅δ (star-idem l) a = begin
  δ l a · l * · (l *) *  ≈⟨ concat-congʳ (star-idem l) ⟩
  δ l a · l * · l *      ≈⟨ concat-assoc (δ l a) ⟩
  δ l a · (l * · l *)    ≈⟨ concat-congʳ (star-concat-idem l) ⟩
  δ l a · l *
  ∎
  where open EqR (Bis _)

-- Recursion equation for the Kleene star

star-rec : ∀{i} (l : Trie ∞) → l * ≅⟨ i ⟩≅ ε ∪ (l · l *)
≅ν (star-rec l) = refl
≅δ (star-rec l) a with ν l
... | true  = begin
    δ l a · l *
  ≈⟨ ≅sym union-idem ⟩
    (δ l a · l * ∪ δ l a · l *)
  ≈⟨ ≅sym union-empty ⟩
    ∅ ∪ (δ l a · l * ∪ δ l a · l *)
  ∎
  where open EqR (Bis _)
... | false = ≅sym union-empty

-- Kleene star absorbs ε

unit-union-star : ∀{i} (l : Trie ∞) → ε ∪ (l *) ≅⟨ i ⟩≅ (l *)
≅ν (unit-union-star l)   = refl
≅δ (unit-union-star l) a = union-empty

star-union-unit : ∀{i} (l : Trie ∞) → (l *) ∪ ε ≅⟨ i ⟩≅ (l *)
star-union-unit l = ≅trans (union-comm (l *) ε) (unit-union-star _)

empty-star-union-star : ∀{i} (l : Trie ∞) → (∅ *) ∪ (l *) ≅⟨ i ⟩≅ (l *)
≅ν (empty-star-union-star l)   = refl
≅δ (empty-star-union-star l) a =  ≅trans (union-congˡ (concat-emptyˡ _)) union-empty

star-union-empty-star : ∀{i} (l : Trie ∞) → (l *) ∪ (∅ *) ≅⟨ i ⟩≅ (l *)
star-union-empty-star l = ≅trans (union-comm (l *) (∅ *)) (empty-star-union-star _)

-}
