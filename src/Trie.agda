open import Library

module _
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

infix   1 _≅⟨_⟩≅_
infix   2 _∈_
infixr 10 ¬_
infixl  4 _∪_
infixl  5 _∩_
infixl  6 _·_
infixr 15 _^_
infixr 15 _*

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

record Lang i : Set where
  coinductive
  field
    ν : Bool -- nullable
    δ : ∀{j : Size< i} → A → Lang j
open Lang

-- Word membership

_∈_ : List A → Lang ∞ → Bool
[]     ∈ l = ν l
a ∷ as ∈ l = as ∈ δ l a

-- Language from word membership

lang : ∀{i} (mem : List A → Bool) → Lang i
ν (lang mem)   = mem []
δ (lang mem) a = lang λ as → mem (a ∷ as)

-- This makes Lang isomophic to (List A → Bool)

-- Constructions of language

-- empty language

∅ : ∀{i} → Lang i
ν ∅   = false
δ ∅ x = ∅

-- trivial language (containing every word)

all : ∀{i} → Lang i
ν all   = true
δ all x = all

-- language consisting of the empty word

ε : ∀{i} → Lang i
ν ε   = true
δ ε x = ∅

-- language consisting of a single single-character word

char : ∀{i} (a : A) → Lang i
ν (char a) = false
δ (char a) x with a ≟ x
... | yes _ = ε
... | no  _ = ∅

-- language complement

¬_ : ∀{i} (l : Lang i) → Lang i
ν (¬ l)   = not (ν l)
δ (¬ l) x = ¬ δ l x

-- intersection of languages

_∩_ : ∀{i} (k l : Lang i) → Lang i
ν (k ∩ l)   = ν k ∧ ν l
δ (k ∩ l) x = δ k x ∩ δ l x

-- union of languages

_∪_ : ∀{i} (k l : Lang i) → Lang i
ν (k ∪ l)   = ν k ∨ ν l
δ (k ∪ l) x = δ k x ∪ δ l x

-- concatenation of languages

_·_ : ∀{i} (k l : Lang i) → Lang i
ν (k · l)   = ν k ∧ ν l
δ (k · l) x = let k'l = δ k x · l in
  if ν k then k'l ∪ δ l x else k'l
-- δ (k · l) x = if ν k then k'l ∪ δ l x else k'l
--   where k'l = δ k x · l
-- OR: δ (k · l) x = (δ k x · l) ∪ (if ν k then δ l x else ∅)

-- Kleene star

_* : ∀{i} (l : Lang i) → Lang i
ν (l *)   = true
δ (l *) x = δ l x · (l *)

-- Exponentiation

_^_ : ∀{i} (l : Lang i) (n : ℕ) → Lang i
l ^ zero  = ε
l ^ suc n = l · l ^ n

-- Examples

aⁿbⁿ : ∀{i} (a b : A) (n : ℕ) → Lang i
aⁿbⁿ a b n = char a ^ n · char b ^ n


-- Language equality

record _≅⟨_⟩≅_ (l : Lang ∞) i (k : Lang ∞) : Set where
  coinductive
  field
    ≅ν : ν l ≡ ν k
    ≅δ : ∀{j : Size< i} (a : A) → δ l a ≅⟨ j ⟩≅ δ k a
open _≅⟨_⟩≅_ public

-- Equivalence relation laws

≅refl : ∀{i} {l : Lang ∞} → l ≅⟨ i ⟩≅ l
≅ν ≅refl   = refl
≅δ ≅refl a = ≅refl

≅sym : ∀{i} {k l : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → k ≅⟨ i ⟩≅ l
≅ν (≅sym p)   = sym (≅ν p)
≅δ (≅sym p) a = ≅sym (≅δ p a)

≅trans : ∀{i} {k l m : Lang ∞} (p : k ≅⟨ i ⟩≅ l) (q : l ≅⟨ i ⟩≅ m) → k ≅⟨ i ⟩≅ m
≅ν (≅trans p q)   = trans (≅ν p) (≅ν q)
≅δ (≅trans p q) a = ≅trans (≅δ p a) (≅δ q a)

-- Congruence law (UNPROVABLE)

-- ≅cong : ∀{i} (f : Lang ∞ → Lang ∞) {k l : Lang ∞} (p : l ≅⟨ i ⟩≅ k) →
--   f l ≅⟨ i ⟩≅ f k
-- ≅ν (≅cong f p) = {!≅ν p!}
-- ≅δ (≅cong f p) a = {!!}

-- Setoid

≅isEquivalence : (i : Size) → IsEquivalence (λ l l' → l ≅⟨ i ⟩≅ l')
IsEquivalence.refl  (≅isEquivalence i) = ≅refl
IsEquivalence.sym   (≅isEquivalence i) = ≅sym
IsEquivalence.trans (≅isEquivalence i) = ≅trans

Bis : ∀(i : Size) → Setoid lzero lzero
Setoid.Carrier       (Bis i) = Lang ∞
Setoid._≈_           (Bis i) = λ l k → l ≅⟨ i ⟩≅ k
Setoid.isEquivalence (Bis i) = ≅isEquivalence i

-- Complement laws

compl-empty : ∀{i} → ¬ ∅ ≅⟨ i ⟩≅ all
≅ν compl-empty   = refl
≅δ compl-empty a = compl-empty

compl-top : ∀{i} → ¬ all ≅⟨ i ⟩≅ ∅
≅ν compl-top   = refl
≅δ compl-top a = compl-top

compl-cong : ∀{i}{l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → ¬ l ≅⟨ i ⟩≅ ¬ k
≅ν (compl-cong p) rewrite ≅ν p = refl
≅δ (compl-cong p) a = compl-cong (≅δ p a)

-- Intersection laws

inter-assoc : ∀{i} (k {l m} : Lang ∞) → (k ∩ l) ∩ m ≅⟨ i ⟩≅ k ∩ (l ∩ m)
≅ν (inter-assoc k)   =  ∧-assoc (ν k) _ _
≅δ (inter-assoc k) a = inter-assoc _

inter-comm : ∀{i} (l {k} : Lang ∞) → l ∩ k ≅⟨ i ⟩≅ k ∩ l
≅ν (inter-comm l)   = ∧-comm (ν l) _
≅δ (inter-comm l) a = inter-comm (δ l a)

inter-idem : ∀{i} (l : Lang ∞) → l ∩ l ≅⟨ i ⟩≅ l
≅ν (inter-idem l)   = ∧-idempotent (ν l)
≅δ (inter-idem l) a = inter-idem (δ l a)

inter-empty : ∀{i} {l : Lang ∞} → ∅ ∩ l ≅⟨ i ⟩≅ ∅
≅ν inter-empty   = refl
≅δ inter-empty a = inter-empty

inter-top : ∀{i} {l : Lang ∞} → all ∩ l ≅⟨ i ⟩≅ l
≅ν inter-top   = refl
≅δ inter-top a = inter-top

inter-congˡ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → l ∩ m ≅⟨ i ⟩≅ k ∩ m
≅ν (inter-congˡ p) rewrite ≅ν p = refl
≅δ (inter-congˡ p) a = inter-congˡ (≅δ p a)

inter-congʳ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → m ∩ l ≅⟨ i ⟩≅ m ∩ l
≅ν (inter-congʳ p) rewrite ≅ν p = refl
≅δ (inter-congʳ p) a = inter-congʳ (≅δ p a)

-- Union laws

union-assoc : ∀{i} (k {l m} : Lang ∞) → (k ∪ l) ∪ m ≅⟨ i ⟩≅ k ∪ (l ∪ m)
≅ν (union-assoc k)   = ∨-assoc (ν k) _ _
≅δ (union-assoc k) a = union-assoc _

union-comm : ∀{i} (l k : Lang ∞) → l ∪ k ≅⟨ i ⟩≅ k ∪ l
≅ν (union-comm l k)   = ∨-comm (ν l) _
≅δ (union-comm l k) a = union-comm (δ l a) (δ k a)

union-idem : ∀{i} {l : Lang ∞} → l ∪ l ≅⟨ i ⟩≅ l
≅ν union-idem   = ∨-idempotent _
≅δ union-idem a = union-idem

union-empty : ∀{i} {l : Lang ∞} → ∅ ∪ l ≅⟨ i ⟩≅ l
≅ν union-empty   = refl
≅δ union-empty a = union-empty

union-top : ∀{i} {l : Lang ∞} → all ∪ l ≅⟨ i ⟩≅ all
≅ν union-top   = refl
≅δ union-top a = union-top

union-congˡ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → l ∪ m ≅⟨ i ⟩≅ k ∪ m
≅ν (union-congˡ p) rewrite ≅ν p = refl
≅δ (union-congˡ p) a = union-congˡ (≅δ p a)

union-congʳ : ∀{i}{m l k : Lang ∞} (p : l ≅⟨ i ⟩≅ k) → m ∪ l ≅⟨ i ⟩≅ m ∪ k
≅ν (union-congʳ p) rewrite ≅ν p = refl
≅δ (union-congʳ p) a = union-congʳ (≅δ p a)

union-cong : ∀{i}{k k' l l' : Lang ∞} (p : k ≅⟨ i ⟩≅ k') (q : l ≅⟨ i ⟩≅ l') → k ∪ l ≅⟨ i ⟩≅ k' ∪ l'
≅ν (union-cong p q) rewrite ≅ν p | ≅ν q = refl
≅δ (union-cong p q) a = union-cong (≅δ p a) (≅δ q a)

-- Language union forms an idempotent commutative monoid.

union-icm : (i : Size) → IdempotentCommutativeMonoid _ _
union-icm i = record
  { Carrier = Lang ∞
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

union-swap23 : ∀{i} (k {l m} : Lang ∞) →
  (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ l
union-swap23 {i} k {l} {m} = prove 3 ((x ⊕ y) ⊕ z) ((x ⊕ z) ⊕ y) (k ∷ l ∷ m ∷ [])
  where
  open ICMSolver (union-icm i)
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))

union-swap24 : ∀{i} {k l m n : Lang ∞} →
  (k ∪ l) ∪ (m ∪ n) ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ n)
union-swap24 {i} {k} {l} {m} {n} = prove 4 ((x ⊕ y) ⊕ (z ⊕ u)) ((x ⊕ z) ⊕ (y ⊕ u)) (k ∷ l ∷ m ∷ n ∷ [])
  where
  open ICMSolver (union-icm i)
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))
  u = var (suc (suc (suc zero)))

union-union-distr : ∀{i} (k {l m} : Lang ∞) →
  (k ∪ l) ∪ m ≅⟨ i ⟩≅ (k ∪ m) ∪ (l ∪ m)
union-union-distr {i} k {l} {m} = prove 3 ((x ⊕ y) ⊕ z) ((x ⊕ z) ⊕ (y ⊕ z)) (k ∷ l ∷ m ∷ [])
  where
  open ICMSolver (union-icm i)
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))

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

concat-union-distribˡ : ∀{i} (k {l m} : Lang ∞) → (k ∪ l) · m ≅⟨ i ⟩≅ (k · m) ∪ (l · m)
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


concat-union-distribʳ : ∀{i} (k {l m} : Lang ∞) → k · (l ∪ m) ≅⟨ i ⟩≅ (k · l) ∪ (k · m)
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


-- Associativity of concatenation
--
-- uses concat-union-distribˡ

concat-assoc : ∀{i} (k {l m} : Lang ∞) → (k · l) · m ≅⟨ i ⟩≅ k · (l · m)
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

-- Laws of the Kleene star

-- Recursion equation for the Kleene star

star-rec : ∀{i} (l : Lang ∞) → l * ≅⟨ i ⟩≅ ε ∪ (l · l *)
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
