{-# OPTIONS --rewriting #-}

-- Boehm trees

open import Size
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

data SizeLt (i : Size) : Set where
  size : (j : Size< i) → SizeLt i

-- Agda-2.4.2.5 needs a patch to allow functions into size:
getSize : ∀{i} → SizeLt i → Size
getSize (size j) = j

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : (m n : ℕ) → ℕ
zero  + n = n
suc m + n = suc (m + n)

n+0 : ∀(n : ℕ) → (n + 0) ≡ n
n+0 zero = refl
n+0 (suc n) = cong suc (n+0 n)

n+suc : ∀ n {m} → (n + suc m) ≡ suc (n + m)
n+suc zero    = refl
n+suc (suc n) = cong suc (n+suc n)

{-# REWRITE n+0 #-}
{-# REWRITE n+suc #-}

data Var : (n : ℕ) → Set where
  vz : ∀{n} → Var (suc n)
  vs : ∀{n} → (x : Var n) → Var (suc n)

data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A

_++_ : ∀{A} (xs ys : List A) → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀{A B} (f : A → B) (xs : List A) → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

for : ∀{A B} (xs : List A) (f : A → B) → List B
for [] f = []
for (x ∷ xs) f = f x ∷ for xs f

mutual
  record BT (i : Size) (n : ℕ) : Set where
    inductive; constructor Λ
    field nabs : ℕ
          var  : Var (nabs + n)
          args : List (BT' i (nabs + n))

  -- data BT (i : Size) (n : ℕ) : Set where
  --   Λ : (k : ℕ) (x : Var (k + n)) (args : List (BT' i (k + n))) → BT i n

  record BT' (i : Size) (n : ℕ) : Set where
    coinductive; constructor delay
    field force : ∀{j : SizeLt i} → BT (getSize j) n

open BT'

var : ∀{i n} (x : Var n) → BT i n
var x = Λ 0 x []

abs : ∀{i n} (t : BT i (1 + n)) → BT i n
abs (Λ n x ts) = Λ (1 + n) x ts

-- data Ren : (n m : ℕ) → Set where
--   weak : ∀{n} k → Ren (k + n) n
--   _,_  : Ren n m → Var n → Ren n (1 + m)
--   lift : ∀{n m} k (ρ : Ren n m) → Ren (k + n) (k + m)

-- order-preserving embeddings (thinnings)
-- (subsequence)

data Ope : (n m : ℕ) → Set where
  id   : ∀{n} → Ope n n
  weak : ∀{n m} (ρ : Ope n m) → Ope (1 + n) m
  lift : ∀{n m} (ρ : Ope n m) → Ope (1 + n) (1 + m)

lifts : ∀ k {n m} (ρ : Ope n m) → Ope (k + n) (k + m)
lifts 0       ρ = ρ
lifts (suc k) ρ = lift (lifts k ρ)

renVar : ∀{n m} (ρ : Ope n m) (x : Var m) → Var n
renVar id       x      = x
renVar (weak ρ) x      = vs (renVar ρ x)
renVar (lift ρ) vz     = vz
renVar (lift ρ) (vs x) = vs (renVar ρ x)

mutual
  ren  : ∀{i n m} (ρ : Ope n m) (t : BT i m) → BT i n
  ren {i} ρ₀ (Λ n x ts) = Λ n (renVar ρ x) (map (ren' {i} ρ) ts)
    where ρ = lifts n ρ₀

  ren' : ∀{i n m} (ρ : Ope n m) (t : BT' i m) → BT' i n
  force (ren' ρ t) {size j}  = ren {j} ρ (force t {size j})

-- -- Agda reports (unjustifiedly) unsolvable constraints:
-- ren  : ∀{i n m} (ρ : Ope n m) (t : BT i m) → BT i n
-- ren {i} ρ₀ (Λ n x ts) = Λ n (renVar ρ x) $ for ts \ t → delay
--    \{ {size j} → ren {j} ρ $ force t {size j} }
--   where ρ = lifts n ρ₀
