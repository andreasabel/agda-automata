{-# OPTIONS --sized-types --rewriting #-}

-- Boehm trees

open import Size
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

record BT (i : Size) (n : ℕ) : Set where
  coinductive; constructor bt
  field nabs : ℕ
        var  : Var (nabs + n)
        args : ∀ {j : SizeLt i} → List (BT (getSize j) (nabs + n))

var : ∀{i n} (x : Var n) → BT i n
var x = bt 0 x []

abs : ∀{i n} (t : BT i (1 + n)) → BT i n
BT.nabs (abs t)          = 1 + BT.nabs t
BT.var  (abs t)          = BT.var t
BT.args (abs t) {size _} = BT.args t {size _}

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

ren : ∀{i n m} (ρ : Ope n m) (t : BT i m) → BT i n
BT.nabs (ren ρ t) = BT.nabs t
BT.var  (ren ρ t) = renVar (lifts (BT.nabs t) ρ) (BT.var t)
BT.args (ren ρ t) {size _} = map (ren (lifts (BT.nabs t) ρ)) (BT.args t {size _})
