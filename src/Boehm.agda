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

+assoc : ∀ n {m l} → ((n + m) + l) ≡ (n + (m + l))
+assoc zero = refl
+assoc (suc n) = cong suc (+assoc n)

{-# REWRITE n+0 #-}
{-# REWRITE n+suc #-}
{-# REWRITE +assoc #-}

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
  -- record BT (i : Size) (n : ℕ) : Set where
  --   inductive; constructor Λ
  --   field nabs : ℕ
  --         var  : Var (nabs + n)
  --         args : List (BT' i (nabs + n))

  data BT (i j : Size) (n : ℕ) : Set where
    Λ   : (k : ℕ) (x : Var (k + n)) {j' : Size< j} (args : List (BT i j' (k + n))) → BT i j n
    rep : (t : BT' i n) → BT i j n

  record BT' (i : Size) (n : ℕ) : Set where
    coinductive; constructor delay
    field force : ∀{j : SizeLt i} → BT (getSize j) ∞ n

open BT'

var : ∀{i j n} (x : Var n) → BT i (↑ j) n
var x = Λ 0 x []

-- abs : ∀{i j n} k (t : BT i j (k + n)) → BT i j n
abs : ∀{i n} k (t : BT i ∞ (k + n)) → BT i ∞ n
abs k (Λ n x ts) = Λ (n + k) x ts
abs k (rep t)    = rep (delay \{ {size _} → abs k $ force t {size _} })

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
  ren  : ∀{i j n m} (ρ : Ope n m) (t : BT i j m) → BT i j n
  ren {i} ρ₀ (Λ n x ts) = Λ n (renVar ρ x) (map (ren {i} ρ) ts)
    where ρ = lifts n ρ₀
  ren ρ (rep t) = rep (ren' ρ t)

  ren' : ∀{i n m} (ρ : Ope n m) (t : BT' i m) → BT' i n
  force (ren' ρ t) {size j}  = ren {j} ρ (force t {size j})

-- -- Agda reports (unjustifiedly) unsolvable constraints:
-- -- It does not like the $ !
-- ren  : ∀{i n m} (ρ : Ope n m) (t : BT i m) → BT i n
-- ren {i} ρ₀ (Λ n x ts) = Λ n (renVar ρ x) $ for ts \ t → delay
--    \{ {size j} → ren {j} ρ $ force t {size j} }
--   where ρ = lifts n ρ₀

weakT : ∀{i j n} (t : BT i j n) → BT i j (1 + n)
weakT = ren (weak id)

data Sub (i : Size) : (n m : ℕ) → Set where
  rn   : ∀{n m} (ρ : Ope n m) → Sub i n m
  _,_  : ∀{n m} (σ : Sub i n m) (t : BT i ∞ n) → Sub i n (1 + m)
  -- lift : ∀{n m} (σ : Sub n m) → Sub (1 + n) (1 + m)
  -- weak : ∀{n m} (σ : Sub n m) → Sub (1 + n) m

weakS : ∀{i n m} (σ : Sub i n m) → Sub i (1 + n) m
weakS (rn ρ) = rn (weak ρ)
weakS (s , t) = weakS s , weakT t

liftS : ∀{i n m} (σ : Sub i n m) → Sub i (1 + n) (1 + m)
liftS σ = weakS σ , var vz

liftsS : ∀{i n m} k (σ : Sub i n m) → Sub i (k + n) (k + m)
liftsS zero σ = σ
liftsS (suc k) σ = liftS (liftsS k σ)

sgS : ∀{i n} (t : BT i ∞ n) → Sub i n (1 + n)
sgS t = rn id , t

subVar : ∀{i n m} (σ : Sub i n m) (x : Var m) → BT i ∞ n
subVar (rn ρ)  x      = var (renVar ρ x)
subVar (σ , t) vz     = t
subVar (σ , t) (vs x) = subVar σ x

mutual
  -- sub'  : ∀{i n m} (σ : Sub i n m) (t : BT' i m) → BT' i n
  -- force (sub' σ t) {size _} = sub σ (force t {size _})

  sub  : ∀{i n m} (σ : Sub i n m) (t : BT i ∞ m) → BT i ∞ n
  sub σ t = apps t σ []

  apply : ∀{i n} (t : BT i ∞ n) (us : List (BT i ∞ n)) → BT i ∞ n
  apply t us = apps t (rn id) us

  apps : ∀{i n m} (t : BT i ∞ m) (σ : Sub i n m) (us : List (BT i ∞ n)) → BT i ∞ n
  apps (Λ (suc k) x ts) σ (u ∷ us) = apps (Λ k x ts) (σ , u) us
  apps (Λ zero    x ts) σ us = rep (delay \{ {size _} →
                               apply (subVar σ x) (map (sub σ) ts ++ us) })
  -- Should work, but insufficiency in constraint solver
  -- apps (Λ (suc k) x ts) σ [] = abs (suc k) $ (rep (delay \{ {size _} →
  --                              apply (subVar σ' x) (map (sub σ') ts)}))
  apps (Λ (suc k) x ts) σ [] = (rep (delay \{ {size _} →
                               abs (suc k) $ apply (subVar σ' x) (map (sub σ') ts)}))
    where σ' = liftsS (suc k) σ
  apps (rep t) σ us = rep (delay \{ {size _} → apps (force t {size _}) σ us})

app : ∀{i n} (t u : BT i ∞ n) → BT i ∞ n
app t u = apply t (u ∷ [])
