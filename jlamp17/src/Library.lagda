\AgdaHide{
\begin{code}
module Library where

open import Level public using (Level) renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Size  public

open import Data.Bool.Base public using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Empty public using (⊥; ⊥-elim)
-- open import Data.List.Base public using (List; []; _∷_; _++_) hiding (module List)

open import Data.Maybe.Base public using (Maybe; nothing; just; maybe′)
open import Data.Nat.Base public using (ℕ; zero; suc; _+_; pred)
open import Data.Product public using (_×_; _,_; proj₁; proj₂)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Unit public using (⊤)

open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; []; _∷_) hiding (module Vec)

open import Function public using (case_of_)

open import Relation.Nullary public using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable public using (⌊_⌋)
open import Relation.Binary public
open import Relation.Binary.PropositionalEquality public
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid
module EqR = Relation.Binary.Reasoning.Setoid

open import Function.Equality public using (module Π)
open import Function.Inverse public using (_↔_; module _InverseOf_; module Inverse)

open import Data.Bool.Properties public using (∨-∧-isBooleanAlgebra)
open import Algebra public using (IdempotentCommutativeMonoid)
open import Algebra.Structures public using (module IsBooleanAlgebra; module IsDistributiveLattice; module IsLattice)
open IsBooleanAlgebra ∨-∧-isBooleanAlgebra public using
  ( ∧-cong; ∧-comm; ∧-assoc
  ; ∨-cong; ∨-comm; ∨-assoc
  ; ∨-∧-distribʳ
  ; isDistributiveLattice
  )

open import Algebra.Properties.DistributiveLattice (record { isDistributiveLattice = isDistributiveLattice }) public
import Algebra.Solver.IdempotentCommutativeMonoid
module ICMSolver = Algebra.Solver.IdempotentCommutativeMonoid

postulate TODO : ∀{a}{A : Set a} → A

-- Goals
show_proof_ : ∀{a} (A : Set a) → A → A
show A proof x = x

-- Now exported:
-- -- These names are not exported from Algebra.Properties.DistributiveLattice
-- ∨-∧-distribˡ = proj₁ ∨-∧-distrib
-- ∧-∨-distribˡ = proj₁ ∧-∨-distrib
-- ∧-∨-distribʳ = proj₂ ∧-∨-distrib

∨-false : ∀ b → b ∨ false ≡ b
∨-false true  = refl
∨-false false = refl

∨-true : ∀ b → b ∨ true ≡ true
∨-true true  = refl
∨-true false = refl

∧-false : ∀ b → b ∧ false ≡ false
∧-false true  = refl
∧-false false = refl

∧-true : ∀ b → b ∧ true ≡ b
∧-true true  = refl
∧-true false = refl

∨-absorbs-∧ : ∀ b a → a ≡ (b ∧ a) ∨ a
∨-absorbs-∧ false a = refl
∨-absorbs-∧ true false = refl
∨-absorbs-∧ true true = refl

zero? : ℕ → Bool
zero? zero = true
zero? (suc _) = false

module List where

  data List (i : Size) (A : Set) : Set where
    []   :  List i A
    _∷_  :  ∀{j : Size< i} (x : A) (xs : List j A) → List i A

  map : ∀{i A B} → (A → B) → List i A → List i B
  map f []        =  []
  map f (x ∷ xs)  =  f x ∷ map f xs

  foldr : ∀ {i} {A B : Set} → (A → B → B) → B → List i A → B
  foldr c n []       = n
  foldr c n (x ∷ xs) = c x (foldr c n xs)

--   foldl : ∀{i A} (B : Size → Set) (f : ∀{i} → B i → A → B (↑ i)) (b : ∀{i} → B i)
  foldl : ∀{i}{A B : Set} (f : B → A → B) (b : B)
    → List i A → B
  foldl f b [] = b
  foldl f b (x ∷ xs) = foldl f (f b x) xs

  -- foldl-map : ∀{A B C : Set} {f : A → B → A} {g : C → B} {a : A} (cs : List ∞ C) →
  --   foldl f a (map g cs) ≡ foldl (λ a c → f a (g c)) a cs
  -- foldl-map [] = refl
  -- foldl-map (c ∷ cs) = foldl-map cs

  or : ∀{i} → List i Bool → Bool
  or = foldr _∨_ false

  any : ∀{i} {A : Set} → (A → Bool) → List i A → Bool
  any p xs = or (map p xs)

open List public using (List; []; _∷_) hiding (module List)

module Vec where

  open Data.Vec public hiding (map; zipWith; zip)

  -- Reimplementing some functions for nicer reduction behavior

  map : ∀ {a b n} {A : Set a} {B : Set b} →
          (A → B) → Vec A n → Vec B n
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
            (A → B → C) → Vec A n → Vec B n → Vec C n
  zipWith f [] [] = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

  zip : ∀ {a b n} {A : Set a} {B : Set b} →
        Vec A n → Vec B n → Vec (A × B) n
  zip = zipWith _,_

  -- New lemma about zipWith fusion

  vcong : ∀{a}{A : Set a}{n} {v v' : Vec A (suc n)} (p : head v ≡ head v') (q : tail v ≡ tail v') → v ≡ v'
  vcong {v = _ ∷ _} {v' = _ ∷ _} p q = cong₂ _ p q

  zipWith-map-map :  ∀ {a b c n} {A A' : Set a} {B B' : Set b} {C : Set c} →
    (f : A' → B' → C) (g : A → A') (h : B → B') (xs : Vec A n) (ys : Vec B n) →
    zipWith f (map g xs) (map h ys) ≡ zipWith (λ x y → f (g x) (h y)) xs ys
  zipWith-map-map f g h [] [] = refl
  zipWith-map-map f g h (x ∷ xs) (y ∷ ys) = vcong refl (zipWith-map-map f g h xs ys)

  -- New functionality

  tail' : ∀{a} {A : Set a} {n} (v : Vec A n) → Vec A (pred n)
  tail' [] = []
  tail' (x ∷ xs) = xs

  -- open import Data.List.All public using (module All) renaming (All to ListAll)
  data All {a p} {A : Set a} (P : A → Set p) : ∀{n} → Vec A n → Set (p l⊔ a) where
    []ᵃ  : All P []
    _∷ᵃ_ : ∀ {n x}{xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

  data All₂ {a b p} {A : Set a} {B : Set b} (R : A → B → Set p)
      : ∀{n} → Vec A n → Vec B n → Set (p l⊔ a l⊔ b) where
    []ᵃ  : All₂ R [] []
    _∷ᵃ_ : ∀ {n x}{xs : Vec A n}{y}{ys : Vec B n}
          (r : R x y) (rs : All₂ R xs ys) → All₂ R (x ∷ xs) (y ∷ ys)

  any : ∀{n} → Vec Bool n → Bool
  any = foldr (λ _ → Bool) _∨_ false

  -- Get all indices which map to true.  l = [ i | v[i] = true ]

  trues : ∀{n} → Vec Bool n → List ∞ (Fin n)
  trues [] = []
  trues (b ∷ v) = let l = List.map suc (trues v) in
    if b then zero ∷ l else l

  -- -- Original, Haskell-like implementation.

  -- trues-Haskellish : ∀{n} → Vec Bool n → List ∞ (Fin n)
  -- trues-Haskellish v = List.map proj₂ (List.filter proj₁ (toList (zip v (allFin _))))

  -- Set multiple elements of an array.

  setTo : ∀ {A : Set} (a : A) {n} (v : Vec A n) (l : List ∞ (Fin n)) → Vec A n
  setTo a = List.foldl (λ w i → w [ i ]≔ a)

  -- Get all elements of the list (as set represented by a bit vector).
  -- v[i] = (i ∈ l)
  elemSet : ∀{n} → List ∞ (Fin n) → Vec Bool n
  elemSet = setTo true (replicate false)

  -- Apply a state transition to a set of states.

  ∨-permute : ∀{n} → Vec Bool n → (Fin n → Fin n) → Vec Bool n
  ∨-permute v f = elemSet (List.map f (trues v))

  -- Properties

  -- -- Lemmata for: elemSet ∘ trues ≡ id

  -- [suc] : ∀{A : Set} {n} {a b : A} {w : Vec A n} (l : List ∞ (Fin n)) →

  --         List.foldl (λ v i → v [ suc i ]≔ b) (a ∷ w) l
  --   ≡ a ∷ List.foldl (λ v i → v [ i     ]≔ b) w       l

  -- [suc] [] = refl
  -- [suc] (x ∷ l) = [suc] l

  -- [suc]' : ∀{A : Set} {n} (a b : A) (w : Vec A n) (l : List ∞ (Fin n)) →

  --         List.foldl (λ v i → v [ i ]≔ b) (a ∷ w) (List.map suc l)
  --   ≡ a ∷ List.foldl (λ v i → v [ i ]≔ b) w       l

  -- [suc]' a b w l = trans (List.foldl-map l) ([suc] l)

  -- -- Theorem: elemSet ∘ trues ≡ id

  -- elemSet-trues : ∀ {n} (v : Vec Bool n) → elemSet (trues v) ≡ v
  -- elemSet-trues [] = refl
  -- elemSet-trues (false ∷ v)
  --   rewrite [suc]' false true (replicate false) (trues v)
  --         | elemSet-trues v
  --         = refl
  -- elemSet-trues (true ∷ v)
  --   rewrite [suc]' true true (replicate false) (trues v)
  --         | elemSet-trues v
  --         = refl

open Vec public using ([]ᵃ; _∷ᵃ_)


\end{code}
}
