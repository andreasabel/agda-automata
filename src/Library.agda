module Library where

open import Level public renaming (zero to lzero; suc to lsuc)
open import Size  public

open import Data.Bool.Base public using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.List.Base public using (List; []; _∷_) -- hiding (module List)

open import Data.Maybe public using (Maybe; nothing; just)
open import Data.Nat.Base public using (ℕ; zero; suc; _+_)
open import Data.Product public using (_×_; _,_; proj₁; proj₂)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Unit public using (⊤)

open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; []; _∷_)

open import Function public using (case_of_)

open import Relation.Nullary public using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable public using (⌊_⌋)
open import Relation.Binary public
open import Relation.Binary.PropositionalEquality public
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
import Relation.Binary.EqReasoning
module EqR = Relation.Binary.EqReasoning

open import Function.Equality public using (module Π)
open import Function.Inverse public using (_↔_; module _InverseOf_; module Inverse)

open import Data.Bool.Properties public using (isBooleanAlgebra)
open import Algebra public using (IdempotentCommutativeMonoid)
open import Algebra.Structures public using (module IsBooleanAlgebra; module IsDistributiveLattice; module IsLattice)
open IsBooleanAlgebra isBooleanAlgebra public using (∧-cong; ∧-comm; ∧-assoc; ∨-cong; ∨-comm; ∨-assoc; ∨-∧-distribʳ; isDistributiveLattice; isLattice) -- renaming (∨-idempotent to ∨-idem)

open import Algebra.Properties.Lattice (record { isLattice = isLattice }) public using () renaming (∨-idempotent to ∨-idem)

open import Algebra.Properties.DistributiveLattice (record { isDistributiveLattice = isDistributiveLattice }) public
import Algebra.IdempotentCommutativeMonoidSolver
module ICMSolver = Algebra.IdempotentCommutativeMonoidSolver

-- These names are not exported from Algebra.Properties.DistributiveLattice
∨-∧-distribˡ = proj₁ ∨-∧-distrib
∧-∨-distribˡ = proj₁ ∧-∨-distrib
∧-∨-distribʳ = proj₂ ∧-∨-distrib

zero? : ℕ → Bool
zero? zero = true
zero? (suc _) = false

module List where

  open Data.List.Base public

  foldl-map : ∀{A B C : Set} {f : A → B → A} {g : C → B} {a : A} (cs : List C) →
    foldl f a (map g cs) ≡ foldl (λ a c → f a (g c)) a cs
  foldl-map [] = refl
  foldl-map (c ∷ cs) = foldl-map cs

module Vec where

  open Data.Vec public

  vcong : ∀{A : Set}{n} {v v' : Vec A (suc n)} (p : head v ≡ head v') (q : tail v ≡ tail v') → v ≡ v'
  vcong {v = _ ∷ _} {v' = _ ∷ _} p q = cong₂ _ p q

  any : ∀{n} → Vec Bool n → Bool
  any = foldr (λ _ → Bool) _∨_ false

  -- Get all indices which map to true.  l = [ i | v[i] = true ]

  trues : ∀{n} → Vec Bool n → List (Fin n)
  trues [] = []
  trues (b ∷ v) = let l = List.map suc (trues v) in
    if b then zero ∷ l else l

  -- Original, Haskell-like implementation.

  trues-Haskellish : ∀{n} → Vec Bool n → List (Fin n)
  trues-Haskellish v = List.map proj₂ (List.filter proj₁ (toList (zip v (allFin _))))

  -- Set multiple elements of an array.

  setTo : ∀ {A : Set} (a : A) {n} (v : Vec A n) (l : List (Fin n)) → Vec A n
  setTo a = List.foldl (λ w i → w [ i ]≔ a)

  -- Get all elements of the list (as set represented by a bit vector).
  -- v[i] = (i ∈ l)
  elemSet : ∀{n} → List (Fin n) → Vec Bool n
  elemSet = setTo true (replicate false)

  -- Apply a state transition to a set of states.

  ∨-permute : ∀{n} → Vec Bool n → (Fin n → Fin n) → Vec Bool n
  ∨-permute v f = elemSet (List.map f (trues v))

  -- Properties

  -- Lemmata for: elemSet ∘ trues ≡ id

  [suc] : ∀{A : Set} {n} {a b : A} {w : Vec A n} (l : List (Fin n)) →

          List.foldl (λ v i → v [ suc i ]≔ b) (a ∷ w) l
    ≡ a ∷ List.foldl (λ v i → v [ i     ]≔ b) w       l

  [suc] [] = refl
  [suc] (x ∷ l) = [suc] l

  [suc]' : ∀{A : Set} {n} (a b : A) (w : Vec A n) (l : List (Fin n)) →

          List.foldl (λ v i → v [ i ]≔ b) (a ∷ w) (List.map suc l)
    ≡ a ∷ List.foldl (λ v i → v [ i ]≔ b) w       l

  [suc]' a b w l = trans (List.foldl-map l) ([suc] l)

  -- Theorem: elemSet ∘ trues ≡ id

  elemSet-trues : ∀ {n} (v : Vec Bool n) → elemSet (trues v) ≡ v
  elemSet-trues [] = refl
  elemSet-trues (false ∷ v)
    rewrite [suc]' false true (replicate false) (trues v)
          | elemSet-trues v
          = refl
  elemSet-trues (true ∷ v)
    rewrite [suc]' true true (replicate false) (trues v)
          | elemSet-trues v
          = refl
