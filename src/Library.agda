module Library where

open import Level public renaming (zero to lzero; suc to lsuc)
open import Size  public

open import Data.Bool.Base public using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.List.Base public using (List; []; _∷_) -- hiding (module List)

open import Data.Maybe public using (Maybe; nothing; just)
open import Data.Nat.Base public using (ℕ; zero; suc)
open import Data.Product public using (_×_; _,_; proj₁; proj₂)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Unit public using (⊤)

open import Data.Fin public using (Fin; zero; suc)
open import Data.Vec public using (Vec; []; _∷_)

open import Relation.Nullary public using (Dec; yes; no)
open import Relation.Nullary.Decidable public using (⌊_⌋)
open import Relation.Binary public
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
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

  -- downFrom : ∀ n → Vec (Fin n) n
  -- downFrom 0 = []
  -- downFrom (suc n) = toFin n ∷ downFrom n

  -- -- alternative implementation of allFin which is
  -- upTo : ∀ n → Vec (Fin n) n
  -- upTo

  -- tr1 : ∀{n} → (Fin n → Bool) → Vec (Fin n × Bool) n
  -- tr1 f = tabulate λ i → f i , i

  -- tr2 : ∀{n} → Vec (Fin n × Bool) n → List (Fin n)
  -- tr2 v = List.gfilter (λ{ (i , b) → if b then just i else nothing}) (toList v)

  -- Get all indices which map to true.  l = [ i | v[i] = true ]
  trues : ∀{n} → Vec Bool n → List (Fin n)
  trues v = List.map proj₂ (List.filter proj₁ (toList (zip v (allFin _))))

  trues' : ∀{n} → Vec Bool n → List (Fin n)
  trues' [] = []
  trues' (b ∷ v) = let l = List.map suc (trues' v) in
    if b then zero ∷ l else l

  setTo : ∀ {A : Set} (a : A) {n} (v : Vec A n) (l : List (Fin n)) → Vec A n
  setTo a = List.foldl (λ w i → w [ i ]≔ a)

  -- Get all elements of the list (as set represented by a bit vector).
  -- v[i] = (i ∈ l)
  elemSet : ∀{n} → List (Fin n) → Vec Bool n
  elemSet = setTo true (replicate false)

  ∨-permute : ∀{n} → Vec Bool n → (Fin n → Fin n) → Vec Bool n
  ∨-permute v f = elemSet (List.map f (trues v))

  elemSet-trues : ∀ {n} (v : Vec Bool n) → elemSet (trues v) ≡ v
  elemSet-trues [] = refl
  elemSet-trues (true ∷ v) = {!elemSet-trues v!}
  elemSet-trues (false ∷ v) = {!!}

  tail[zero] : ∀{A : Set}{n} (v : Vec A (suc n)) {w : Vec A n} {a : A} →
    (p : tail v ≡ w) → tail (v [ zero ]≔ a) ≡ w
  tail[zero] (_ ∷ _) p = p

  [map] : ∀{A : Set} {n m} {a b : A} {w : Vec A n} (f : Fin m → Fin n) (l : List (Fin m)) →
      List.foldl (λ v i → v [ i ]≔ b) w (List.map f l)
    ≡ List.foldl (λ v i → v [ f i ]≔ b) w l
  [map] = {!!}

  [suc] : ∀{A : Set} {n} {a b : A} {w : Vec A n} (l : List (Fin n)) →
      List.foldl (λ v i → v [ suc i ]≔ b) (a ∷ w) l
    ≡ a ∷ List.foldl (λ v i → v [ i ]≔ b) w l
  [suc] [] = refl
  [suc] (x ∷ l) = [suc] l

  [suc'] : ∀{A : Set} {n} {a b : A} {w : Vec A n} (l : List (Fin n)) →
      tail (List.foldl (λ v i → v [ i ]≔ b) (a ∷ w) (List.map suc l))
    ≡ List.foldl (λ v i → v [ i ]≔ b) w l
  [suc'] [] = refl
  [suc'] (i ∷ is) = {!!}

  elemSet-trues' : ∀ {n} (v : Vec Bool n) → elemSet (trues' v) ≡ v
  elemSet-trues' [] = refl
  elemSet-trues' (false ∷ v)
    rewrite List.foldl-map {f = λ w i → w [ i ]≔ true} {g = suc} {a = replicate false} (trues' v)
         | [suc] {a = false} {b = true} {w = replicate false} (trues' v)
         | elemSet-trues' v = refl
  elemSet-trues' (true ∷ v)
    rewrite List.foldl-map {f = λ w i → w [ i ]≔ true} {g = suc} {a = true ∷ replicate false} (trues' v)
         | [suc] {a = true} {b = true} {w = replicate false} (trues' v)
         | elemSet-trues' v = refl
    -- vcong {!!}
    -- {! (tail[zero] (List.foldr _ _ (List.map suc (trues' v))) {!elemSet-trues' v!}) !}
