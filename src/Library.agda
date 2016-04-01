module Library where

open import Level public renaming (zero to lzero; suc to lsuc)
open import Size  public

open import Data.Bool.Base public using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.List.Base public using (List; []; _∷_)
module List = Data.List.Base
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
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; sym; trans)
import Relation.Binary.EqReasoning
module EqR = Relation.Binary.EqReasoning

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

module Vec where

  open Data.Vec public

  any : ∀{n} → Vec Bool n → Bool
  any = foldr (λ _ → Bool) _∨_ false

  -- Get all indices which map to true.  [ i | v[i] = true ]
  trues : ∀{n} → Vec Bool n → List (Fin n)
  trues v = List.map proj₂ (List.filter proj₁ (toList (zip v (allFin _))))

  ∨-permute : ∀{n} → Vec Bool n → (Fin n → Fin n) → Vec Bool n
  ∨-permute v f = List.foldl setTrue allFalse (List.map f (trues v))
    where
    allFalse = replicate false
    setTrue = λ v i → v [ i ]≔ true
