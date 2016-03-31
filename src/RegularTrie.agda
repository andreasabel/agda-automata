open import Library

module RegularTrie (A : Set) where

-- We present regular grammars as regular tries where each inner node
-- is a binder and leafs are variables (de Bruijn indices) refering
-- back to nodes.

data Tree (n : ℕ) : Set where
  var  : (x : Fin n) → Tree n
  node : (ν : Bool) (δ : A → Tree (suc n)) → Tree n

-- We only substitute closed trees, and only for the last free variable.

substVar : ∀ (u : Tree 0) n (i : Fin (suc n)) → Tree n
substVar u zero zero = u
substVar u (suc n) zero = var zero
substVar u zero (suc ())
substVar u (suc n) (suc i) = {!substVar u n i!}

subst : ∀ (u : Tree 0) {n} (t : Tree (suc n)) → Tree n
subst u (var x) = substVar u _ x
subst u (node ν δ) = node ν (λ x → subst u (δ x))
