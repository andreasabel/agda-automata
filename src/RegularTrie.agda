open import Library

module RegularTrie
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Trie decA

-- We present regular grammars as regular tries where each inner node
-- is a binder and leafs are variables (de Bruijn indices) refering
-- back to nodes.

data Tree : (n : ℕ) → Set where
  leaf : ∀{n} → Tree (suc n)
  weak : ∀{n} (t : Tree n) → Tree (suc n)
  node : ∀{n} (ν : Bool) (δ : A → Tree (suc n)) → Tree n
--  state : ∀{n}(s : List A) → Tree n

-- We only substitute closed trees, and only for the last free variable.

-- substVar : ∀ (u : Tree 0) n (i : Fin (suc n)) → Tree n
-- substVar u zero zero = u
-- substVar u (suc n) zero = var zero
-- substVar u zero (suc ())
-- substVar u (suc n) (suc i) = {!substVar u n i!} -- needs weakening

subst : ∀ (u : Tree 0) {n} (t : Tree (suc n)) → Tree n
-- subst u (var x) = substVar u _ x
subst u {zero}  leaf     = u
subst u {suc n} leaf     = leaf
subst u {zero}  (weak t) = t
subst u {suc n} (weak t) = weak (subst u t)
subst u       (node ν δ) = node ν (λ x → subst u (δ x))

Λ : ∀{i} (t : Tree 0) → Lang i
-- Λ (state _) = ∅
Lang.ν (Λ (node ν δ))   = ν
Lang.δ (Λ (node ν δ)) x = Λ (subst (node ν δ) (δ x))

∅T : Tree 0
∅T = node false (λ x → leaf)

εT : Tree 0
εT = node true λ x → weak ∅T

charT : (a : A) → Tree 0
charT a = node false λ x → weak (if ⌊ x ≟ a ⌋ then εT else ∅T)

{-
auto : Tree n → List A → Vec (List A) n →

name : List A → Tree 0 → Tree 0
name as (node ν δ) = node ν (λ a → {!name (a ∷ as) (subst (state as) (δ a))!})
name as (state s) = state s
-}
