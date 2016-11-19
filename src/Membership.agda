open import Library

module Membership (A : Set) where

L = List A → Bool

ν : L → Bool
ν f = f []

δ : L → A → L
δ f x xs = f (x ∷ xs)

_⊻_ : L → L → L
(f ⊻ g) x = f x ∨ g x

_∘_ : L → L → L
(f ∘ g) []       = ν f ∧ ν g
(f ∘ g) (x ∷ xs) = (δ f x ∘ g) xs ∨ (ν f ∧ g xs)

{-# TERMINATING #-}
_* : L → L
(f *) []       = true
(f *) (x ∷ xs) = (δ f x ∘ (f *)) xs
