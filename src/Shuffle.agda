{-# OPTIONS --sized-types --allow-unsolved-metas #-}

open import Library

module Shuffle
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA

-- The shuffle product

infixl  5 _∥_

_∥_ : ∀{i} (k l : Lang i) → Lang i
ν (k ∥ l)   = ν k ∧ ν l
δ (k ∥ l) x = (δ k x ∥ l) ∪ (k ∥ δ l x)

-- The shuffle product is commutative.

shuffle-comm : ∀{i} (k l : Lang ∞) → k ∥ l ≅⟨ i ⟩≅ l ∥ k
≅ν (shuffle-comm k l)   = ∧-comm (ν k) _
≅δ (shuffle-comm k l) x = begin
  δ k x ∥ l ∪ k ∥ δ l x ≈⟨ union-cong (shuffle-comm _ _) (shuffle-comm _ _) ⟩
  l ∥ δ k x ∪ δ l x ∥ k ≈⟨ union-comm (l ∥ δ k x) (δ l x ∥ k) ⟩
  δ l x ∥ k ∪ l ∥ δ k x
  ∎ where open EqR (Bis _)

-- Interleaving of lists.

data Interleave : (xs ys zs : List A) → Set where
  nil   : Interleave [] [] []
  left  : ∀{x xs ys zs} → Interleave xs ys zs → Interleave (x ∷ xs) ys (x ∷ zs)
  right : ∀{y xs ys zs} → Interleave xs ys zs → Interleave xs (y ∷ ys) (y ∷ zs)

-- Language membership, propositionally.

data In (l : Lang ∞) : (xs : List A) → Set where
  nil  : ν l ≡ true → In l []
  cons : ∀{x xs} → In (δ l x) xs → In l (x ∷ xs)

-- Membership in a union.

union-inˡ : ∀{k l xs} →  In k xs → In (k ∪ l) xs
union-inˡ {k} {l} (nil _) with ν k | In.nil {k ∪ l}
union-inˡ (nil ()) | false | _
union-inˡ (nil _ ) | true  | h = h refl
union-inˡ (cons p) = cons (union-inˡ p)

union-inʳ : ∀{k l xs} →  In l xs → In (k ∪ l) xs
union-inʳ {k} {l} (nil _) with ν k | ν l | In.nil {k ∪ l}
union-inʳ (nil ())   | _     | false | _
union-inʳ (nil refl) | false | true  | h = h refl
union-inʳ (nil refl) | true  | true  | h = h refl
union-inʳ (cons p) = cons (union-inʳ p)

-- Deciding union membership

split-in :  ∀{k l xs} → In (k ∪ l) xs → In k xs ⊎ In l xs
split-in {k} {l} (nil x) with ν k | In.nil {k}
split-in {k} {l} (nil _)  | true  | h = inj₁ (h refl)
split-in {k} {l} (nil _)  | false | h with ν l | In.nil {l}
split-in {k} {l} (nil ()) | false | _ | false | j
split-in {k} {l} (nil _)  | false | _ | true  | j = inj₂ (j refl)
split-in (cons p) with split-in p
split-in (cons p) | inj₁ q = inj₁ (cons q)
split-in (cons p) | inj₂ q = inj₂ (cons q)

-- Completeness of shuffle-stroke:
-- The interleaving of xs ∈ k and ys ∈ l is in k ∥ l.

shuffle-complete : ∀{xs ys zs} → Interleave xs ys zs → ∀{k l} → In k xs → In l ys → In (k ∥ l) zs
shuffle-complete nil {k} {l} (nil q) (nil r) with ν k | ν l | In.nil {l = k ∥ l}
shuffle-complete _ (nil ())  _ | false | _     | _
shuffle-complete _ _ (nil ())  | _     | false | _
shuffle-complete _ _ _         | true  | true  | h = h refl

shuffle-complete (left  p) (cons q) r = cons (union-inˡ (shuffle-complete p q r))
shuffle-complete (right p) q (cons r) = cons (union-inʳ (shuffle-complete p q r))

-- Soundness of shuffle-stroke.

record SortOut (k l : Lang ∞) (zs : List A) : Set where
  constructor sortOut
  field xs ys : List A
        p : In k xs
        q : In l ys
        r : Interleave xs ys zs

-- Any zs ∈ k ∥ l is an interleaving of an xs ∈ k and a ys ∈ l.

shuffle-sound : ∀{k l zs} → In (k ∥ l) zs → SortOut k l zs
shuffle-sound {k} {l} (nil x) with ν k | ν l | In.nil {k} | In.nil {l}
shuffle-sound (nil ()) | false | _     | _ | _
shuffle-sound (nil ()) | true  | false | _ | _
shuffle-sound (nil _ ) | true  | true  | f | g = sortOut [] [] (f refl) (g refl) nil
shuffle-sound (cons p) with split-in p
shuffle-sound (cons _) | inj₁ q with shuffle-sound q
shuffle-sound (cons _) | inj₁ _ | (sortOut xs ys p q r) = sortOut (_ ∷ xs) ys (cons p) q (left r)
shuffle-sound (cons _) | inj₂ q with shuffle-sound q
shuffle-sound (cons _) | inj₂ _ | (sortOut xs ys p q r) = sortOut xs (_ ∷ ys) p (cons q) (right r)
