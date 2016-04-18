-- Regular expressions

open import Library

module RE
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Trie decA

data RE : Set where
  0ʳ   : RE
  1ʳ   : RE
  chʳ  : (a : A) → RE
  _+ʳ_ : (r s : RE) → RE
  _∙ʳ_  : (r s : RE) → RE
  _*ʳ  : (r : RE) → RE

-- semantics of regular expressions

⟦_⟧ : ∀{i} (r : RE) → Lang i
⟦ 0ʳ ⟧     = ∅
⟦ 1ʳ ⟧     = ε
⟦ chʳ a ⟧  = char a
⟦ r +ʳ s ⟧ = ⟦ r ⟧ ∪ ⟦ s ⟧
⟦ r ∙ʳ s ⟧ = ⟦ r ⟧ · ⟦ s ⟧
⟦ r *ʳ ⟧   = ⟦ r ⟧ *

-- simplifying smart constructors
-- (arguments are assumed to be simplified

-- monoid structure for _+ʳ_
_+ˢ_ : (r s : RE) → RE
0ʳ +ˢ         s = s
r +ˢ          0ʳ = r
(r +ʳ r₁) +ˢ  s = r +ʳ (r₁ +ʳ s)
r +ˢ          s = r +ʳ s

-- monoid with zero for _∙ʳ_

_∙ˢ_ : (r s : RE) → RE
0ʳ ∙ˢ s = 0ʳ
1ʳ ∙ˢ s = s
r ∙ˢ 0ʳ = 0ʳ
r ∙ˢ 1ʳ = r
(r ∙ʳ r₁) ∙ˢ s = r ∙ʳ (r₁ ∙ʳ s)
r ∙ˢ s = r ∙ʳ s

-- Star is idempotent

_*ˢ : (r : RE) → RE
0ʳ *ˢ = 1ʳ
1ʳ *ˢ = 1ʳ
(r *ʳ) *ˢ = r *ʳ
r *ˢ = r *ʳ

-- Correctness proofs.

plus-correct : ∀{i} r s → ⟦ r +ˢ s ⟧ ≅⟨ i ⟩≅ ⟦ r +ʳ s ⟧
plus-correct 0ʳ s                = ≅sym union-empty
plus-correct 1ʳ 0ʳ               = ≅trans (≅sym union-empty) (union-comm _ _)
plus-correct 1ʳ 1ʳ               = ≅refl
plus-correct 1ʳ (chʳ a)          = ≅refl
plus-correct 1ʳ (s +ʳ s₁)        = ≅refl
plus-correct 1ʳ (s ∙ʳ s₁)        = ≅refl
plus-correct 1ʳ (s *ʳ)           = ≅refl
plus-correct (chʳ a) 0ʳ          = ≅trans (≅sym union-empty) (union-comm _ _)
plus-correct (chʳ a) 1ʳ          = ≅refl
plus-correct (chʳ a) (chʳ a₁)    = ≅refl
plus-correct (chʳ a) (s +ʳ s₁)   = ≅refl
plus-correct (chʳ a) (s ∙ʳ s₁)   = ≅refl
plus-correct (chʳ a) (s *ʳ)      = ≅refl
plus-correct (r +ʳ r₁) 0ʳ        = ≅trans (≅sym union-empty) (union-comm _ _)
plus-correct (r +ʳ r₁) 1ʳ        = ≅sym (union-assoc _)
plus-correct (r +ʳ r₁) (chʳ a)   = ≅sym (union-assoc _)
plus-correct (r +ʳ r₁) (s +ʳ s₁) = ≅sym (union-assoc _)
plus-correct (r +ʳ r₁) (s ∙ʳ s₁) = ≅sym (union-assoc _)
plus-correct (r +ʳ r₁) (s *ʳ)    = ≅sym (union-assoc _)
plus-correct (r ∙ʳ r₁) 0ʳ        = ≅trans (≅sym union-empty) (union-comm _ _)
plus-correct (r ∙ʳ r₁) 1ʳ        = ≅refl
plus-correct (r ∙ʳ r₁) (chʳ a)   = ≅refl
plus-correct (r ∙ʳ r₁) (s +ʳ s₁) = ≅refl
plus-correct (r ∙ʳ r₁) (s ∙ʳ s₁) = ≅refl
plus-correct (r ∙ʳ r₁) (s *ʳ)    = ≅refl
plus-correct (r *ʳ) 0ʳ           = ≅trans (≅sym union-empty) (union-comm _ _)
plus-correct (r *ʳ) 1ʳ           = ≅refl
plus-correct (r *ʳ) (chʳ a)      = ≅refl
plus-correct (r *ʳ) (s +ʳ s₁)    = ≅refl
plus-correct (r *ʳ) (s ∙ʳ s₁)    = ≅refl
plus-correct (r *ʳ) (s *ʳ)       = ≅refl

star-correct : ∀{i} r → ⟦ r *ˢ ⟧ ≅⟨ i ⟩≅ ⟦ r *ʳ ⟧
star-correct 0ʳ        = ≅sym star-empty
star-correct 1ʳ        = ≅sym star-unit
star-correct (chʳ a)   = ≅refl
star-correct (r +ʳ r₁) = ≅refl
star-correct (r ∙ʳ r₁) = ≅refl
star-correct (r *ʳ)    = ≅sym (star-idem _)
