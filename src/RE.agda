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
(r +ʳ r₁) +ˢ  s = r +ʳ (r₁ +ʳ s)
r +ˢ          0ʳ = r
r +ˢ          s = r +ʳ s

-- monoid with zero for _∙ʳ_

_∙ˢ_ : (r s : RE) → RE
0ʳ ∙ˢ s = 0ʳ
1ʳ ∙ˢ s = s
(r ∙ʳ r₁) ∙ˢ s = r ∙ʳ (r₁ ∙ʳ s)
r ∙ˢ 0ʳ = 0ʳ
r ∙ˢ 1ʳ = r
r ∙ˢ s = r ∙ʳ s

-- Star is idempotent

_*ˢ : (r : RE) → RE
0ʳ *ˢ = 1ʳ
1ʳ *ˢ = 1ʳ
(r *ʳ) *ˢ = r *ʳ
r *ˢ = r *ʳ
