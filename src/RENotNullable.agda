-- Regular expressions which denote languages that are not nullable
-- i.e. do not contain the empty word.

open import Library

module RENotNullable
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA
open import RE decA public

data Renn : Set where
  0ⁿ : Renn
  chⁿ  : (a : A) → Renn
  _+ⁿ_ : (s s' : Renn) → Renn
  _∙ⁿ_  : (r : RE) (s : Renn) → Renn
  _ⁿ∙_  : (s : Renn) (r : RE) → Renn

re : (r : Renn) → RE
re 0ⁿ = 0ʳ
re (chⁿ a) = chʳ a
re (s +ⁿ s') = re s +ʳ re s'
re (r ∙ⁿ s) = r ∙ʳ re s
re (s ⁿ∙ r) = re s ∙ʳ r

⟦_⟧ⁿ : ∀{i} (s : Renn) → Lang i
⟦ s ⟧ⁿ = ⟦ re s ⟧

-- Soundness: these REs are actually not nullable

not-nullable : ∀ s → ν ⟦ s ⟧ⁿ ≡ false
not-nullable 0ⁿ = refl
not-nullable (chⁿ a) = refl
not-nullable (s +ⁿ s′) rewrite not-nullable s | not-nullable s′ = refl
not-nullable (r ∙ⁿ s) rewrite not-nullable s = ∧-false (ν ⟦ r ⟧)
not-nullable (s ⁿ∙ r) rewrite not-nullable s = refl

_*ⁿ : Renn → RE
s *ⁿ = (re s) *ʳ
