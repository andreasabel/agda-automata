-- Regular expressions

open import Library

module RegularExpressions
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA

-- Non-zero regular expression

data RENZ : Set where
  1ʳ   : RENZ
  chʳ  : (a : A) → RENZ
  _+ʳ_ : (r s : RENZ) → RENZ
  _∙ʳ_  : (r s : RENZ) → RENZ
  _*ʳ  : (r : RENZ) → RENZ

-- Possibly zero regular expressions

data RE : Set where
  0ˢ   : RE
  ⌜_⌝  :  RENZ → RE

-- semantics of regular expressions

⟦_⟧ʳ : ∀{i} (r : RENZ) → Lang i
⟦ 1ʳ ⟧ʳ     = ε
⟦ chʳ a ⟧ʳ  = char a
⟦ r +ʳ s ⟧ʳ = ⟦ r ⟧ʳ ∪ ⟦ s ⟧ʳ
⟦ r ∙ʳ s ⟧ʳ = ⟦ r ⟧ʳ · ⟦ s ⟧ʳ
⟦ r *ʳ ⟧ʳ   = ⟦ r ⟧ʳ *

⟦_⟧ : ∀{i} (r : RE) → Lang i
⟦ 0ˢ ⟧     = ∅
⟦ ⌜ r ⌝ ⟧  = ⟦ r ⟧ʳ

-- Constructors of RE

1ˢ : RE
1ˢ = ⌜ 1ʳ ⌝

chˢ : (a : A) → RE
chˢ a = ⌜ chʳ a ⌝

_+ˢ_ : (r s : RE) → RE
0ˢ +ˢ s = s
r +ˢ 0ˢ = r
⌜ r ⌝ +ˢ ⌜ s  ⌝ = ⌜ r +ʳ s ⌝

_∙ˢ_ : (r s : RE) → RE
0ˢ ∙ˢ s = 0ˢ
r ∙ˢ 0ˢ = 0ˢ
⌜ r ⌝ ∙ˢ ⌜ s  ⌝ = ⌜ r ∙ʳ s ⌝

_*ˢ : (r : RE) → RE
0ˢ *ˢ = 1ˢ
⌜ r ⌝ *ˢ = ⌜ r *ʳ ⌝

-- Equality of REs

_≅ʳ_ : (r s : RE) → Set
r ≅ʳ s = ⟦ r ⟧ ≅ ⟦ s ⟧

≅ʳisEquivalence : IsEquivalence _≅ʳ_
IsEquivalence.refl  ≅ʳisEquivalence = ≅refl
IsEquivalence.sym   ≅ʳisEquivalence = ≅sym
IsEquivalence.trans ≅ʳisEquivalence = ≅trans

REq : Setoid lzero lzero
Setoid.Carrier       REq = RE
Setoid._≈_           REq = _≅ʳ_
Setoid.isEquivalence REq = ≅ʳisEquivalence

plus-icm : IdempotentCommutativeMonoid _ _
plus-icm =  record
  { Carrier = RE
  ; _≈_ = _≅ʳ_
  ; _∙_ = _+ʳ_
  ; ε = 0ʳ
  ; isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = ≅ʳisEquivalence
        ; assoc = λ r s t → union-assoc _
        ; ∙-cong = union-cong
        }
      ; identityˡ = λ r → union-empty
      ; comm = λ r s → union-comm _ _
      }
    ; idem = λ r → union-idem
    }
  }

plus-cong : ∀{r r' s s'} (p : r ≅ʳ r') (q : s ≅ʳ s') → (r +ʳ s) ≅ʳ (r' +ʳ s')
plus-cong = union-cong

-- plus-congˡ :

unit-correct : ⟦ 1ʳ ⟧ ≅ ε
unit-correct = star-empty

-- Correctness proofs.

plus-correct : ∀{i} r s → ⟦ r +ˢ s ⟧ ≅⟨ i ⟩≅ ⟦ r +ʳ s ⟧
plus-correct 0ʳ s                = ≅sym union-empty
plus-correct 1ʳ 0ʳ               = ≅trans (≅sym union-empty) (union-comm _ _)
plus-correct 1ʳ (chʳ a)          = ≅refl
plus-correct 1ʳ (s +ʳ s₁)        = ≅refl
plus-correct 1ʳ (s ∙ʳ s₁)        = ≅refl
plus-correct 1ʳ 1ʳ               = ≅sym union-idem
plus-correct 1ʳ (chʳ a *ʳ) = ≅sym (empty-star-union-star _)
plus-correct 1ʳ ((s +ʳ s₁) *ʳ) = ≅sym (empty-star-union-star _)
plus-correct 1ʳ ((s ∙ʳ s₁) *ʳ) = ≅sym (empty-star-union-star _)
plus-correct 1ʳ ((s *ʳ) *ʳ) = ≅sym (empty-star-union-star _)
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
plus-correct (r *ʳ) (chʳ a)      = ≅refl
plus-correct (r *ʳ) (s +ʳ s₁)    = ≅refl
plus-correct (r *ʳ) (s ∙ʳ s₁)    = ≅refl
plus-correct (chʳ a *ʳ) (0ʳ *ʳ) = ≅sym (star-union-empty-star _)
plus-correct (chʳ a *ʳ) (chʳ a₁ *ʳ) = ≅refl
plus-correct (chʳ a *ʳ) ((s +ʳ s₁) *ʳ) = ≅refl
plus-correct (chʳ a *ʳ) ((s ∙ʳ s₁) *ʳ) = ≅refl
plus-correct (chʳ a *ʳ) ((s *ʳ) *ʳ) = ≅refl
plus-correct ((r +ʳ r₁) *ʳ) (0ʳ *ʳ) = ≅sym (star-union-empty-star _)
plus-correct ((r +ʳ r₁) *ʳ) (chʳ a *ʳ) = ≅refl
plus-correct ((r +ʳ r₁) *ʳ) ((s +ʳ s₁) *ʳ) = ≅refl
plus-correct ((r +ʳ r₁) *ʳ) ((s ∙ʳ s₁) *ʳ) = ≅refl
plus-correct ((r +ʳ r₁) *ʳ) ((s *ʳ) *ʳ) = ≅refl
plus-correct ((r ∙ʳ r₁) *ʳ) (0ʳ *ʳ) = ≅sym (star-union-empty-star _)
plus-correct ((r ∙ʳ r₁) *ʳ) (chʳ a *ʳ) = ≅refl
plus-correct ((r ∙ʳ r₁) *ʳ) ((s +ʳ s₁) *ʳ) = ≅refl
plus-correct ((r ∙ʳ r₁) *ʳ) ((s ∙ʳ s₁) *ʳ) = ≅refl
plus-correct ((r ∙ʳ r₁) *ʳ) ((s *ʳ) *ʳ) = ≅refl
plus-correct ((r *ʳ) *ʳ) (0ʳ *ʳ) = ≅sym (star-union-empty-star _)
plus-correct ((r *ʳ) *ʳ) (chʳ a *ʳ) = ≅refl
plus-correct ((r *ʳ) *ʳ) ((s +ʳ s₁) *ʳ) = ≅refl
plus-correct ((r *ʳ) *ʳ) ((s ∙ʳ s₁) *ʳ) = ≅refl
plus-correct ((r *ʳ) *ʳ) ((s *ʳ) *ʳ) = ≅refl

postulate times-correct : ∀{i} r s → ⟦ r ∙ˢ s ⟧ ≅⟨ i ⟩≅ ⟦ r ∙ʳ s ⟧
-- times-correct =

star-correct : ∀{i} r → ⟦ r *ˢ ⟧ ≅⟨ i ⟩≅ ⟦ r *ʳ ⟧
star-correct 0ʳ        = ≅refl
star-correct (chʳ a)   = ≅refl
star-correct (r +ʳ r₁) = ≅refl
star-correct (r ∙ʳ r₁) = ≅refl
star-correct (r *ʳ)    = ≅sym (star-idem _)
