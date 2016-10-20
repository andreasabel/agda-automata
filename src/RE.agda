-- Regular expressions

open import Library

module RE
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA

data RE : Set where
  0ʳ   : RE
  chʳ  : (a : A) → RE
  _+ʳ_ : (r s : RE) → RE
  _∙ʳ_  : (r s : RE) → RE
  _*ʳ  : (r : RE) → RE

-- The unit is definable

pattern 1ʳ = 0ʳ *ʳ

-- semantics of regular expressions

⟦_⟧ : ∀{i} (r : RE) → Lang i
⟦ 0ʳ ⟧     = ∅
⟦ chʳ a ⟧  = char a
⟦ r +ʳ s ⟧ = ⟦ r ⟧ ∪ ⟦ s ⟧
⟦ r ∙ʳ s ⟧ = ⟦ r ⟧ · ⟦ s ⟧
⟦ r *ʳ ⟧   = ⟦ r ⟧ *

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

plus-empty : ∀ r → (r +ʳ 0ʳ) ≅ʳ r
plus-empty r = ≅trans (union-comm _ _) union-empty

plus-assoc : ∀ r s t → ((r +ʳ s) +ʳ t) ≅ʳ (r +ʳ (s +ʳ t))
plus-assoc r s t = union-assoc _

plus-cong : ∀{r r' s s'} (p : r ≅ʳ r') (q : s ≅ʳ s') → (r +ʳ s) ≅ʳ (r' +ʳ s')
plus-cong = union-cong

plus-congˡ : ∀{r r' s } (p : r ≅ʳ r') → (r +ʳ s) ≅ʳ (r' +ʳ s)
plus-congˡ = union-congˡ

plus-idem : ∀ r → ⟦ r +ʳ r ⟧ ≅⟨ ∞ ⟩≅ ⟦ r ⟧
plus-idem r = union-idem

plus-comm : ∀ r s → ⟦ r +ʳ s ⟧ ≅⟨ ∞ ⟩≅ ⟦ s +ʳ r ⟧
plus-comm r s = union-comm _ _

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
        ; assoc = plus-assoc
        ; ∙-cong = union-cong
        }
      ; identityˡ = λ r → union-empty
      ; comm = plus-comm
      }
    ; idem = plus-idem
    }
  }

comp-empty : ∀ r → (r ∙ʳ 0ʳ) ≅ʳ 0ʳ
comp-empty r = concat-emptyʳ _

comp-assoc : ∀ r s t → ((r ∙ʳ s) ∙ʳ t) ≅ʳ (r ∙ʳ (s ∙ʳ t))
comp-assoc r s t = concat-assoc _

plus-comp-distr : ∀ r r' s → ((r +ʳ r') ∙ʳ s) ≅ʳ ((r ∙ʳ s) +ʳ (r' ∙ʳ s))
plus-comp-distr r r' s = concat-union-distribˡ _

comp-plus-distr : ∀ r s s' → (r ∙ʳ (s +ʳ s')) ≅ʳ ((r ∙ʳ s) +ʳ (r ∙ʳ s'))
comp-plus-distr r s s' = concat-union-distribʳ _

den-unit : ⟦ 1ʳ ⟧ ≅ ε
den-unit = star-empty

den-plus : ∀ {i} r s → ⟦ r +ʳ s ⟧ ≅⟨ i ⟩≅ ⟦ r ⟧ ∪ ⟦ s ⟧
den-plus r s = ≅refl

den-comp : ∀ {i} r s → ⟦ r ∙ʳ s ⟧ ≅⟨ i ⟩≅ ⟦ r ⟧ · ⟦ s ⟧
den-comp r s = ≅refl

------------------------------------------------------------------------

-- Simplifying smart constructors
-- (arguments are assumed to be simplified

-- idempotent monoid structure for _+ʳ_

_+ˢ_ : (r s : RE) → RE
0ʳ +ˢ s = s
r +ˢ 0ʳ = r
1ʳ +ˢ (r *ʳ) = r *ʳ
(r *ʳ) +ˢ 1ʳ = r *ʳ
(r +ʳ r₁) +ˢ s = r +ʳ (r₁ +ʳ s)
r +ˢ s = r +ʳ s

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
(r *ʳ) *ˢ = r *ʳ
r *ˢ = r *ʳ

-- Correctness proofs of simplified regular expressions.

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
