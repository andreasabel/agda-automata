{-# OPTIONS --sized-types --allow-unsolved-metas #-}

-- Regular expressions

open import Library

module RegularExpressions
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA

-- Non-zero regular expression

data RENZ : Set where
  1ⁿ   : RENZ
  chⁿ  : (a : A) → RENZ
  _+ⁿ_ : (r s : RENZ) → RENZ
  _∙ⁿ_  : (r s : RENZ) → RENZ
  _*ⁿ  : (r : RENZ) → RENZ

-- Possibly zero regular expressions

data RE : Set where
  0ʳ   : RE
  ⌜_⌝  :  RENZ → RE

-- semantics of regular expressions

⟦_⟧ⁿ : ∀{i} (r : RENZ) → Lang i
⟦ 1ⁿ ⟧ⁿ     = ε
⟦ chⁿ a ⟧ⁿ  = char a
⟦ r +ⁿ s ⟧ⁿ = ⟦ r ⟧ⁿ ∪ ⟦ s ⟧ⁿ
⟦ r ∙ⁿ s ⟧ⁿ = ⟦ r ⟧ⁿ · ⟦ s ⟧ⁿ
⟦ r *ⁿ ⟧ⁿ   = ⟦ r ⟧ⁿ *

⟦_⟧ : ∀{i} (r : RE) → Lang i
⟦ 0ʳ ⟧     = ∅
⟦ ⌜ r ⌝ ⟧  = ⟦ r ⟧ⁿ

-- Constructors of RE

1ʳ : RE
1ʳ = ⌜ 1ⁿ ⌝

chʳ : (a : A) → RE
chʳ a = ⌜ chⁿ a ⌝

_+ʳ_ : (r s : RE) → RE
0ʳ +ʳ s = s
r +ʳ 0ʳ = r
⌜ r ⌝ +ʳ ⌜ s  ⌝ = ⌜ r +ⁿ s ⌝

_∙ʳ_ : (r s : RE) → RE
0ʳ ∙ʳ s = 0ʳ
r ∙ʳ 0ʳ = 0ʳ
⌜ r ⌝ ∙ʳ ⌜ s  ⌝ = ⌜ r ∙ⁿ s ⌝

_*ʳ : (r : RE) → RE
0ʳ *ʳ = 1ʳ
⌜ r ⌝ *ʳ = ⌜ r *ⁿ ⌝

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

0≠r : ∀ r → 0ʳ ≅ʳ ⌜ r ⌝ → ⊥
0≠r 1ⁿ p with ≅ν p
... | ()
0≠r (chⁿ a) p with a ≟ a | ≅ν (≅δ p a)
0≠r (chⁿ a) p | yes p₁ | ()
0≠r (chⁿ a) p | no ¬p | q = ¬p (DecSetoid.refl decA)
0≠r (r +ⁿ r₁) p = {!!}  -- Follows from union=∅ ==> both are ∅
0≠r (r ∙ⁿ r₁) p = {!!}  -- Follows from r∙s=∅ ==> both are ∅
0≠r (r *ⁿ) p with ≅ν p
... | ()

plusʳ-empty : ∀ r → (r +ʳ 0ʳ) ≅ʳ r
plusʳ-empty 0ʳ = ≅refl
plusʳ-empty ⌜ r ⌝ = ≅refl

plus-assoc : ∀ r s t → ((r +ʳ s) +ʳ t) ≅ʳ (r +ʳ (s +ʳ t))
plus-assoc 0ʳ s t = ≅refl
plus-assoc ⌜ r ⌝ 0ʳ t = ≅refl
plus-assoc ⌜ r ⌝ ⌜ s ⌝ 0ʳ = ≅refl
plus-assoc ⌜ r ⌝ ⌜ s ⌝ ⌜ t ⌝ = union-assoc _

plus-cong : ∀{r r' s s'} (p : r ≅ʳ r') (q : s ≅ʳ s') → (r +ʳ s) ≅ʳ (r' +ʳ s')
plus-cong {0ʳ} {0ʳ} p q = q
plus-cong {0ʳ} {⌜ r ⌝} p q = ⊥-elim (0≠r r p)
plus-cong {⌜ r ⌝} {0ʳ} p q = ⊥-elim (0≠r r (≅sym p))
plus-cong {⌜ r ⌝} {⌜ r' ⌝} {0ʳ} {0ʳ} p q = p
plus-cong {⌜ r ⌝} {⌜ r' ⌝} {0ʳ} {⌜ s ⌝} p q = ⊥-elim (0≠r s q)
plus-cong {⌜ r ⌝} {⌜ r' ⌝} {⌜ s ⌝} {0ʳ} p q = ⊥-elim (0≠r s (≅sym q))
plus-cong {⌜ r ⌝} {⌜ r' ⌝} {⌜ s ⌝} {⌜ s' ⌝} p q = union-cong p q

plusʳ-idem : ∀ r → ⟦ r +ʳ r ⟧ ≅⟨ ∞ ⟩≅ ⟦ r ⟧
plusʳ-idem 0ʳ = ≅refl
plusʳ-idem ⌜ r ⌝ = union-idem

plus-comm : ∀ r s → ⟦ r +ʳ s ⟧ ≅⟨ ∞ ⟩≅ ⟦ s +ʳ r ⟧
plus-comm 0ʳ 0ʳ = ≅refl
plus-comm 0ʳ ⌜ s ⌝ = ≅refl
plus-comm ⌜ r ⌝ 0ʳ = ≅refl
plus-comm ⌜ r ⌝ ⌜ s ⌝ = union-comm _ _

plus-icm : IdempotentCommutativeMonoid _ _
plus-icm =  record
  { Carrier = RE
  ; _≈_ = _≅ʳ_
  ; _∙_ = _+ʳ_
  ; ε = 0ʳ
  ; isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = ≅ʳisEquivalence
            ; ∙-cong =  λ {r r' s s'} → plus-cong {r} {r'} {s} {s'}
            }
          ; assoc = plus-assoc
          }
        ; identity = (λ r → {! plus-empty !}), plusʳ-empty
        }
      ; comm = plus-comm
      }
    ; idem = plusʳ-idem
    }
  }

comp-empty : ∀ r → (r ∙ʳ 0ʳ) ≅ʳ 0ʳ
comp-empty 0ʳ    = ≅refl
comp-empty ⌜ r ⌝ = ≅refl

comp-assoc : ∀ r s t → ((r ∙ʳ s) ∙ʳ t) ≅ʳ (r ∙ʳ (s ∙ʳ t))
comp-assoc 0ʳ s t = ≅refl
comp-assoc ⌜ r ⌝ 0ʳ t = ≅refl
comp-assoc ⌜ r ⌝ ⌜ s ⌝ 0ʳ = ≅refl
comp-assoc ⌜ r ⌝ ⌜ s ⌝ ⌜ t ⌝ = concat-assoc ⟦ r ⟧ⁿ

plus-comp-distr : ∀ r r' s → ((r +ʳ r') ∙ʳ s) ≅ʳ ((r ∙ʳ s) +ʳ (r' ∙ʳ s))
plus-comp-distr 0ʳ r' s = ≅refl
plus-comp-distr ⌜ r ⌝ 0ʳ s = ≅sym (plusʳ-empty (⌜ r ⌝ ∙ʳ s))
plus-comp-distr ⌜ r ⌝ ⌜ r' ⌝ 0ʳ = ≅refl
plus-comp-distr ⌜ r ⌝ ⌜ r' ⌝ ⌜ s ⌝ = concat-union-distribˡ ⟦ r ⟧ⁿ

comp-plus-distr : ∀ r s s' → (r ∙ʳ (s +ʳ s')) ≅ʳ ((r ∙ʳ s) +ʳ (r ∙ʳ s'))
comp-plus-distr 0ʳ s s' = ≅refl
comp-plus-distr ⌜ r ⌝ 0ʳ s' = ≅refl
comp-plus-distr ⌜ r ⌝ ⌜ s ⌝ 0ʳ = ≅refl
comp-plus-distr ⌜ r ⌝ ⌜ s ⌝ ⌜ s' ⌝ = concat-union-distribʳ ⟦ r ⟧ⁿ

den-unit : ⟦ 1ʳ ⟧ ≅ ε
den-unit =  ≅refl

den-plus : ∀ {i} r s → ⟦ r +ʳ s ⟧ ≅⟨ i ⟩≅ ⟦ r ⟧ ∪ ⟦ s ⟧
den-plus 0ʳ s = ≅sym (union-emptyˡ)
den-plus ⌜ r ⌝ 0ʳ = ≅sym (union-emptyʳ)
den-plus ⌜ r ⌝ ⌜ s ⌝ = ≅refl

den-comp : ∀ {i} r s → ⟦ r ∙ʳ s ⟧ ≅⟨ i ⟩≅ ⟦ r ⟧ · ⟦ s ⟧
den-comp 0ʳ s = ≅sym (concat-emptyˡ _)
den-comp ⌜ r ⌝ 0ʳ = ≅sym (concat-emptyʳ _)
den-comp ⌜ r ⌝ ⌜ s ⌝ = ≅refl
