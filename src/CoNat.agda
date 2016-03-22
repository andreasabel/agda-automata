open import Size
open import Relation.Binary.PropositionalEquality

mutual
  record CoNat i : Set where
    coinductive; constructor delay
    field force : ∀{j : Size< i} → CoNat' j

  data CoNat' i : Set where
    zero : CoNat' i
    suc  : (n : CoNat i) → CoNat' i

-- -- _+'_ : ∀{i} (n : CoNat i) {j : Size< i} (m : CoNat' j) → CoNat i
-- -- CoNat.force (n +' m) with CoNat.force n
-- -- ... | zero  = m
-- -- ... | suc n' = suc (n' +' m)

-- _+_ : ∀{i} (n m : CoNat i) → CoNat i
-- CoNat.force (n + m) with CoNat.force n
-- ... | zero   = CoNat.force m
-- ... | suc n' = suc (n' + m)

_+_  : ∀{i} (n m : CoNat i) → CoNat i
_+'_ : ∀{i} {j : Size< i} (n : CoNat' j) (m : CoNat i) → CoNat' j

CoNat.force (n + m) = CoNat.force n +' m

zero   +' m = CoNat.force m
suc n' +' m = suc (n' + m)

-- _*suc_ : ∀{i} (n : CoNat i) (m : CoNat i) → CoNat i
-- CoNat.force (n *suc m) {j} with CoNat.force n {j}
-- ... | zero   = zero
-- ... | suc n' = suc (m + (n' *suc m ))

_*suc_  : ∀{i} (n : CoNat i) (m : CoNat i) → CoNat i
_*suc'_ : ∀{i} (n : CoNat (↑ i)) (m : CoNat i) → CoNat' i

CoNat.force (n *suc m) = n *suc' m

n *suc' m with CoNat.force n
... | zero   = zero
... | suc n' = suc (m + (n' *suc m ))

_*_  : ∀{i} (n : CoNat i) (m : CoNat i) → CoNat i
CoNat.force (n * m) with CoNat.force m
... | zero   = zero
... | suc m' = n *suc' m'

-- -- _+'_ : ∀{i} (n m : CoNat' i) → CoNat' i
-- -- zero +' m = m
-- -- suc n +' m = suc (CoNat.force n +' m)

-- _+'_ : ∀{i} (n : CoNat (↑ i)) (m : CoNat' i) → CoNat (↑ i)
-- n +' m = n + delay m

mutual
  record _≅⟨_⟩_ (n : CoNat ∞) (i : Size) (m : CoNat ∞) : Set where
    coinductive; constructor delay≅
    field force≅ : ∀{j : Size< i} → CoNat.force n ≅'⟨ j ⟩ CoNat.force m

  data _≅'⟨_⟩_ : (n : CoNat' ∞) (i : Size) (m : CoNat' ∞) → Set where
    zero≅ : ∀{i} → zero ≅'⟨ i ⟩ zero
    suc≅  : ∀{i} {n m : CoNat ∞} (p : n ≅⟨ i ⟩ m) → suc n ≅'⟨ i ⟩ suc m

open _≅⟨_⟩_

0ᶜ : CoNat ∞
CoNat.force 0ᶜ = zero

sucᶜ : ∀{i} (n : CoNat i) → CoNat (↑ i)
CoNat.force (sucᶜ n) = suc n

1ᶜ : CoNat ∞
CoNat.force 1ᶜ = suc 0ᶜ

n+0 : ∀{i} (n : CoNat ∞) → (n + 0ᶜ) ≅⟨ i ⟩ n
force≅ (n+0 n) with CoNat.force n
... | zero   = zero≅
... | suc n' = suc≅ (n+0 n')

n+suc : ∀{i} (n m : CoNat ∞) → (n + sucᶜ m) ≅⟨ i ⟩ sucᶜ (n + m)
force≅ (n+suc n m) with inspect CoNat.force n
force≅ (n+suc n m) | zero   = suc≅ {!!}
force≅ (n+suc n m) | suc n' = {!!}

n*0 : ∀{i} (n : CoNat ∞) → (n * 0ᶜ) ≅⟨ i ⟩ 0ᶜ
force≅ (n*0 n) = zero≅

0*suc' : ∀{i} (n : CoNat ∞) → (0ᶜ *suc' n) ≅'⟨ i ⟩ zero
0*suc' n with CoNat.force n
... | zero  = zero≅
... | suc _ = zero≅

0*suc : ∀{i} (n : CoNat ∞) → (0ᶜ *suc n) ≅⟨ i ⟩ 0ᶜ
force≅ (0*suc n) = 0*suc' n

0*n : ∀{i} (n : CoNat ∞) → (0ᶜ * n) ≅⟨ i ⟩ 0ᶜ
force≅ (0*n n) with CoNat.force n
... | zero  = zero≅
... | suc _ = zero≅

1*suc  : ∀{i} (n : CoNat ∞) → (1ᶜ *suc n)  ≅⟨ i ⟩  delay (suc n)
1*suc' : ∀{i} (n : CoNat ∞) → (1ᶜ *suc' n) ≅'⟨ i ⟩ suc n

force≅ (1*suc n) = 1*suc' n
1*suc' n = suc≅ {!trans≅ (cong≅ (_+_ n) (0*suc n)) (n+0 n)!}  -- n + 0ᶜ *suc n = n

1*n : ∀{i} (n : CoNat ∞) → (1ᶜ * n) ≅⟨ i ⟩ n
force≅ (1*n n) with CoNat.force n
... | zero   = zero≅
... | suc n' = suc≅ {!trans≅ (cong≅ (_+_ n') (0*suc n')) (n+0 n')!}
