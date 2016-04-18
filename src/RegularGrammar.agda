
open import Library

module RegularGrammar
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import RE decA

-- A regular grammar consists of equations for non-terminals of
-- one of the following forms:
--
--   Y = a₁ X₁ + ... + aₙ Xₙ
--   Y = a₁ X₁ + ... + aₙ Xₙ + ε
--
-- The whole grammar can be expressed as a linear equation system
--
--   X = A·X + b
--
-- where bᵢ ∈ {0,1} and A = (aᵢⱼ).  A is a square matrix of regular expressions
-- which contain of exactly one letter each.  We can solve this system
-- by a Gauss-like elimination procedure using the law
--
--   L = K·L + M  ==> L = K*·M    (if K ≠ ∅)
--
-- We have for the last variable (non-terminal)
--
--   Xₙ = aₙₙ Xₙ + (aₙ₁ X₁ + ... + aₙ_(n-1) X_(n-1) + bₙ)
--
-- and thus,
--
--   Xₙ = aₙₙ* · (aₙ₁ X₁ + ... + aₙ_(n-1) X_(n-1) + bₙ)
--   Xₙ = aₙₙ*aₙ₁ X₁ + ... + aₙₙ*aₙ_(n-1) X_(n-1) + aₙₙ*bₙ
--
-- We substitute the solution in the remaining (n-1) equation
-- and get a system of (n-1) linear equations where each of
-- the r.e. coefficients is not ∅.

-- record RHS (n : ℕ) : Set where
--   constructor rhs
--   field coeffs : Vec RE (suc n)

-- Vector space over regular expressions

_∙ᵛ_ : ∀{n} → RE → Vec RE n → Vec RE n
r ∙ᵛ v = Vec.map (λ s → r ∙ˢ s) v

_+ᵛ_ : ∀{n} (v w : Vec RE n) → Vec RE n
v +ᵛ w = Vec.zipWith (_+ˢ_) v w

-- We represent the term
--
--   v = a₁ X₁ + ... + aₙ Xₙ + a₀
--
-- as vector aₙ ∷ ... ∷ a₁ ∷ a₀

-- Substitute w for the first variable (Xₙ) in v.

subst : ∀{n} → Vec RE n → Vec RE (suc n) → Vec RE n
subst w (r ∷ v)  = (r ∙ᵛ w)  +ᵛ v

-- parallel substitution is a kind of matrix multiplication
psubst : ∀{n m} → Vec (Vec RE n) m → Vec RE m → Vec RE n
psubst a v = Vec.foldr (λ _ → Vec RE _) (_+ᵛ_) (Vec.replicate 0ʳ)
  (Vec.zipWith (_∙ᵛ_) v a)

-- One step of the Gaussian algorithm.
-- We have a work-list and a solution list.
-- One step moves one equation from the work list to the solution list.

-- We have m+1 equations in n+1 variables.
-- The first equation is the one we eliminate and return as "solved".

step : ∀{n m} → Vec (Vec RE (suc n)) (suc m) → Vec (Vec RE n) (suc m)
step ((r ∷ v) ∷ vs) = v' ∷ Vec.map (subst v') vs
  where
    v' = (r *ˢ) ∙ᵛ v

gauss : ∀{n}
   → Vec (Vec RE (suc n)) (suc n)
  →  Vec (Vec RE 1) (suc n)
gauss (w ∷ []) = w ∷ []
gauss (w ∷ (w₀ ∷ ws)) with step (w ∷ (w₀ ∷ ws))
... | w' ∷ ws' with gauss ws'
... | vs = psubst vs w' ∷ vs

-- gauss : ∀{n m}
--   (work-list : Vec (Vec RE (suc n)) (suc n))
--   (sol-list  : Vec (Vec RE (suc n)) m)  -- reversed
--   → Vec (Vec RE 1) (suc n + m)
-- gauss (w ∷ []) vs = w ∷ vs
-- gauss (w ∷ (w₀ ∷ ws)) vs with step (w ∷ (w₀ ∷ ws))
-- ... | w' ∷ ws' = gauss {! ws' !} {! w' ∷ Vec.map (subst w') vs !}

-- [[ gauss ws vs ]] = [[ revapp vs ws ]]
