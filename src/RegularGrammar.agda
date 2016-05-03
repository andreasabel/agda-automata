
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

-- Scaling

_∙ᵛ_ : ∀{n} → RE → Vec RE n → Vec RE n
r ∙ᵛ v = Vec.map (λ s → r ∙ˢ s) v

-- Addition

_+ᵛ_ : ∀{n} (v w : Vec RE n) → Vec RE n
v +ᵛ w = Vec.zipWith (_+ˢ_) v w

-- We represent the linear combination in n variables
--
--   v = a₁ X₁ + ... + aₙ Xₙ + a₀
--
-- as vector aₙ ∷ ... ∷ a₁ ∷ a₀

-- LinComb (suc n) is a linear combination in n variables
-- LinComb 0       is the empty sum which represent the empty language

LinComb : ℕ → Set
LinComb n = Vec RE n

-- Valuing a linear combination

eval : ∀{n} → LinComb n → Vec RE (pred n) → RE
eval [] _ = 0ʳ
eval (a ∷ []) _ = a
eval (a ∷ (b ∷ bs)) (r ∷ rs) = (a ∙ˢ r) +ˢ eval (b ∷ bs) rs

-- Substitute w for the first variable (Xₙ) in v.
-- We need to substitute at least one variable.

-- Semantics: eval (subst w v) ρ ≅ʳ eval v (eval w ρ ∷ ρ)

subst : ∀{n} → LinComb (1 + n) → LinComb (2 + n) → LinComb (1 + n)
subst w (r ∷ v)  = (r ∙ᵛ w)  +ᵛ v

-- parallel substitution is a kind of matrix multiplication
psubst : ∀{n m} → Vec (LinComb n) m → LinComb m → LinComb n
psubst {n} a v = Vec.foldr (λ _ → LinComb n) (_+ᵛ_) (Vec.replicate 0ʳ)
  (Vec.zipWith (_∙ᵛ_) v a)

-- One step of the Gaussian algorithm.
-- We have a work-list and a solution list.
-- One step moves one equation from the work list to the solution list.

-- We have m+1 equations in n+1 variables.
-- The first equation is the one we eliminate and return as "solved".

step : ∀{n m} → Vec (LinComb (2 + n)) (suc m) → Vec (LinComb (1 + n)) (suc m)
step ((r ∷ v) ∷ vs) = v' ∷ Vec.map (subst v') vs
  where
    v' = (r *ˢ) ∙ᵛ v

gauss : ∀{n}
   → Vec (LinComb (suc n)) (suc n)
  →  Vec (LinComb 1) (suc n)
gauss (w ∷ []) = w ∷ []
gauss (w ∷ (w₀ ∷ ws)) with step (w ∷ (w₀ ∷ ws))
... | w' ∷ ws' with gauss ws'
... | vs = psubst vs w' ∷ vs

-- gauss : ∀{n m}
--   (work-list : Vec (LinComb (suc n)) (suc n))
--   (sol-list  : Vec (LinComb (suc n)) m)  -- reversed
--   → Vec (LinComb 1) (suc n + m)
-- gauss (w ∷ []) vs = w ∷ vs
-- gauss (w ∷ (w₀ ∷ ws)) vs with step (w ∷ (w₀ ∷ ws))
-- ... | w' ∷ ws' = gauss {! ws' !} {! w' ∷ Vec.map (subst w') vs !}

-- [[ gauss ws vs ]] = [[ revapp vs ws ]]
