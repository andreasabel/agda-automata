
open import Library

module RegularGrammar
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA
open import RE decA

-- Let Σ = {a₁,...,aₘ} be a finite alphabet.
-- A regular grammar consists of equations for non-terminals of
-- one of the following forms:
--
--   Y = a₁ Y₁ + ... + aₘ Yₘ
--   Y = a₁ Y₁ + ... + aₘ Yₘ + ε
--
-- Herein, the non-terminals Yᵢ are not necessarily different.
--
-- Let X₁..Xₙ be an enumeration of the n non-terminals of a grammar.
-- The productions for non-terminal Xᵢ can be written as equation
--
--   Xᵢ = rᵢ₁ X₁ + ... + rᵢₙ Xₙ + sᵢ
--
-- where the rᵢⱼ regular expressions which are either 0 or a simple
-- sum of different characters such that Σ{rᵢⱼ|j=1..n} = a₁ + ... + aₘ.
-- The regular expression sᵢ ∈ {0,1}.
--
-- The whole grammar can be expressed as a linear equation system
--
--   X = R·X + s
--
-- where bᵢ ∈ {0,1} and R is a n×n square matrix of regular expressions.
--
-- We can solve this system by a Gauss-like elimination procedure
-- using the law
--
--   L = K·L + M  ==> L = K*·M    (if K ≠ ∅)
--
-- We have for the last variable (non-terminal)
--
--   Xₙ = rₙₙ Xₙ + (rₙ₁ X₁ + ... + rₙ_(n-1) X_(n-1) + sₙ)
--
-- and thus, of rₙₙ = 0,
--
--   Xₙ = rₙ₁ X₁ + ... + rₙ_(n-1) X_(n-1) + sₙ
--
-- and otherwise, if rₙₙ ≠ 0,
--
--   Xₙ = rₙₙ* · (rₙ₁ X₁ + ... + rₙ_(n-1) X_(n-1) + sₙ)
--   Xₙ = rₙₙ*rₙ₁ X₁ + ... + rₙₙ*rₙ_(n-1) X_(n-1) + rₙₙ*sₙ
--
-- We summarize both case as
--
--   Xₙ = rₙ₁' X₁ + ... + rₙ_(n-1)' X_(n-1) + sₙ'
--
-- We substitute the solution in the remaining (n-1) equation
-- and get a system of (n-1) linear equations.
--
--   Xᵢ = rᵢ₁ X₁ + ... + rᵢ(n-1) X(n-1) + rᵢₙ Xₙ + sᵢ
--     =  (rᵢ₁ + rₙ₁') X₁ + ... + (rᵢ(n-1) + rₙ(n-1)') X(n-1) + (sᵢ + sₙ')
--
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

-- Correctness proofs

-- Evaluation is a morphism of vector spaces

eval-plus : ∀{n} (v w : LinComb n) (ρ  : Vec RE (pred n)) →
  eval (v +ᵛ w) ρ ≅ʳ (eval v ρ +ʳ eval w ρ)
eval-plus [] [] _ = ≅sym union-empty
eval-plus (a ∷ []) (b ∷ []) [] = plus-correct a _
eval-plus (a ∷ a' ∷ v) (b ∷ b' ∷ w) (r ∷ ρ) = {!!}  -- This should be an instance of AC for +.

eval-scale : ∀{n} (v : LinComb n) {a} {ρ} → eval (a ∙ᵛ v) ρ ≅ʳ (a ∙ʳ eval v ρ)
eval-scale = {!!} -- This should follow from the distributivity law.

-- Substitution

subst-correct : ∀{n} (v : LinComb (2 + n)) {w : LinComb (1 + n)} {ρ : Vec RE n} →
  eval (subst w v) ρ ≅ʳ eval v (eval w ρ ∷ ρ)
subst-correct (a ∷ b ∷ v) {w} {ρ} = begin
  eval (subst w (a ∷ b ∷ v)) ρ      ≡⟨⟩
  eval ((a ∙ᵛ w) +ᵛ (b ∷ v)) ρ       ≈⟨ eval-plus (a ∙ᵛ w) _ _ ⟩
  eval (a ∙ᵛ w) ρ +ʳ eval (b ∷ v) ρ  ≈⟨ union-cong (eval-scale w {a = a}) ≅refl ⟩
  (a ∙ʳ eval w ρ) +ʳ eval (b ∷ v) ρ  ≈⟨ union-cong (≅sym (times-correct a _)) ≅refl ⟩
  (a ∙ˢ eval w ρ) +ʳ eval (b ∷ v) ρ  ≈⟨  ≅sym (plus-correct (a ∙ˢ eval w ρ) _) ⟩
  (a ∙ˢ eval w ρ) +ˢ eval (b ∷ v) ρ  ≡⟨⟩
  eval (a ∷ b ∷ v) (eval w ρ ∷ ρ)    ∎ where open EqR REq


-- Semantics of a linear combination

⟦_⟧ᵛ : ∀{n i} → LinComb n → Vec (Lang i) (pred n) → Lang i
⟦ []           ⟧ᵛ _        = ∅
⟦ a ∷ []       ⟧ᵛ _        = ⟦ a ⟧
⟦ a ∷ (b ∷ bs) ⟧ᵛ (l ∷ ls) = ⟦ a ⟧ · l ∪ ⟦ b ∷ bs ⟧ᵛ ls
