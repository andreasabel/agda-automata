
open import Library

module RegularGrammar
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

import Language
import RENotNullable

open module LA = Language decA
open module RA = RENotNullable decA

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
-- All of the rᵢⱼ are not nullable.
--
-- The whole grammar can be expressed as a linear equation system
--
--   X = R·X + s
--
-- where bᵢ ∈ {0,1} and R is a n×n square matrix of regular expressions
-- that are not nullable.
--
-- We can solve this system by a Gauss-like elimination procedure
-- using the law
--
--   L = K·L + M  ==> L = K*·M    (unless K is nullable)
--
-- We have for the last variable (non-terminal)
--
--   Xₙ = rₙₙ Xₙ + (rₙ₁ X₁ + ... + rₙ_(n-1) X_(n-1) + sₙ)
--
-- and thus, if rₙₙ not nullable,
--
--   Xₙ = rₙₙ* · (rₙ₁ X₁ + ... + rₙ_(n-1) X_(n-1) + sₙ)
--   Xₙ = rₙₙ*rₙ₁ X₁ + ... + rₙₙ*rₙ_(n-1) X_(n-1) + rₙₙ*sₙ
--
-- With appropriate definition of r' and s' this is
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

-- -- Scaling

-- _∙ᵛ_ : ∀{n} → RE → Vec RE n → Vec RE n
-- r ∙ᵛ v = Vec.map (λ s → r ∙ʳ s) v

-- -- Addition

-- _+ᵛ_ : ∀{n} (v w : Vec RE n) → Vec RE n
-- v +ᵛ w = Vec.zipWith (_+ʳ_) v w

-- We represent the linear combination in n variables
--
--   v = a₁ X₁ + ... + aₙ Xₙ + a₀
--
-- as pair of a vector aₙ ∷ ... ∷ a₁ ∷ [] and a final coefficient a₀
-- The coefficients of the Xᵢ are assumed to be non-nullable.

-- LinComb n is a linear combination in n variables

record LinComb (n : ℕ) : Set where
  constructor _+ᶜ_
  field v : Vec Renn n
        c : RE

_∷ᶜ_ : ∀{n} → Renn → LinComb n → LinComb (suc n)
r ∷ᶜ (v +ᶜ c) = (r ∷ v) +ᶜ c

-- Semantics of a linear combination

⟦_⟧ᵛ : ∀{n i} → LinComb n → Vec (Lang i) n → Lang i
⟦ []       +ᶜ c ⟧ᵛ ρ       = ⟦ c ⟧
⟦ (a ∷ as) +ᶜ c ⟧ᵛ (l ∷ ρ) = ⟦ a ⟧ⁿ · l ∪ ⟦ as +ᶜ c ⟧ᵛ ρ
-- ⟦ []           ⟧ᵛ _        = ∅
-- ⟦ a ∷ []       ⟧ᵛ _        = ⟦ a ⟧
-- ⟦ a ∷ (b ∷ bs) ⟧ᵛ (l ∷ ls) = ⟦ a ⟧ · l ∪ ⟦ b ∷ bs ⟧ᵛ ls

-- Scaling

_∙ᵛ_ : ∀{n} → RE → LinComb n → LinComb n
r ∙ᵛ (v +ᶜ c) = Vec.map (r ∙ⁿ_) v +ᶜ (r ∙ʳ c)

-- Addition

_+ᵛ_ : ∀{n} (v w : LinComb n) → LinComb n
(v +ᶜ c) +ᵛ (w +ᶜ d) = Vec.zipWith (_+ⁿ_) v w +ᶜ (c +ʳ d)

-- Zero

0ᵛ : ∀{n} → LinComb n
0ᵛ = Vec.replicate 0ⁿ +ᶜ 0ʳ

{-
-- Simplification if first coefficient is 0

sem-empty : ∀{i n} (v : LinComb n) (ls : Vec (Lang ∞) n) →

  ⟦ 0ʳ ∷ v ⟧ᵛ ls ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ (Vec.tail' ls)

sem-empty [] ls = ≅refl
sem-empty (a ∷ []) (l ∷ ls) = union-concat-empty
sem-empty (a ∷ b ∷ v) (l ∷ ls) = union-concat-empty
-}

-- Semantics is a vector space morphism

-- Scaling a linear combination is sound

sound-scale : ∀{i n} a (v : LinComb n) ρ →

  ⟦ a ∙ᵛ v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ a ⟧ · ⟦ v ⟧ᵛ ρ

sound-scale a ([]      +ᶜ c) ρ = ≅refl
sound-scale a ((b ∷ v) +ᶜ c) (l ∷ ρ) = begin

    ⟦ a ∙ᵛ ((b ∷ v) +ᶜ c) ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
    ⟦ a ∙ⁿ b ⟧ⁿ · l ∪ ⟦ a ∙ᵛ (v +ᶜ c) ⟧ᵛ ρ

  ≈⟨  union-congʳ (sound-scale a (v +ᶜ c) ρ)  ⟩

    (⟦ a ⟧ · ⟦ b ⟧ⁿ) · l ∪ ⟦ a ⟧ · ⟦ v +ᶜ c ⟧ᵛ ρ

  ≈⟨ union-congˡ (concat-assoc ⟦ a ⟧) ⟩

    ⟦ a ⟧ · (⟦ b ⟧ⁿ · l) ∪ ⟦ a ⟧ · ⟦ v +ᶜ c ⟧ᵛ ρ

  ≈⟨ ≅sym (concat-union-distribʳ ⟦ a ⟧) ⟩

    ⟦ a ⟧ · (⟦ b ⟧ⁿ · l ∪ ⟦ v +ᶜ c ⟧ᵛ ρ)
  ≡⟨⟩
    ⟦ a ⟧ · ⟦ (b ∷ v) +ᶜ c ⟧ᵛ (l ∷ ρ)
  ∎
  where
  open EqR (Bis _)


-- Adding linear combinations is sound

sound-plus : ∀{i n} (v w : LinComb n) (ρ  : Vec (Lang ∞) n) →
  ⟦ v +ᵛ w ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ ρ ∪ ⟦ w ⟧ᵛ ρ
sound-plus ([] +ᶜ c) ([] +ᶜ d) [] = ≅refl
sound-plus ((a ∷ v) +ᶜ c) ((b ∷ w) +ᶜ d) (l ∷ ρ) = begin

    ⟦ ((a ∷ v) +ᶜ c) +ᵛ ((b ∷ w) +ᶜ d) ⟧ᵛ (l ∷ ρ)

  ≡⟨⟩

    ⟦ a +ⁿ b ⟧ⁿ · l ∪ ⟦ v' +ᵛ w' ⟧ᵛ ρ

  ≈⟨ union-congʳ (sound-plus v' w' ρ) ⟩

    (⟦ a ⟧ⁿ ∪ ⟦ b ⟧ⁿ) · l ∪ ( ⟦ v' ⟧ᵛ ρ ∪ ⟦ w' ⟧ᵛ ρ)

  ≈⟨ union-congˡ (concat-union-distribˡ ⟦ a ⟧ⁿ) ⟩

    (⟦ a ⟧ⁿ · l ∪ ⟦ b ⟧ⁿ · l) ∪ (⟦ v' ⟧ᵛ ρ ∪ ⟦ w' ⟧ᵛ ρ)

  ≈⟨ prove 4 ((x₁ ⊕ x₂) ⊕ (x₃ ⊕ x₄))
             ((x₁ ⊕ x₃) ⊕ (x₂ ⊕ x₄)) (⟦ a ⟧ⁿ · l ∷ ⟦ b ⟧ⁿ · l ∷ ⟦ v' ⟧ᵛ ρ ∷ ⟦ w' ⟧ᵛ ρ ∷ []) ⟩

    ((⟦ a ⟧ⁿ · l) ∪ ⟦ v' ⟧ᵛ ρ) ∪ ((⟦ b ⟧ⁿ · l) ∪ ⟦ w' ⟧ᵛ ρ)

  ≡⟨⟩

    ⟦ (a ∷ v) +ᶜ c ⟧ᵛ (l ∷ ρ) ∪ ⟦ (b ∷ w) +ᶜ d ⟧ᵛ (l ∷ ρ)

  ∎  where
    v' = v +ᶜ c
    w' = w +ᶜ d
    open EqR (Bis _)
    open ICMSolver (union-icm _) using (prove; Expr; var; _⊕_)
    x₁ x₂ x₃ x₄ : Expr 4
    x₁ = var (zero)
    x₂ = var (suc zero)
    x₃ = var (suc (suc zero))
    x₄ = var (suc (suc (suc zero)))

sound-zero : ∀{i n}(ρ : Vec (Lang ∞) n) → ⟦ 0ᵛ ⟧ᵛ ρ ≅⟨ i ⟩≅ ∅
sound-zero [] = ≅refl
sound-zero (l ∷ ρ) = ≅trans union-concat-empty (sound-zero ρ)

-- Substitute w for the first variable (Xₙ) in v.
-- We need to substitute at least one variable.

-- Semantics: ⟦ subst w v ⟧ᵛ ρ ≅ʳ ⟦ v ⟧ᵛ (⟦ w ⟧ᵛ ρ ∷ ρ)

subst : ∀{n} → LinComb n → LinComb (1 + n) → LinComb n
subst w ((r ∷ v) +ᶜ c) = (re r ∙ᵛ w) +ᵛ (v +ᶜ c)

sound-subst : ∀ {i n} (w : LinComb n) (v : LinComb (1 + n)) (ρ : Vec (Lang ∞) n) →
  ⟦ subst w v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ (⟦ w ⟧ᵛ ρ ∷ ρ)
sound-subst w ((a ∷ v) +ᶜ c) ρ = begin
  ⟦ subst w ((a ∷ v) +ᶜ c) ⟧ᵛ ρ     ≡⟨⟩
  ⟦ (re a ∙ᵛ w) +ᵛ v' ⟧ᵛ ρ          ≈⟨ sound-plus (re a ∙ᵛ w) v' ρ ⟩
  ⟦ re a ∙ᵛ w  ⟧ᵛ ρ ∪ ⟦ v' ⟧ᵛ ρ     ≈⟨ union-congˡ (sound-scale (re a) w ρ) ⟩
  ⟦ a ⟧ⁿ · ⟦ w  ⟧ᵛ ρ ∪ ⟦ v' ⟧ᵛ ρ    ≡⟨⟩
  ⟦ (a ∷ v) +ᶜ c ⟧ᵛ (⟦ w ⟧ᵛ ρ ∷ ρ)
  ∎ where
    open EqR (Bis _)
    v' = v +ᶜ c


-- The semantics of m equations in n-1 variables:

⟦_⟧ᴹ : ∀{i n m} → Vec (LinComb n) m → Vec (Lang i) n → Vec (Lang i) m
⟦ M ⟧ᴹ ρ = Vec.map (λ v → ⟦ v ⟧ᵛ ρ) M

_≅⟨_⟩≅ᴸ_ : ∀{n} (L : Vec (Lang ∞) n) (i : Size) (L' : Vec (Lang ∞) n) → Set
L ≅⟨ i ⟩≅ᴸ L' = Vec.All₂ (λ l l' → l ≅⟨ i ⟩≅ l') L L'

-- sound-psubst : ∀{i n m} (A : Vec (LinComb n) m) (v : LinComb m) (ρ : Vec (Lang ∞) (pred n)) →
--   ⟦ psubst A v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ (⟦ A ⟧ᴹ ρ)
-- sound-psubst A v ρ = {!!}

-- One step of the Gaussian algorithm.

-- We have m+1 equations in n+1 variables.
-- The first equation is the one we eliminate and return as "solved".

-- L = K·L + M  ==> L = K*·M    (unless K is nullable)

step : ∀{n m} → Vec (LinComb (suc n)) (suc m) → Vec (LinComb n) (suc m)
step (((r ∷ v) +ᶜ c) ∷ vs) = v' ∷ Vec.map (subst v') vs
  where
    v' = (r *ⁿ) ∙ᵛ (v +ᶜ c)

--   L = r·L + a  ==> L = r*·a    (if r ≠ ∅)
--   r*·a = r·r*·a + a

unused-lemma : ∀{i n} r (v : LinComb n) (ρ : Vec (Lang ∞) n) →
   ⟦ (r *ⁿ) ∙ᵛ v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ r ∷ᶜ v ⟧ᵛ (⟦ (r *ⁿ) ∙ᵛ v ⟧ᵛ ρ ∷ ρ)
unused-lemma r ([] +ᶜ c) ρ = star-concat _   -- Law for star
unused-lemma {i} r ((a ∷ v) +ᶜ c) (l ∷ ρ) = begin
    ⟦ r* ∙ᵛ ((a ∷ v) +ᶜ c) ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
    ⟦ (r* ∙ⁿ a) ∷ᶜ (r* ∙ᵛ v') ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
     ⟦ r* ∙ⁿ a ⟧ⁿ · l ∪ ⟦ r* ∙ᵛ v' ⟧ᵛ ρ
  ≈⟨ {!!} ⟩
    ⟦ r ⟧ⁿ · (⟦ r* ∙ⁿ a ⟧ⁿ · l ∪ ⟦ r* ∙ᵛ v' ⟧ᵛ ρ) ∪ (⟦ a ⟧ⁿ · l ∪ ⟦ v' ⟧ᵛ ρ)
  ≡⟨⟩
    ⟦ r ⟧ⁿ · ⟦ (r* ∙ⁿ a) ∷ᶜ (r* ∙ᵛ v') ⟧ᵛ (l ∷ ρ) ∪ (⟦ a ⟧ⁿ · l ∪ ⟦ v' ⟧ᵛ ρ)
  ≡⟨⟩
    ⟦ r ⟧ⁿ · ⟦ r* ∙ᵛ ((a ∷ v) +ᶜ c) ⟧ᵛ (l ∷ ρ) ∪ ⟦ (a ∷ v) +ᶜ c ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
    ⟦ (r ∷ (a ∷ v)) +ᶜ c ⟧ᵛ (⟦ r* ∙ᵛ ((a ∷ v) +ᶜ c) ⟧ᵛ (l ∷ ρ) ∷ l ∷ ρ)
  ∎
  where
  v' : LinComb _
  v' = v +ᶜ c
  r* : RE
  r* = (re r *ʳ)
  open EqR (Bis _)


sound-step : ∀{i n m} (M : Vec (LinComb (suc n)) (suc m)) (ρ : Vec (Lang ∞) n) →
  let M' = step M; l = ⟦ Vec.head M' ⟧ᵛ ρ
  in  ⟦ M' ⟧ᴹ ρ ≅⟨ i ⟩≅ᴸ ⟦ M ⟧ᴹ (l ∷ ρ)

sound-step {i} {n} (((r ∷ v) +ᶜ c) ∷ M) ρ = (begin
    ⟦ (r *ⁿ) ∙ᵛ v' ⟧ᵛ ρ
  ≈⟨ sound-scale (r *ⁿ) v' ρ ⟩
    ⟦ r *ⁿ ⟧ · ⟦ v' ⟧ᵛ ρ
  ≡⟨⟩
    ⟦ r ⟧ⁿ * · ⟦ v' ⟧ᵛ ρ
  ≈⟨ star-concat ⟦ r ⟧ⁿ  ⟩
     ⟦ r ⟧ⁿ · (⟦ r ⟧ⁿ * · ⟦ v' ⟧ᵛ ρ) ∪ ⟦ v' ⟧ᵛ ρ
  ≡⟨⟩
     ⟦ r ⟧ⁿ · (⟦ r *ⁿ ⟧ · ⟦ v' ⟧ᵛ ρ) ∪ ⟦ v' ⟧ᵛ ρ
  ≈⟨ union-congˡ (concat-congʳ (≅sym (sound-scale (r *ⁿ) v' ρ))) ⟩
     ⟦ r ⟧ⁿ · ⟦ (r *ⁿ) ∙ᵛ v' ⟧ᵛ ρ ∪ ⟦ v' ⟧ᵛ ρ
  ∎) ∷ᵃ lem M
  where
  open EqR (Bis i)
  v' = v +ᶜ c
  v'' = (r *ⁿ) ∙ᵛ v'
  lem : ∀ {i m} (M : Vec (LinComb (suc n)) m) →
      (Vec.map (λ v₁ → ⟦ v₁ ⟧ᵛ ρ) (Vec.map (subst v'') M))
      ≅⟨ i ⟩≅ᴸ
      (Vec.map (λ v₁ → ⟦ v₁ ⟧ᵛ (⟦ v'' ⟧ᵛ ρ ∷ ρ)) M)
  lem [] = []ᵃ
  lem (w ∷ M') = (sound-subst v'' w ρ) ∷ᵃ (lem M')


-- -- parallel substitution is a kind of matrix multiplication
-- --
-- -- psubst (wₙ-1 ∷ ... ∷ w₀ ∷ []) (aₙ-1 ∷ ... ∷ a₀ ∷ [])
-- --   = aₙ-1 ∙ᵛ wₙ-1 +ᵛ ... +ᵛ a₀ ∙ᵛ w₀ +ᵛ 0ᵛ
-- psubst : ∀{n m} → Vec (LinComb n) m → LinComb m → LinComb n
-- psubst {n} M (v +ᶜ c) = Vec.foldr (λ _ → LinComb n) (_+ᵛ_) 0ᵛ
--   (Vec.zipWith (λ r → re r ∙ᵛ_) v M)


-- old-gauss : ∀{n}
--    → Vec (LinComb (suc n)) (suc n)
--   →  Vec (LinComb 1) (suc n)
-- old-gauss (w ∷ []) = w ∷ []
-- old-gauss (w ∷ (w₀ ∷ ws)) with step (w ∷ (w₀ ∷ ws))
-- ... | w' ∷ ws' with old-gauss ws'
-- ... | vs = psubst vs w' ∷ vs

scalar-l : ∀{n} → Vec RE (suc n) → LinComb n → RE
scalar-l (a ∷ [])       ([]      +ᶜ c) = a ∙ʳ c
scalar-l (a ∷ (a' ∷ v)) ((b ∷ w) +ᶜ c) = (a ∙ʳ re b) +ʳ scalar-l (a' ∷ v) (w +ᶜ c)

scalar : ∀{n} (as : Vec Renn n) (bs : Vec RE n) → Renn
scalar [] [] = 0ⁿ
scalar (a ∷ as) (b ∷ bs) = (a ⁿ∙ b) +ⁿ scalar as bs

gauss : ∀{n}
   → Vec (LinComb n) n
   → Vec RE n
gauss [] = []
gauss (w ∷ ws) with step (w ∷ ws)
-- ... | ([] +ᶜ c) ∷ [] = c ∷ []
... | (as +ᶜ c) ∷ ws' = (re (scalar as bs) +ʳ c) ∷ bs
  where bs = gauss ws'

sound-gauss : ∀{i n} (M : Vec (LinComb n) n) →
  let  ρ = Vec.map ⟦_⟧ (gauss M)
  in   ⟦ M ⟧ᴹ ρ ≅⟨ i ⟩≅ᴸ  ρ
sound-gauss [] = []ᵃ
sound-gauss (w ∷ M) with step (w ∷ M)
... | (as +ᶜ c) ∷ M' = {!!} ∷ᵃ {!sound-gauss M'!}

-- gauss : ∀{n}
--    → Vec (LinComb (suc n)) (suc n)
--    → Vec RE (suc n)
-- gauss (([] +ᶜ c) ∷ []) = c ∷ []
-- gauss (w ∷ (w₀ ∷ ws)) with step (w ∷ (w₀ ∷ ws))
-- ... | w' ∷ ws' with gauss ws'
-- ... | vs = scalar vs w' ∷ vs


-- sound-gauss : ∀{n} (M : Vec (LinComb (suc n)) (suc n)) →
--   let  ρ = Vec.map ⟦_⟧ (gauss M)  in  ⟦ M ⟧ᴹ ρ ≅ ρ
-- sound-gauss = ?

-- We have a work-list and a solution list.
-- One step moves one equation from the work list to the solution list.
-- gauss : ∀{n m}
--   (work-list : Vec (LinComb (suc n)) (suc n))
--   (sol-list  : Vec (LinComb (suc n)) m)  -- reversed
--   → Vec (LinComb 1) (suc n + m)
-- gauss (w ∷ []) vs = w ∷ vs
-- gauss (w ∷ (w₀ ∷ ws)) vs with step (w ∷ (w₀ ∷ ws))
-- ... | w' ∷ ws' = gauss {! ws' !} {! w' ∷ Vec.map (subst w') vs !}

-- [[ gauss ws vs ]] = [[ revapp vs ws ]]

-- Evaluation of linear combinations to regular expressions
------------------------------------------------------------------------

-- Valuing a linear combination

eval : ∀{n} → LinComb n → Vec RE n → RE
eval ([] +ᶜ c)_ = c
eval ((a ∷ v) +ᶜ c) (r ∷ rs) = (re a ∙ʳ r) +ʳ eval (v +ᶜ c) rs
{-
-- Evaluation is a morphism of vector spaces

eval-plus : ∀{n} (v w : LinComb n) (ρ  : Vec RE (pred n)) →
  eval (v +ᵛ w) ρ ≅ʳ (eval v ρ +ʳ eval w ρ)
eval-plus [] [] _ =  ≅sym union-empty
eval-plus (a ∷ []) (b ∷ []) [] =  ≅refl
eval-plus (a ∷ a' ∷ v) (b ∷ b' ∷ w) (r ∷ ρ) = begin

    ((a +ʳ b) ∙ʳ r) +ʳ eval (v' +ᵛ w') ρ

  ≈⟨  plus-cong {((a +ʳ b) ∙ʳ r)} {((a ∙ʳ r) +ʳ (b ∙ʳ r))} {eval (v' +ᵛ w') ρ} {eval v' ρ +ʳ eval w' ρ}
      (plus-comp-distr a b r)
      (eval-plus v' w' ρ)  ⟩

    ((a ∙ʳ r) +ʳ (b ∙ʳ r)) +ʳ (eval v' ρ +ʳ eval w' ρ)

  ≡⟨⟩
    ((e₁ +ʳ e₂) +ʳ (e₃ +ʳ e₄))
  ≈⟨ prove 4 ((x₁ ⊕ x₂) ⊕ (x₃ ⊕ x₄)) ((x₁ ⊕ x₃) ⊕ (x₂ ⊕ x₄)) (e₁ ∷ e₂ ∷ e₃ ∷ e₄ ∷ []) ⟩
    ((e₁ +ʳ e₃) +ʳ (e₂ +ʳ e₄))
  ≡⟨⟩

    ((a ∙ʳ r) +ʳ eval v' ρ) +ʳ ((b ∙ʳ r) +ʳ eval w' ρ)

  ∎ where
    v' = a' ∷ v
    w' = b' ∷ w
    open EqR REq
    open ICMSolver plus-icm
    e₁ = a ∙ʳ r
    e₂ = b ∙ʳ r
    e₃ = eval v' ρ
    e₄ = eval w' ρ
    x₁ x₂ x₃ x₄ : Expr 4
    x₁ = var (zero)
    x₂ = var (suc zero)
    x₃ = var (suc (suc zero))
    x₄ = var (suc (suc (suc zero)))


eval-scale : ∀{n} (v : LinComb n) a ρ → eval (a ∙ᵛ v) ρ ≅ʳ (a ∙ʳ eval v ρ)
eval-scale [] a ρ = ≅sym (comp-empty a)
eval-scale (_ ∷ []) a ρ = ≅refl
eval-scale (b ∷ c ∷ w) a (r ∷ ρ) = begin

    (((a ∙ʳ b) ∙ʳ r) +ʳ eval (a ∙ᵛ v) ρ)

  ≈⟨ plus-cong {(a ∙ʳ b) ∙ʳ r} {a ∙ʳ (b ∙ʳ r)} {eval (a ∙ᵛ v) ρ} {a ∙ʳ eval v ρ}
      (comp-assoc a b r)
      (eval-scale v a ρ) ⟩

    ((a ∙ʳ (b ∙ʳ r)) +ʳ (a ∙ʳ eval v ρ))

  ≈⟨ ≅sym (comp-plus-distr a (b ∙ʳ r) (eval v ρ)) ⟩

    (a ∙ʳ ((b ∙ʳ r) +ʳ eval v ρ))
  ∎ where
  v : LinComb _
  v = c ∷ w
  open EqR REq

-- Substitution

subst-correct : ∀{n} (v : LinComb (2 + n)) {w : LinComb (1 + n)} {ρ : Vec RE n} →
  eval (subst w v) ρ ≅ʳ eval v (eval w ρ ∷ ρ)
subst-correct (a ∷ b ∷ v) {w} {ρ} = begin
  eval (subst w (a ∷ b ∷ v)) ρ      ≡⟨⟩
  eval ((a ∙ᵛ w) +ᵛ (b ∷ v)) ρ       ≈⟨ eval-plus (a ∙ᵛ w) _ _ ⟩
  eval (a ∙ᵛ w) ρ +ʳ eval (b ∷ v) ρ  ≈⟨  union-congˡ -- {eval (a ∙ᵛ w) ρ} {a ∙ʳ eval w ρ}
                                         (eval-scale w a ρ)   ⟩
  (a ∙ʳ eval w ρ) +ʳ eval (b ∷ v) ρ  ≡⟨⟩
  eval (a ∷ b ∷ v) (eval w ρ ∷ ρ)    ∎ where open EqR REq

-- -}
-- -}
