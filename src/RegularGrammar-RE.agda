{-# OPTIONS --sized-types --allow-unsolved-metas #-}

open import Library

module RegularGrammar-RE
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A)) where

open import Language decA
open import RENotNullable decA

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

-- Scaling

_∙ᵛ_ : ∀{n} → RE → Vec RE n → Vec RE n
r ∙ᵛ v = Vec.map (λ s → r ∙ʳ s) v

-- Addition

_+ᵛ_ : ∀{n} (v w : Vec RE n) → Vec RE n
v +ᵛ w = Vec.zipWith (_+ʳ_) v w

-- We represent the linear combination in n variables
--
--   v = a₁ X₁ + ... + aₙ Xₙ + a₀
--
-- as vector aₙ ∷ ... ∷ a₁ ∷ a₀

-- LinComb (suc n) is a linear combination in n variables
-- LinComb 0       is the empty sum which represent the empty language

LinComb : ℕ → Set
LinComb n = Vec RE n

-- Semantics of a linear combination

⟦_⟧ᵛ : ∀{n i} → LinComb n → Vec (Lang i) (pred n) → Lang i
⟦ []           ⟧ᵛ _        = ∅
⟦ a ∷ []       ⟧ᵛ _        = ⟦ a ⟧
⟦ a ∷ (b ∷ bs) ⟧ᵛ (l ∷ ls) = ⟦ a ⟧ · l ∪ ⟦ b ∷ bs ⟧ᵛ ls

-- Simplification if first coefficient is 0

sem-empty : ∀{i n} (v : LinComb n) (ls : Vec (Lang ∞) n) →

  ⟦ 0ʳ ∷ v ⟧ᵛ ls ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ (Vec.tail' ls)

sem-empty [] ls = ≅refl
sem-empty (a ∷ []) (l ∷ ls) = union-concat-empty
sem-empty (a ∷ b ∷ v) (l ∷ ls) = union-concat-empty

-- Semantics is a vector space morphism

-- Scaling a linear combination is sound

sound-scale : ∀{i n} a (v : LinComb n) ρ →

  ⟦ a ∙ᵛ v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ a ⟧ · ⟦ v ⟧ᵛ ρ

sound-scale a [] ρ = ≅sym (concat-emptyʳ _)
sound-scale a (_ ∷ []) ρ = ≅refl
sound-scale a (b ∷ c ∷ w) (l ∷ ρ) = begin

    ⟦ a ∙ᵛ (b ∷ v) ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
    ⟦ a ∙ʳ b ⟧ · l ∪ ⟦ a ∙ᵛ v ⟧ᵛ ρ

  ≈⟨ union-cong (concat-congˡ (den-comp a b)) (sound-scale a v ρ) ⟩

    (⟦ a ⟧ · ⟦ b ⟧) · l ∪ ⟦ a ⟧ · ⟦ v ⟧ᵛ ρ

  ≈⟨ union-congˡ (concat-assoc ⟦ a ⟧) ⟩

    ⟦ a ⟧ · (⟦ b ⟧ · l) ∪ ⟦ a ⟧ · ⟦ v ⟧ᵛ ρ

  ≈⟨ ≅sym (concat-union-distribʳ ⟦ a ⟧) ⟩

    ⟦ a ⟧ · (⟦ b ⟧ · l ∪ ⟦ v ⟧ᵛ ρ)
  ≡⟨⟩
    ⟦ a ⟧ · ⟦ b ∷ v ⟧ᵛ (l ∷ ρ)
  ∎
  where
  v : LinComb _
  v = c ∷ w
  open EqR (Bis _)

-- Adding linear combinations is sound

sound-plus : ∀{i n} (v w : LinComb n) (ρ  : Vec (Lang ∞) (pred n)) →
  ⟦ v +ᵛ w ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ ρ ∪ ⟦ w ⟧ᵛ ρ
sound-plus [] [] _ = ≅sym union-emptyˡ
sound-plus (a ∷ []) (b ∷ []) [] = den-plus a b
sound-plus (a ∷ a' ∷ v') (b ∷ b' ∷ w') (l ∷ ρ) = begin

    ⟦ (a ∷ v) +ᵛ (b ∷ w) ⟧ᵛ (l ∷ ρ)

  ≡⟨⟩

    ⟦ a +ʳ b ⟧ · l ∪ ⟦ v +ᵛ w ⟧ᵛ ρ

  ≈⟨ union-cong (concat-congˡ (den-plus a b)) (sound-plus v w ρ) ⟩

    (⟦ a ⟧ ∪ ⟦ b ⟧) · l ∪ ( ⟦ v ⟧ᵛ ρ ∪ ⟦ w ⟧ᵛ ρ)

  ≈⟨ union-congˡ (concat-union-distribˡ ⟦ a ⟧) ⟩

    (⟦ a ⟧ · l ∪ ⟦ b ⟧ · l) ∪ (⟦ v ⟧ᵛ ρ ∪ ⟦ w ⟧ᵛ ρ)

  ≈⟨ prove 4 ((x₁ ⊕ x₂) ⊕ (x₃ ⊕ x₄)) ((x₁ ⊕ x₃) ⊕ (x₂ ⊕ x₄)) (⟦ a ⟧ · l ∷ ⟦ b ⟧ · l ∷ ⟦ v ⟧ᵛ ρ ∷ ⟦ w ⟧ᵛ ρ ∷ []) ⟩

    ((⟦ a ⟧ · l) ∪ ⟦ v ⟧ᵛ ρ) ∪ ((⟦ b ⟧ · l) ∪ ⟦ w ⟧ᵛ ρ)

  ≡⟨⟩

    ⟦ a ∷ v ⟧ᵛ (l ∷ ρ) ∪ ⟦ b ∷ w ⟧ᵛ (l ∷ ρ)

  ∎  where
    v = a' ∷ v'
    w = b' ∷ w'
    open EqR (Bis _)
    open ICMSolver (union-icm _) using (prove; Expr; var; _⊕_)
    x₁ x₂ x₃ x₄ : Expr 4
    x₁ = var (zero)
    x₂ = var (suc zero)
    x₃ = var (suc (suc zero))
    x₄ = var (suc (suc (suc zero)))

-- Substitute w for the first variable (Xₙ) in v.
-- We need to substitute at least one variable.

-- Semantics: ⟦ subst w v ⟧ᵛ ρ ≅ʳ ⟦ v ⟧ᵛ (⟦ w ⟧ᵛ ρ ∷ ρ)

subst : ∀{n} → LinComb (1 + n) → LinComb (2 + n) → LinComb (1 + n)
subst w (r ∷ v) = (r ∙ᵛ w) +ᵛ v

sound-subst : ∀ {i n} (v : LinComb (2 + n)) (w : LinComb (1 + n)) (ρ : Vec (Lang ∞) n) →
  ⟦ subst w v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ (⟦ w ⟧ᵛ ρ ∷ ρ)
sound-subst (a ∷ b ∷ v') w ρ = begin
  ⟦ subst w (a ∷ v) ⟧ᵛ ρ          ≡⟨⟩
  ⟦ (a ∙ᵛ w) +ᵛ v ⟧ᵛ ρ            ≈⟨ sound-plus (a ∙ᵛ w) v ρ ⟩
  ⟦ a ∙ᵛ w  ⟧ᵛ ρ ∪ ⟦ v ⟧ᵛ ρ       ≈⟨ union-congˡ (sound-scale a w ρ) ⟩
  ⟦ a ⟧ · ⟦ w  ⟧ᵛ ρ ∪ ⟦ v ⟧ᵛ ρ    ≡⟨⟩
  ⟦ a ∷ v ⟧ᵛ (⟦ w ⟧ᵛ ρ ∷ ρ)
  ∎ where
    open EqR (Bis _)
    v = b ∷ v'

-- parallel substitution is a kind of matrix multiplication
--
-- psubst (wₙ-1 ∷ ... ∷ w₀ ∷ []) (aₙ-1 ∷ ... ∷ a₀ ∷ [])
--   = aₙ-1 ∙ᵛ wₙ-1 +ᵛ ... +ᵛ a₀ ∙ᵛ w₀ +ᵛ 0ᵛ
psubst : ∀{n m} → Vec (LinComb n) m → LinComb m → LinComb n
psubst {n} M v = Vec.foldr (λ _ → LinComb n) (_+ᵛ_) (Vec.replicate _ 0ʳ)
  (Vec.zipWith (_∙ᵛ_) v M)

-- The semantics of m equations in n-1 variables:

⟦_⟧ᴹ : ∀{i n m} → Vec (LinComb n) m → Vec (Lang i) (pred n) → Vec (Lang i) m
⟦ M ⟧ᴹ ρ = Vec.map (λ v → ⟦ v ⟧ᵛ ρ) M

_≅⟨_⟩≅ᴸ_ : ∀{n} (L : Vec (Lang ∞) n) (i : Size) (L' : Vec (Lang ∞) n) → Set
L ≅⟨ i ⟩≅ᴸ L' = Vec.All (λ ll' → proj₁ ll' ≅⟨ i ⟩≅ proj₂ ll') (Vec.zip L L')

-- sound-psubst : ∀{i n m} (A : Vec (LinComb n) m) (v : LinComb m) (ρ : Vec (Lang ∞) (pred n)) →
--   ⟦ psubst A v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ v ⟧ᵛ (⟦ A ⟧ᴹ ρ)
-- sound-psubst A v ρ = {!!}

-- One step of the Gaussian algorithm.

-- We have m+1 equations in n+1 variables.
-- The first equation is the one we eliminate and return as "solved".

step : ∀{n m} → Vec (LinComb (2 + n)) (suc m) → Vec (LinComb (1 + n)) (suc m)
step ((r ∷ v) ∷ vs) = v' ∷ Vec.map (subst v') vs
  where
    v' = (r *ʳ) ∙ᵛ v

--   L = r·L + a  ==> L = r*·a    (if r ≠ ∅)
--   r*·a = r·r*·a + a

lemma : ∀{i n} r (v : Vec RE (suc n)) (ρ : Vec (Lang ∞) n) →
   ⟦ Vec.map ((r *ʳ) ∙ʳ_) v ⟧ᵛ ρ ≅⟨ i ⟩≅ ⟦ r ∷ v ⟧ᵛ (⟦ Vec.map ((r *ʳ) ∙ʳ_) v ⟧ᵛ ρ ∷ ρ)
-- lemma r (0ʳ ∷ []) ρ = ≅sym (≅trans (union-congˡ (≅trans (concat-emptyʳ _) (≅sym (concat-emptyˡ _)))) (union-concat-empty {l = ⟦ r* ⟧})) -- boring proof about ∅
--   where
--   r* : RE
--   r* = (r *ʳ)
lemma r (a ∷ []) ρ = star-concat _   -- Law for star
lemma {i} r (a ∷ b ∷ v') (l ∷ ρ) = begin
    ⟦ r* ∙ᵛ (a ∷ v) ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
    ⟦ (r* ∙ʳ a) ∷ r* ∙ᵛ v ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
     ⟦ r* ∙ʳ a ⟧ · l ∪ ⟦ r* ∙ᵛ v ⟧ᵛ ρ
  ≈⟨ {!!} ⟩
    ⟦ r ⟧ · (⟦ r* ∙ʳ a ⟧ · l ∪ ⟦ r* ∙ᵛ v ⟧ᵛ ρ) ∪ (⟦ a ⟧ · l ∪ ⟦ v ⟧ᵛ ρ)
  ≡⟨⟩
    ⟦ r ⟧ · ⟦ r* ∙ʳ a ∷ r* ∙ᵛ v ⟧ᵛ (l ∷ ρ) ∪ (⟦ a ⟧ · l ∪ ⟦ v ⟧ᵛ ρ)
  ≡⟨⟩
    ⟦ r ⟧ · ⟦ r* ∙ᵛ (a ∷ v) ⟧ᵛ (l ∷ ρ) ∪ ⟦ a ∷ v ⟧ᵛ (l ∷ ρ)
  ≡⟨⟩
    ⟦ r ∷ a ∷ v ⟧ᵛ (⟦ r* ∙ᵛ (a ∷ v) ⟧ᵛ (l ∷ ρ) ∷ l ∷ ρ)
  ∎
  where
  v : Vec RE _
  v = b ∷ v'
  r* : RE
  r* = (r *ʳ)
  open EqR (Bis _)


-- Lemma for sound-step
sound-step-lem : ∀{i n m} (v : Vec RE (suc n)) (M : Vec (LinComb (2 + n)) m) (ρ : Vec (Lang ∞) n)→
   Vec.All (λ ll' → proj₁ ll' ≅⟨ i  ⟩≅ proj₂ ll')
    (Vec.zipWith _,_
     (Vec.map (λ v₁ → ⟦ v₁ ⟧ᵛ ρ) (Vec.map (subst v) M)) --  Vec.map (λ v₁ → ⟦ subst v v₁ ⟧ᵛ ρ) M)
     (Vec.map (λ v₁ → ⟦ v₁ ⟧ᵛ (⟦ v ⟧ᵛ ρ ∷ ρ)) M))
sound-step-lem v []       ρ = []ᵃ
sound-step-lem v (w ∷ M') ρ = (sound-subst w v ρ) ∷ᵃ sound-step-lem v M' ρ

sound-step : ∀{i n m} (M : Vec (LinComb (2 + n)) (suc m)) (ρ : Vec (Lang ∞) n) →
  let M' = step M; l = ⟦ Vec.head M' ⟧ᵛ ρ
  in  ⟦ M' ⟧ᴹ ρ ≅⟨ i ⟩≅ᴸ ⟦ M ⟧ᴹ (l ∷ ρ)
  -- Vec (LinComb (1 + n)) (suc m)
-- sound-step {i} {n} ((0ʳ ∷ v) ∷ M) ρ =  {! ≅sym (sem-empty v (⟦ v ⟧ᵛ ρ ∷ ρ)) !} ∷ᵃ {! lem v M ρ !}
{-  where
  lem : ∀{i m} (M : Vec (LinComb (2 + n)) m) →
     Vec.All (λ ll' → proj₁ ll' ≅⟨ i  ⟩≅ proj₂ ll')
      (Vec.zipWith _,_
       (Vec.map (λ v₁ → ⟦ v₁ ⟧ᵛ ρ) (Vec.map (subst v) M))
       (Vec.map (λ v₁ → ⟦ v₁ ⟧ᵛ (⟦ v ⟧ᵛ ρ ∷ ρ)) M))
  lem [] = []ᵃ
  lem (w ∷ M') = (sound-subst w v ρ) ∷ᵃ lem M'  -- lem rewrite zipWith-map-map _,_ = {!!}
-}

sound-step ((r ∷ v) ∷ M) ρ = {!aux!} ∷ᵃ {!!}

-- -}

gauss : ∀{n}
   → Vec (LinComb (suc n)) (suc n)
  →  Vec (LinComb 1) (suc n)
gauss (w ∷ []) = w ∷ []
gauss (w ∷ (w₀ ∷ ws)) with step (w ∷ (w₀ ∷ ws))
... | w' ∷ ws' with gauss ws'
... | vs = psubst vs w' ∷ vs



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

eval : ∀{n} → LinComb n → Vec RE (pred n) → RE
eval [] _ = 0ʳ
eval (a ∷ []) _ = a
eval (a ∷ (b ∷ bs)) (r ∷ rs) = (a ∙ʳ r) +ʳ eval (b ∷ bs) rs

-- Evaluation is a morphism of vector spaces

eval-plus : ∀{n} (v w : LinComb n) (ρ  : Vec RE (pred n)) →
  eval (v +ᵛ w) ρ ≅ʳ (eval v ρ +ʳ eval w ρ)
eval-plus [] [] _ =  ≅sym union-emptyˡ
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
