
\AgdaHide{
\begin{code}

{-# OPTIONS --sized-types #-}

open import Size

\end{code}
}
\newcommand{\abool}{
\begin{code}

data Bool : Set where
  true   :  Bool
  false  :  Bool

\end{code}
}
\newcommand{\anot}{
\begin{code}

not : Bool → Bool
not true   =  false
not false  =  true

\end{code}
}
\newcommand{\avee}{
\begin{code}

_∨_ : (a b : Bool) → Bool
true   ∨  b  =  true
false  ∨  b  =  b

\end{code}
}
\newcommand{\aapplyWhen}{
\begin{code}

applyWhen : {A : Set} → Bool → (A → A) → A → A
applyWhen  true   f  a  =  f a
applyWhen  false  _  a  =  a

\end{code}
}
\newcommand{\amaybe}{
\begin{code}

data Maybe (A : Set) : Set where
  just     :  A → Maybe A
  nothing  :  Maybe A

\end{code}
}
\newcommand{\alist}{
\begin{code}

data List (i : Size) (A : Set) : Set where
  []   :  List i A
  _∷_  :  {j : Size< i} (x : A) (xs : List j A) → List i A

\end{code}
}
\newcommand{\amap}{
\begin{code}

map : ∀{i A B} → (A → B) → List i A → List i B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

\end{code}
}
\newcommand{\afoldr}{
\begin{code}

foldr : ∀{i} {A B : Set} → (A → B → B) → B → List i A → B
foldr c n []        =  n
foldr c n (x ∷ xs)  =  c x (foldr c n xs)

\end{code}
}
\newcommand{\aor}{
\begin{code}

or : List ∞ Bool → Bool
or = foldr _∨_ false

\end{code}
}
\newcommand{\aany}{
\begin{code}

any : ∀{i A} → (A → Bool) → List i A → Bool
any p xs = foldr _∨_ false (map p xs)

\end{code}
}
\newcommand{\aprod}{
\begin{code}

record _×_ (A B : Set) : Set where
  constructor _,_
  field  fst  :  A
         snd  :  B

\end{code}
}
\AgdaHide{
\begin{code}
open _×_
\end{code}
}
\newcommand{\aswap}{
\begin{code}

swap : ∀{A B} → A × B → B × A
fst  (swap p)  =  snd  p
snd  (swap p)  =  fst  p

\end{code}
}
\newcommand{\abot}{
\begin{code}

data ⊥ : Set where

⊥-elim : {A : Set} (p : ⊥) → A
⊥-elim ()

\end{code}
}
\newcommand{\atriv}{
\begin{code}

record ⊤ : Set where

triv : ⊤
triv = record {}

\end{code}
}
\newcommand{\aeq}{
\begin{code}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

\end{code}
}
\newcommand{\aeqsym}{
\begin{code}

sym : ∀{A} {x y : A} → x ≡ y → y ≡ x
sym {A} {x} {.x} refl = refl

\end{code}
}
\newcommand{\aeqtrans}{
\begin{code}

trans : ∀{A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

\end{code}
}
\newcommand{\aAnyInf}{
\begin{code}

data AnyS (i : Size) {A} (P : A → Set) : List i A → Set where
  here   :  ∀{j : Size< i} {x} {xs : List j A} (p : P x)          →  AnyS i P (x ∷ xs)
  there  :  ∀{j : Size< i} {x} {xs : List j A} (p : AnyS j P xs)  →  AnyS i P (x ∷ xs)

\end{code}
}

\newcommand{\aAny}{
\begin{code}

data Any (i : Size) {A} (P : A → Set) : List ∞ A → Set where
  here   :  ∀{x xs}                 (p : P x)         →  Any i P (x ∷ xs)
  there  :  ∀{x xs}  {j : Size< i}  (p : Any j P xs)  →  Any i P (x ∷ xs)

\end{code}
}

\newcommand{\aDec}{
\begin{code}

data Dec (P : Set) : Set where
  yes  :  ( p  :  P )     →  Dec P
  no   :  (¬p  :  P → ⊥)  →  Dec P

⌊_⌋ : ∀{P} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false
\end{code}
}
\newcommand{\aanyany}{
\begin{code}

True : Bool → Set
True true   =  ⊤
True false  =  ⊥

-- any-Any : ∀{i A} (p : A → Bool) (xs : List i A)
--   →  True (any p xs)
--   →  Any i (λ x → True (p x)) xs
-- any-Any {i} p [] ()
-- any-Any {i} p (x ∷ xs) q with p x | here {i = i} {P = λ x → True (p x)} {x = x} {xs = xs}
-- any-Any {i} p (x ∷ xs) q | true   | h = h _
-- any-Any {i} p (x ∷ xs) q | false  | h = there (any-Any p xs q)

any-Any : ∀{i A} {P : A → Set} (p : (a : A) → Dec (P a)) (xs : List i A)
  →  True (any (λ x → ⌊ p x ⌋) xs)
  →  AnyS i P xs
any-Any p [] ()
any-Any p (x ∷ xs) q with p x
any-Any p (x ∷ xs) q | yes r  =  here r
any-Any p (x ∷ xs) q | no _   =  there (any-Any p xs q)

\end{code}
}
\newcommand{\awith}{
\begin{code}

withExample : (P : Bool → Set) (p : P true) (q : P false) →
  {A : Set} (g : A → Bool) (x : A) → P (g x)
withExample P p q g x with g x
... | true   =  p
... | false  =  q

\end{code}
}
\AgdaHide{
\begin{code}

\end{code}
}
