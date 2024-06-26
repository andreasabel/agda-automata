
\AgdaHide{
\begin{code}

{-# OPTIONS --sized-types #-}

open import Relation.Binary.PropositionalEquality

\end{code}
}

\newcommand{\arewrite}{
\begin{code}

rewriteExample : {A : Set} {P : A → Set} {x : A} (p : P x)
  {g : A → A} (e : g x ≡ x) → P (g x)
rewriteExample p e rewrite e = p

\end{code}
}
