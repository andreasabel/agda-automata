-- Weak Greibach normal form of context-free grammars

{-# OPTIONS --allow-unsolved-metas #-}

open import Library

module WeakGreibach
  (decA : DecSetoid lzero lzero)
  (open DecSetoid decA using (_≟_) renaming (Carrier to A))
  (NT : Set)
  (start : NT)
  where

import Language
open import Automaton decA

data Letter : Set where
  ter : (a : A)  → Letter
  nt  : (X : NT) → Letter

-- Sentence form
-- the empty list means empty word

Form = List Letter

record LangF (S : Set) : Set where
  field  ν : Bool
         δ : A → S

-- Context free grammar in weak Greibach Normal Form

CFG = NT → LangF (Maybe (List Form))
  -- the empty list means the empty word
  -- nothing means cannot step

-- State of a recognizing automaton
-- empty list is error state

St = List Form

-- Automaton construction

module WGA (G : CFG) where

  -- is a letter nullable?
  nullLetter : Letter → Bool
  nullLetter (ter _) = false
  nullLetter (nt  X) = LangF.ν (G X)

  -- is a sentence form nullable?
  nullForm : Form → Bool
  nullForm = List.all nullLetter

  stepLetter : Letter → A → Maybe St
  stepLetter (ter a) x = if ⌊ a ≟ x ⌋ then just [] else nothing
  stepLetter (nt X)    = LangF.δ (G X)

  stepForm : Form → A → Maybe St
  stepForm []       a = nothing
  stepForm (x ∷ xs) a = Maybe.map (List.map (_++ xs)) (stepLetter x a)

  stepSt : St → A → St
  stepSt xss a = List.concat (List.catMaybes (List.map (λ xs → stepForm xs a) xss))

  aut : DAut St
  DAut.ν aut = List.any nullForm
  DAut.δ aut s a = {!List.catMaybes (List.map (λ xs → stepForm xs a) s)!}
