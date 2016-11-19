{-# OPTIONS --allow-unsolved-metas #-}

module ColoredTrie where

open import Library
open import Trie

-- Reverse word lookup
δs : ∀{A B} (t : Trie ∞ A B) (as : List A) → Trie ∞ A B
δs t [] = t
δs t (a ∷ as) = δ (δs t as) a
-- δs t (a ∷ as) = δs (δ t a) as

δs-++ : ∀{i A B} (t : Trie ∞ A B) as bs → δs (δs t as) bs ≅⟨ i ⟩≅ δs t (bs ++ as)
δs-++ t as []       = ≅refl
δs-++ t as (b ∷ bs) = ≅δ (δs-++ t as bs) b

-- An index f to a Trie exhibits for each B
-- a subtree with that root label.
Index : ∀{A B} (f : B → List A) → Trie ∞ A B → Set
Index f t = ∀ b → ν (δs t (f b)) ≡ b

record Aut (A B S : Set) : Set where
  field
    ν : (s : S) → B
    δ : (s : S) (a : A) → S
open Aut

lang : ∀{i A B S} (da : Aut A B S) (s : S) → Trie i A B
ν (lang aut s)   = ν aut s
δ (lang aut s) a = lang aut (δ aut s a)

aut : ∀{A B} (t : Trie ∞ A B) (f : B → List A) → Aut A B B
ν (aut t f) s   = s -- ν (δs t (f s))
δ (aut t f) s a = ν (δ (δs t (f s)) a)

-- Root determines tree
RootDet : ∀{A B} (t₁ t₂ : Trie ∞ A B) → Set
RootDet t₁ t₂ = ν t₁ ≡ ν t₂ → t₁ ≅ t₂

-- Coherently colored: nodes with same labels span same subtree
Coh : ∀{A B} (t : Trie ∞ A B) → Set
Coh t = ∀ as bs → RootDet (δs t as) (δs t bs)

coh-δ : ∀{A B} (t : Trie ∞ A B) → Coh t → ∀ cs → Coh (δs t cs)
coh-δ t coh cs as bs = {!coh (as ++ cs) (bs ++ cs) !} -- Need RootDet closed under bisim
-- ≅ν (coh-δ t coh cs as bs eq) = eq
-- ≅δ (coh-δ t coh cs as bs eq) a = {!coh!}

-- CorrAut' :
--   ∀{i A B} (t : Trie ∞ A B) (coh : Coh t) (f : B → List A) (ind : Index f t)
--   → ∀ as → let t' = δs t as; b = ν t' in t' ≅⟨ i ⟩≅ lang (aut t f) b
-- ≅ν (CorrAut' t coh f ind as) = refl
-- ≅δ (CorrAut' t coh f ind as) a -- rewrite ind b
--   = ≅trans (CorrAut' t coh f ind (a ∷ as)) {!coh ? ? ?!}
-- --   = {!CorrAut t coh f ind (ν (δ (δs t (f b)) a))!}

module _ {A B} (t : Trie ∞ A B) (coh : Coh t) (f : B → List A) (ind : Index f t) where

  fact :  ∀{i} as → let t' = (δs t as) in δs t (f (ν t')) ≅⟨ i ⟩≅ t'
  ≅ν (fact as) = ind (ν (δs t as))
  ≅δ (fact as) a = {! coh-δ t coh (a ∷ []) {! (f (ν (δs t as))) !} as {!ind !} !}
-- coh (a ∷ f (ν (δs t as))) (a ∷ as) {!ind !}

  -- Fact: The subtrie indicated by f (ν t) is bisimilar to the whole tree t
  -- (Thus, w.l.o.g. f (ν t) ≡ [])
  start : ∀{i} → δs t (f (ν t)) ≅⟨ i ⟩≅ t
  ≅ν start = ind (ν t)
  ≅δ start a = coh (a ∷ f (ν t)) (a ∷ []) {!ind (ν (δ t a))!}

  -- Theorem: Infinite Myhill-Nerode
  --
  -- Given
  --   * a coherently colored trie t and
  --   * for each color b a path (f b) to a subtree δs t (f b) of that color
  -- then the automata constructed from the nodes indicated by f
  -- recognizes language t.

  CorrAut : ∀{i} b → δs t (f b) ≅⟨ i ⟩≅ lang (aut t f) b

  ≅ν (CorrAut b) = ind b

  ≅δ (CorrAut b) a = begin

      δ (δs t (f b)) a          ≡⟨⟩
      δs t (a ∷ f b)            ≈⟨ coh (a ∷ f b) (f b') root-eq   ⟩
      δs t (f b')               ≈⟨ CorrAut b' ⟩
      lang (aut t f) b'         ≡⟨⟩
      δ (lang (aut t f) b) a     ∎

    where
    b' = ν (δ (δs t (f b)) a)
    root-eq : ν (δs t (a ∷ f b)) ≡ ν (δs t (f b'))
    root-eq = sym (ind b')
    open EqR (Bis _ _ _)

  -- {! ≅trans (coh (a ∷ f b) ((f b')) (sym (ind b')))
  --        (CorrAut t coh f ind b') !}

data Label (Y N : Set) : Set where
  yes : Y → Label Y N
  no  : N → Label Y N

∅ : ∀{i A Y N} (n : N) → Trie i A (Label Y N)
ν (∅ n)   = no n
δ (∅ n) a = ∅ n

ε : ∀{i A Y N} (y : Y) (n : N) → Trie i A (Label Y N)
ν (ε y n)   = yes y
δ (ε y n) a = ∅ n

data Three Y Y' N N' : Set where
  yn : Y → N' → Three Y Y' N N'
  ny : N → Y' → Three Y Y' N N'
  nn : N → N' → Three Y Y' N N'

_⊓_ : ∀{Y N Y' N'} (b : Label Y N) (c : Label Y' N') →
  Label (Y × Y') (Three Y Y' N N')
yes y ⊓ yes y' = yes (y , y')
yes y ⊓ no  n' = no (yn y n')
no  n ⊓ yes y' = no (ny n y')
no  n ⊓ no  n' = no (nn n n')

_∩_ : ∀{i A Y N Y' N'} (t : Trie i A (Label Y N)) (u : Trie i A (Label Y' N')) →
  Trie i A (Label (Y × Y') (Three Y Y' N N'))
t ∩ u = zipWith _⊓_ t u
-- ν (t ∩ u) = ν t ⊓ ν u
-- δ (t ∩ u) a = δ t a ∩ δ u a

_⊔_ : ∀{Y N Y' N'} (b : Label Y N) (c : Label Y' N') →
  Label (Three N N' Y Y') (N × N')
yes y ⊔ yes y' = yes (nn y y')
yes y ⊔ no  n' = yes (ny y n')
no  n ⊔ yes y' = yes (yn n y')
no  n ⊔ no  n' = no  (n , n')

_∪_ : ∀{i A Y N Y' N'} (t : Trie i A (Label Y N)) (u : Trie i A (Label Y' N')) →
  Trie i A (Label (Three N N' Y Y') (N × N'))
t ∪ u = zipWith _⊔_ t u
