-- {-# OPTIONS --show-implicit #-}

module _ where

open import Size

open import Data.Unit using (⊤)
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Sum

open import Relation.Binary.PropositionalEquality

open Deprecated-inspect renaming (inspect to d-inspect)

-- Monads
----------------------------------------------------------------------

record Monad (M : Set → Set) : Set₁ where
  field  <_>return  : ∀{A}   (v : A)                  → M A
         <_>bind    : ∀{A B} (m : M A) (k : A → M B)  → M B

open Monad {{...}} using () renaming (<_>return to return; <_>bind to _>>=_)
open Monad

_<_>>=_ : ∀{M A B} (m : M A) (d : Monad M) (k : A → M B) → M B
m < d >>= k = < d >bind m k

-- Possibly ending streams: "Burroni colists".
----------------------------------------------------------------------

mutual

  record BC i X E : Set where
    coinductive
    constructor delay
    field force : ∀{j : Size< i} → BC' j X E

  data BC' i X E : Set where
    end : (e : E)                  → BC' i X E
    _∷'_ : (x : X) (xs : BC i X E)  → BC' i X E

module _ where

  -- Cons in BC.

  _∷_ : ∀{i X E} (x : X) (xs : BC i X E) → BC (↑ i) X E
  BC.force (x ∷ xs) = x ∷' xs

  -- Cons in BC'

  _∷''_ : ∀{i X E} (x : X) (xs : BC' i X E) → BC' (↑ i) X E
  x ∷'' xs =  x ∷' delay xs

-- Burroni colists form a monad.

-- Return.

  returnBC : ∀{i X E} (e : E) → BC i X E
  BC.force (returnBC e) = end e

-- Bind.

mutual

  _>>=BC_  : ∀{i X D E}
           → (m : BC i X D)
           → (k : D → BC i X E)
           → BC i X E

  BC.force (m >>=BC k) = BC.force m >>=BC' k

  _>>=BC'_ : ∀{i X D E}{j : Size< i}
           → (m : BC' j X D)
           → (k : D → BC i X E)
           → BC' j X E

  end e    >>=BC' k = BC.force (k e)
  (x ∷' xs) >>=BC' k = x ∷' (xs >>=BC k)

-- Monad instance.

instance

  monadBC : ∀{i X} → Monad (BC i X)
  <_>return  monadBC v    = returnBC v
  <_>bind    monadBC m k  = m >>=BC k


-- Property holding everywhere on a Stream

module _ {X E : Set} (P : X → Set) (PE : E → Set) where

  mutual

    record All i (s : BC ∞ X E) : Set where
      coinductive
      constructor delay
      field force : ∀{j : Size< i} → All' j (BC.force s)

    data All' i : (s : BC' ∞ X E) → Set where
      endᵃ  :  ∀{e}     (p : PE e)                 →  All' i (end e)
      _∷'_  :  ∀{x xs}  (p : P x) (ps : All i xs)  →  All' i (x ∷' xs)

module _ {X E : Set} {P : X → Set} {PE : E → Set} where

    _∷ᵃ_  :  ∀{i x xs}  (p : P x) (ps : All P PE i xs)  →  All P PE (↑ i) (x ∷ xs)
    All.force (p ∷ᵃ ps) = p ∷' ps

    _∷ᵃ'_  :  ∀{i x xs}  (p : P x) (ps : All' P PE i xs)  →  All' P PE (↑ i) (x ∷'' xs)
    p ∷ᵃ' ps = p ∷' (All.delay ps)

-- IO Processes
----------------------------------------------------------------------

module IO-type (I O : Set) where

  mutual

    record IO i A : Set where
      coinductive
      constructor delay
      field force : ∀{j : Size< i} → IO' j A

    data IO' j A : Set where
      get' : (f : (i : I) → IO' j A)  → IO' j A
      put' : (o : O) (p : IO j A)      → IO' j A
      ret' : (v : A)                   → IO' j A

  open IO public

-- IO Processes form a monad

module IO-ops {I O : Set} where
  open IO-type hiding (IO; IO')
  private
    IO  = IO-type.IO  I O
    IO' = IO-type.IO' I O

  -- Return.

  returnIO : ∀{i A} (v : A) → IO i A
  force (returnIO v) = ret' v

  -- Bind.

  _>>=IO_  : ∀{i A B}              (m : IO  i A) (k : A → IO i B) → IO  i B
  _>>=IO'_ : ∀{i A B}{j : Size< i} (m : IO' j A) (k : A → IO i B) → IO' j B

  force (m >>=IO k) = force m >>=IO' k

  get' f   >>=IO' k = get' λ i → f i >>=IO' k
  put' o p >>=IO' k = put' o (p >>=IO k)
  ret' v   >>=IO' k = force (k v)

  -- Monad instance.

  instance

    monadIO : ∀{i} → Monad (IO i)
    < monadIO >return v = returnIO v
    < monadIO >bind m k = m >>=IO k

  -- Operations in IO.

  get : ∀{j A} (f : (i : I) → IO j A) → IO j A
  force (get f) = get' λ i → force (f i)

  put : ∀{j A} (o : O) (p : IO j A) → IO j A
  force (put o p) = put' o p

  -- Running an IO process.

  -- We might output an infinite stream,
  -- or a stream terminated by the process result,
  -- or a stream terminated by the end of the input stream.

  runIO     : ∀{i A E}              (p : IO  i A)      (s : BC  ∞ I E) → BC  i O (E ⊎ A)
  runIO'    : ∀{i A E}{j : Size< i} (p : IO' j A)      (s : BC  ∞ I E) → BC' j O (E ⊎ A)

  BC.force (runIO p s) = runIO' (force p) s

  runIO' (get' f)    s with BC.force s
  runIO' (get' f)    s | end e   = end (inj₁ e)
  runIO' (get' f)    s | x ∷' xs = runIO' (f x) xs
  runIO' (put' o p)  s           = o ∷' runIO p s
  runIO' (ret' v)    s           = end (inj₂ v)

-- TODO:

-- process that multiplies a stream
-- terminates early on 0
-- terminates on end

open IO-type
open IO-ops

module Scanl {A : Set} (_*_ : A → A → A) (zero? : A → Bool) where

  -- Process, given an initial A, reading As, writing As, returning an A

  proc1 : ∀{i} (a : A) → IO A A i A
  force (proc1 a) with zero? a
  ... | true  = ret' a
  ... | false = put' a (get λ b → proc1 (a * b))

  proc : ∀{i} → IO A A i A
  force proc = get' λ a → force (proc1 a)

  -- Proof: output is zero-free, result (if any) is zero.

  -- IsZero : (a : A) → Set
  -- IsZero a = zero? a ≡ true

  -- NotZero : (a : A) → Set
  -- NotZero a = zero? a ≡ false

  module _ {E : Set} where

    private
      P  : ∀ i → BC ∞ A (E ⊎ A) → Set
      P  = All (λ a → zero? a ≡ false)
             [ (λ e → ⊤)
             , (λ a → zero? a ≡ true) ]

    -- Lemma for proc1.

    zero-free1     : ∀{i} a s → P i (runIO (proc1 a) s)
    zero-free1-get : ∀{i} a s → P i (runIO (get λ b → proc1 (a * b)) s)

    All.force (zero-free1 a s)      with zero? a | inspect zero? a
    ... | true  | [ iz ] = endᵃ iz
    ... | false | [ nz ] = nz ∷' zero-free1-get a s

    All.force (zero-free1-get a s)  with BC.force s {∞}
    ... | end e          = endᵃ _
    ... | x ∷' xs        = All.force (zero-free1 (a * x) xs)

    -- Theorem for proc.

    zero-free : ∀{i} s → P i (runIO proc s)
    All.force (zero-free s) with BC.force s {∞}
    All.force (zero-free s) | end e = endᵃ _
    All.force (zero-free s) | x ∷' xs = All.force (zero-free1 x xs)


-- abstraction, does the same on the parity
-- show simulation
