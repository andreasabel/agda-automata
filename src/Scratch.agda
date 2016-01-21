module _ where

open import Size
open import Data.Sum

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
    eof : (e : E)                  → BC' i X E
    _∷_ : (x : X) (xs : BC i X E)  → BC' i X E

-- Burroni colists form a monad.

-- Return.

  returnBC : ∀{i X E} (e : E) → BC i X E
  BC.force (returnBC e) = eof e

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

  eof e    >>=BC' k = BC.force (k e)
  (x ∷ xs) >>=BC' k = x ∷ (xs >>=BC k)

-- Monad instance.

instance

  monadBC : ∀{i X} → Monad (BC i X)
  <_>return  monadBC v    = returnBC v
  <_>bind    monadBC m k  = m >>=BC k


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

  -- Running an IO process.

  -- We might output an infinite stream,
  -- or a stream terminated by the process result,
  -- or a stream terminated by the eof of the input stream.

  runIO  : ∀{i A E}              (p : IO  i A) (s : BC ∞ I E) → BC  i O (E ⊎ A)
  runIO' : ∀{i A E}{j : Size< i} (p : IO' j A) (s : BC ∞ I E) → BC' j O (E ⊎ A)

  BC.force (runIO p s)          = runIO' (force p) s

  runIO' (get' f)    s with BC.force s
  runIO' (get' f)    s | eof e  = eof (inj₁ e)
  runIO' (get' f)    s | x ∷ xs = runIO' (f x) xs
  runIO' (put' o p)  s          = o ∷ runIO p s
  runIO' (ret' v)    s          = eof (inj₂ v)


-- TODO:

-- process that multiplies a stream
-- terminates early on 0
-- terminates on eof

-- abstraction, does the same on the parity
-- show simulation
