module NumberFin where

open import Agda.Builtin.FromNat using (Number)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)

data IsTrue : Bool → Set where
  itis : IsTrue true

instance
  indeed : IsTrue true
  indeed = itis

_<?_ : ℕ → ℕ → Bool
zero <? zero = false
zero <? suc y = true
suc x <? zero = false
suc x <? suc y = x <? y

natToFin : ∀ {n} (m : ℕ) {{_ : IsTrue (m <? n)}} → Fin n
natToFin {zero} zero {{()}}
natToFin {zero} (suc m) {{()}}
natToFin {suc n} zero {{itis}} = zero
natToFin {suc n} (suc m) {{t}} = suc (natToFin m)

instance
  NumFin : ∀ {n} → Number (Fin n)
  Number.Constraint (NumFin {n}) k = IsTrue (k <? n)
  Number.fromNat    NumFin       k = natToFin k
