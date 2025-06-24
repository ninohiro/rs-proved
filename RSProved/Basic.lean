-- Implementation of Reed-Solomon coding

import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Defs

open Matrix

namespace ReedSolomon

structure RSCode (F : Type*) [Field F] where
  k        : ℕ
  n        : ℕ
  h_kn     : k ≤ n
  α        : Fin n → F
  distinct : Function.Injective α

variable {F : Type*} [Field F] (Code : RSCode F)

def M : Matrix (Fin Code.n) (Fin Code.n) F :=
  fun i j => (Code.α j) ^ i.val

def encode (m : Fin Code.k → F) : Fin Code.n → F :=
  let f (x : Fin Code.n) :=
    if h : x.val < Code.k then
      m ⟨x.val, h⟩
    else
      0
  (M Code) *ᵥ f

end ReedSolomon
