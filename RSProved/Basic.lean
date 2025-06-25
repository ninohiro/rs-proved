-- Implementation of Reed-Solomon coding

import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Defs
import Mathlib.LinearAlgebra.Vandermonde
import RSProved.GaussianElimination

open Matrix

namespace ReedSolomon

structure RSCode (F : Type*) [Field F] [DecidableEq F] where
  k        : ℕ
  n        : ℕ
  h_kn     : k ≤ n
  α        : Fin n → F
  distinct : Function.Injective α

namespace RSCode
variable {F : Type*} [Field F] [DecidableEq F] (Code : RSCode F)

def M : Matrix (Fin Code.n) (Fin Code.n) F :=
  Matrix.vandermonde Code.α

def MInv : Matrix (Fin Code.n) (Fin Code.n) F :=
  let (Y, _, _) := toReducedRowEchelonForm Code.M
  Y

def encode (m : Fin Code.k → F) : Fin Code.n → F :=
  let f (x : Fin Code.n) :=
    if h : x.val < Code.k then
      m ⟨x.val, h⟩
    else
      0
  Code.M *ᵥ f

def decode (w : Fin Code.n → F) : Fin Code.k → F :=
  fun x : Fin Code.k => (Code.MInv *ᵥ w) ⟨x.1, by linarith [Code.h_kn, x.2]⟩

end RSCode

end ReedSolomon
