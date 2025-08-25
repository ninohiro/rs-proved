-- Implementation of Reed-Solomon coding

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots

open Matrix Polynomial

namespace ReedSolomon

structure RSCode (F : Type*) [Field F] [DecidableEq F] where
  k        : ℕ
  n        : ℕ
  h_k_gt   : k > 0
  h_kn     : k ≤ n
  α        : Fin n → F
  distinct : Function.Injective α

namespace RSCode
variable {F : Type*} [Field F] [DecidableEq F] (Code : RSCode F)

def M : Matrix (Fin Code.n) (Fin Code.n) F :=
  Matrix.vandermonde Code.α

def MInv : Matrix (Fin Code.n) (Fin Code.n) F := (Code.M.det)⁻¹ • Code.M.adjugate

def encode (m : Fin Code.k → F) : Fin Code.n → F :=
  (Code.M.submatrix id (Fin.castLE Code.h_kn)) *ᵥ m

noncomputable def encodePoly (m : Fin Code.k → F) : F[X] :=
  ∑ i, (C (m i)) * X ^ i.val

theorem encode_eq_poly (m : Fin Code.k → F) (i : Fin Code.n) :
    Code.encode m i = (Code.encodePoly m).eval (Code.α i) := by
  simp [encode, encodePoly, mulVec, dotProduct, Polynomial.eval_finset_sum]
  have h₀ x : Code.M i (Fin.castLE Code.h_kn x) * m x = m x * Code.α i ^ x.val := by
    simp [M, vandermonde]
    ring_nf
  simp [h₀]

def decode (w : Fin Code.n → F) : Option ((Fin Code.k) → F) :=
  let b := Code.MInv *ᵥ w
  let synd : Fin (Code.n - Code.k) → F := fun x =>
    b ⟨Code.k + x.val, by simp [← Nat.lt_sub_iff_add_lt']⟩
  if synd = 0 then
    some (b ∘ (Fin.castLE Code.h_kn))
  else
    none

theorem least_hammingDist (m m' : Fin Code.k → F) (h_m_ne_m' : m ≠ m'):
    hammingDist (Code.encode m) (Code.encode m') > (Code.n - Code.k) := by
  simp [← Nat.add_one_le_iff]
  let k := Code.k - 1
  have h_k_add_one : k + 1 = Code.k := by
    simp [k, Nat.sub_one_add_one (Nat.ne_of_gt Code.h_k_gt)]
  rw [← Nat.sub_add_comm Code.h_kn, ← h_k_add_one]
  rw (occs := [2]) [Nat.add_comm]
  simp [Nat.sub_add_eq]

  simp [hammingDist]
  have h₀ := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
    (fun i : Fin Code.n => Code.encode m i = Code.encode m' i)
  simp at h₀
  simp [← h₀, add_comm, encode_eq_poly, ← sub_eq_zero]
  simp [← eval_sub]
  let p := Code.encodePoly m - Code.encodePoly m'
  have h_p_ne_zero : p ≠ 0 := by
    unfold p encodePoly
    simp [← Finset.sum_sub_distrib, ← sub_mul]
    intro h
    have h₁ (i : Fin Code.k) : (∑ x, (C (m x) - C (m' x)) * X ^ x.val).coeff i.val = 0 := by
      simp [h]
    simp at h₁
    have h₂ (i : Fin Code.k) (b : Fin Code.k) :
        ((C (m b) - C (m' b)) * X ^ b.val).coeff i.val = (if b = i then m i - m' i else 0) := by
        rw [← C_sub, coeff_C_mul, coeff_X_pow]
        by_cases h₄ : b = i
        .
          simp [h₄]
        .
          simp [h₄]
          intro h₅
          have h₆ : i = b := by
            ext
            exact h₅
          rw [h₆] at h₄
          contradiction
    simp [h₂] at h₁
    have h₃ : m = m' := by
      ext i
      exact sub_eq_zero.1 (h₁ i)
    exact h_m_ne_m' h₃

  have h_p_deg : p.natDegree ≤ k := by
    unfold p encodePoly
    simp [← Finset.sum_sub_distrib, ← sub_mul]
    let f (b : Fin Code.k) := (C (m b) - C (m' b)) * X ^ b.val
    have h₁ (i : Fin Code.k) (_ : i ∈ Finset.univ) : (f i).natDegree ≤ k := by
      unfold f
      rw [← C_sub]
      by_cases h₂ : m i - m' i = 0
      .
        simp [h₂]
      .
        rw [natDegree_C_mul_X_pow (ha := h₂)]
        linarith [i.2]
    exact Polynomial.natDegree_sum_le_of_forall_le (Finset.univ) f h₁
  change Finset.card {i | p.IsRoot (Code.α i)} ≤ k
  rw [← (Finset.card_image_of_injective · Code.distinct)]
  have h₁ : Finset.image Code.α {i | p.IsRoot (Code.α i)} ⊆ p.roots.toFinset := by
    simp [Finset.subset_def, Multiset.subset_iff, h_p_ne_zero]
  linarith [Finset.card_le_card h₁, Multiset.toFinset_card_le p.roots, p.card_roots', h_p_deg]

end RSCode

end ReedSolomon

def SampleRS : ReedSolomon.RSCode ℚ := {
  k := 2
  n := 4
  h_k_gt := by simp
  h_kn := by simp
  α := fun x => x.val
  distinct := by
    simp [Function.Injective]
    intro a b h
    ext
    exact h
}

#guard SampleRS.decode (SampleRS.encode (![1,2])) = some ![1,2]
