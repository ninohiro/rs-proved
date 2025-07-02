-- Implementation of gaussian elimination

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic


open Option Matrix

namespace Matrix
theorem submatrix_mul_row {α l m n o : Type*} (A : Matrix l m α) (B : Matrix m n α)
    [Fintype m] [Mul α] [AddCommMonoid α] (r_reindex : o → l) :
    (A.submatrix r_reindex id) * B = (A * B).submatrix r_reindex id := by
  ext i j
  simp [instHMulOfFintypeOfMulOfAddCommMonoid]

theorem submatrix_mul_col {α l m n o : Type*} (A : Matrix l m α) (B : Matrix m n α)
    [Fintype m] [Mul α] [AddCommMonoid α] (c_reindex : o → n) :
    A * (B.submatrix id c_reindex) = (A * B).submatrix id c_reindex := by
  ext i j
  simp [instHMulOfFintypeOfMulOfAddCommMonoid]

theorem submatrix_row_col {α l m n o : Type*} (A : Matrix m n α)
    (r_reindex : l → m) (c_reindex : o → n) :
    A.submatrix r_reindex c_reindex = (A.submatrix r_reindex id).submatrix id c_reindex := by simp

variable {K : Type*} [Field K] [DecidableEq K]
variable {m n : ℕ}

def T (i : Fin m) (f : Fin m → K) : Matrix (Fin m) (Fin m) K
  := (fun k l => if l = i then if k ≠ l then f k else 0 else 0)

omit [DecidableEq K] in
lemma T_pow_two (i : Fin m) (f : Fin m → K) : (T i f) * (T i f) = 0 := by
  change (fun M N i k => (fun j => M i j) ⬝ᵥ fun j => N j k) (T i f) (T i f) = 0
  unfold dotProduct T
  ext k l
  simp
  intro h
  have h₀ x : (if x = l then 0 else if x = i then if k = x then 0 else f k * f x else 0) = 0 := by
    split_ifs with h₁ h₂ h₃ <;> try rfl
    rw [h, h₂] at h₁
    contradiction
  simp [h₀]

section
variable (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n)

def diagonalUnit (f : Fin m → Kˣ) : (Matrix (Fin m) (Fin m) K)ˣ :=
  ⟨
    diagonal (fun x => (f x).val),
    diagonal (fun x => (f x).inv),
    by simp,
    by simp
  ⟩

def ReduceRow : (Matrix (Fin m) (Fin m) K)ˣ :=
  if h : A i j = 0 then 1 else
    let AUnit : Kˣ := ⟨(A i j)⁻¹, A i j, by simp [h], by simp [h]⟩
    diagonalUnit (fun x =>
      if x = i then AUnit else 1)

theorem reduce_row (h : A i j ≠ 0) : ((ReduceRow A i j).val * A) i j = 1 := by
  change (fun M N i k => (fun j => M i j) ⬝ᵥ fun j => N j k) (ReduceRow A i j).val A i j = 1
  simp [dotProduct, ReduceRow, h, diagonalUnit, diagonal]

def elim : (Matrix (Fin m) (Fin m) K)ˣ :=
  let U := T i (fun x : Fin m => - A x j / A i j)
  ⟨
    1 + U,
    1 + - U,
    by
      rw [add_mul, mul_add, mul_add]
      simp [add_assoc]
      exact T_pow_two i (fun x : Fin m => - A x j / A i j)
    ,
    by
      rw [add_mul, mul_add, mul_add]
      simp [add_assoc]
      exact T_pow_two i (fun x : Fin m => - A x j / A i j)
  ⟩

def swapUnit (i₁ : Fin m) (i₂ : Fin m) : (Matrix (Fin m) (Fin m) K)ˣ :=
  ⟨
    swap K i₁ i₂,
    swap K i₁ i₂,
    by simp [swap_mul_self],
    by simp [swap_mul_self]
  ⟩

def elimSwapReduce (k_fin : Fin m) : (Matrix (Fin m) (Fin m) K)ˣ :=
  let C := (swapUnit i k_fin) * (ReduceRow A i j)
  (elim (C.val * A) k_fin j) * C

omit [DecidableEq K] in
theorem elim_eq (h : A i j ≠ 0) :
    ((elim A i j).val * A).col j = (fun x => if x = i then A i j else 0) := by
  ext x
  simp [elim, Matrix.add_mul]
  change A x j + (fun M N i k => (fun j => M i j) ⬝ᵥ fun j => N j k)
      (T i fun x ↦ -A x j / A i j) A x j = if x = i then A i j else 0
  simp [dotProduct, elim, T]
  split_ifs with h₀ <;> simp [h₀, h]

theorem elim_swap_reduce_eq (k_fin : Fin m) (h : A i j ≠ 0):
    ((elimSwapReduce A i j k_fin).val * A).col j = (fun x => if x = k_fin then 1 else 0) := by
  simp [elimSwapReduce]
  let C := (swapUnit i k_fin) * (ReduceRow A i j)
  change ((elim (C.val * A) k_fin j).val * C.val * A).col j = (fun x => if x = k_fin then 1 else 0)
  rw [Matrix.mul_assoc]
  have h₀ : (C.val * A) k_fin j = 1 := by
    simp [C, swapUnit, Matrix.mul_assoc, reduce_row A i j h]
  simp [elim_eq, h₀]
end

structure ReducedRowEchelonForm (mat : Matrix (Fin m) (Fin n) K) where
  elim : (Matrix (Fin m) (Fin m) K)ˣ
  val : Matrix (Fin m) (Fin n) K
  pivots : List ℕ
  h_pivot_lt_n x : pivots.get x < n
  h_elim_mat : elim.val * mat = val
  h_pivot_ordered x y : x < y →
      pivots.get x < pivots.get y
  h_rank_le_height : pivots.length ≤ m
  h_rank_le_width : pivots.length ≤ n
  h_submatrix : val.submatrix
      id (fun x => ⟨pivots.get x, h_pivot_lt_n x⟩) =
      (fun (i : Fin m) (j : Fin pivots.length) => if i.val = j then 1 else 0)
  h_echelon (i : Fin m) (j : Fin n) : i ≥
      Finset.card {x | pivots.get x ≤ j} → val i j = 0

def toReducedRowEchelonForm {n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    ReducedRowEchelonForm (K := K) (m := m) (n := n) A :=
  match n with
  | 0 =>
    {
      elim := 1
      val := A
      pivots := []
      h_pivot_lt_n x := Fin.elim0 (List.length_nil ▸ x)
      h_elim_mat := by simp
      h_pivot_ordered := by simp
      h_rank_le_height := by simp
      h_rank_le_width := by simp
      h_submatrix := by
        ext i j
        exact Fin.elim0 j
      h_echelon := by simp
    }
  | n' + 1 =>
    let B' := toReducedRowEchelonForm A.subLeft
    let C' := B'.elim.val * A
    let S : Finset (Fin m) :=
      { x : Fin m | x ≥ B'.pivots.length ∧ C' x ⟨n', by linarith [B'.h_rank_le_width]⟩ ≠ 0}
    match h : S.min with
    | none =>
      let C := C'
      have h_subLeft : C.subLeft = B'.val := by
        unfold C subLeft
        rw [← submatrix_mul_col]
        exact B'.h_elim_mat
      {
        elim := B'.elim
        val := C
        pivots := B'.pivots
        h_pivot_lt_n x:= by linarith [B'.h_pivot_lt_n x]
        h_elim_mat := rfl
        h_pivot_ordered := B'.h_pivot_ordered
        h_rank_le_width := by linarith [B'.h_rank_le_width]
        h_rank_le_height := B'.h_rank_le_height
        h_submatrix := by
          rw [submatrix_row_col]
          unfold C
          rw [← submatrix_mul_row, ← submatrix_mul_col]
          have h₁ : A.submatrix id (fun x ↦
              ⟨B'.pivots.get x, by linarith [B'.h_pivot_lt_n x]⟩) =
              A.subLeft.submatrix id (fun x ↦
              ⟨B'.pivots.get x, by linarith [B'.h_pivot_lt_n x]⟩) := by
            ext i j
            simp
          rw [h₁, Matrix.submatrix_id_id, submatrix_mul_col, B'.h_elim_mat]
          exact B'.h_submatrix
        h_echelon := by
          intro i j
          by_cases h_j_lt_n : j < n'
          .
            have h₀ : C i j = C.subLeft i ⟨j.1, h_j_lt_n⟩ := by simp
            rw [h₀, h_subLeft]
            exact B'.h_echelon i ⟨j.1, h_j_lt_n⟩
          .
            have h_j_eq_n' : j = ⟨n', by linarith⟩ := by ext; linarith [h_j_lt_n, j.2]
            rw [h_j_eq_n']
            have h₁ x : B'.pivots.get x ≤ n' := by linarith [B'.h_pivot_lt_n x]
            simp [-List.get_eq_getElem, h₁]
            have h₂ : i ∉ S := Finset.eq_empty_iff_forall_notMem.1 (Finset.min_eq_top.1 h) i
            rw [Finset.mem_filter] at h₂
            simp at h₂
            exact h₂
      }
    | some i =>
      have h_i_in_S : i ∈ S := Finset.mem_of_min h
      have h_lt_m : B'.pivots.length < m := by
        rw [Finset.mem_filter] at h_i_in_S
        simp at h_i_in_S
        linarith [h_i_in_S.1, i.2]
      let k : Fin m := ⟨B'.pivots.length, by linarith⟩
      let C := (elimSwapReduce A i ⟨n', by linarith⟩ k).val * C'
      have h_subLeft : C.subLeft = B'.val := by
        sorry
      {
        elim := elimSwapReduce A i ⟨n', by linarith⟩ k * B'.elim
        val := C
        pivots := B'.pivots ++ [n']
        h_pivot_lt_n x := by
          if h : x < B'.pivots.length then
            have h₀ := List.IsPrefix.getElem (List.prefix_append B'.pivots [n']) h
            simp
            rw [← h₀]
            have h₁ :=B'.h_pivot_lt_n ⟨x, h⟩
            simp at h₁
            linarith [h₁]
          else
            have h₀ := x.2
            simp at h₀
            have h₁ : x = B'.pivots.length := by linarith
            simp [h₁]
        h_elim_mat := by
          simp
          rw [Matrix.mul_assoc]
        h_pivot_ordered x y h_x_lt_y := by
          if h_y_lt : y < B'.pivots.length then
            have h_x_lt : x < B'.pivots.length := by
              have h₀ : x.val < y.val := by simp [h_x_lt_y]
              linarith
            have h₀ := List.IsPrefix.getElem (List.prefix_append B'.pivots [n']) h_y_lt
            have h₁ := List.IsPrefix.getElem (List.prefix_append B'.pivots [n']) h_x_lt
            simp
            rw [← h₀, ← h₁]
            exact B'.h_pivot_ordered ⟨x,h_x_lt⟩ ⟨y, h_y_lt⟩ h_x_lt_y
          else
            have h₀ := y.2
            simp at h₀
            have h_y_eq : y = B'.pivots.length := by linarith [h_y_lt, h₀]
            have h₁ := List.getElem_concat_length h_y_eq y.2
            simp [h₁]
            have h_x_lt : x.val < y.val := by simp [h_x_lt_y]
            rw [h_y_eq] at h_x_lt
            have h₂ := List.IsPrefix.getElem (List.prefix_append B'.pivots [n']) h_x_lt
            rw [← h₂]
            have h₃ := B'.h_pivot_lt_n ⟨x, h_x_lt⟩
            simp at h₃
            exact h₃
        h_rank_le_width := by
          simp
          linarith [B'.h_rank_le_width]
        h_rank_le_height := by
          simp
          linarith
        h_submatrix := by
          sorry
        h_echelon := by
          sorry
      }
end Matrix
