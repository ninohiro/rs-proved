-- Implementation of gaussian elimination

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic


open Option Matrix


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
  pivots : List (Fin n)
  rank : ℕ
  h_elim_mat : elim.val * mat = val
  h_pivots_eq_rank : pivots.length = rank
  h_pivot_ordered (x y : Fin rank) : x < y →
      pivots.get ⟨x, by simp [h_pivots_eq_rank]⟩ < pivots.get ⟨y, by simp [h_pivots_eq_rank]⟩
  h_rank_le_height : rank ≤ m
  h_rank_le_width : rank ≤ n
  h_submatrix : val.submatrix
      id (fun x : Fin rank => pivots.get ⟨x.1, by simp[h_pivots_eq_rank]⟩) =
      (fun (i : Fin m) (j : Fin rank) => if i.val = j then 1 else 0)
  h_echelon (i : Fin m) (j : Fin n) : i ≥ {j' ∈ pivots.toFinset | j' ≤ j}.card → val i j = 0

def toReducedRowEchelonForm {n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    ReducedRowEchelonForm (K := K) (m := m) (n := n) A :=
  match n with
  | 0 =>
    {
      elim := 1
      val := A
      pivots := []
      rank := 0
      h_elim_mat := by simp
      h_pivots_eq_rank := rfl
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
    let C := B'.elim.val * A
    match Finset.min
        { x : Fin m | x ≥ B'.rank ∧ A x ⟨n', by linarith [B'.h_rank_le_width]⟩ ≠ 0} with
    | none =>
      {
        elim := B'.elim
        val := C
        pivots := B'.pivots.map Fin.castSucc
        rank := B'.rank
        h_elim_mat := rfl
        h_pivots_eq_rank := by simp [B'.h_pivots_eq_rank]
        h_pivot_ordered := by
          simp
          exact B'.h_pivot_ordered
        h_rank_le_height := B'.h_rank_le_height
        h_rank_le_width := by linarith [B'.h_rank_le_width]
        h_submatrix := by
          rw [submatrix_row_col]
          unfold C
          rw [← submatrix_mul_row, ← submatrix_mul_col]
          have h₀ : A.submatrix id (fun x : Fin B'.rank ↦
              (List.map Fin.castSucc B'.pivots).get ⟨x.1, by simp [x.2, B'.h_pivots_eq_rank]⟩) =
              A.subLeft.submatrix id (fun x : Fin B'.rank ↦
              B'.pivots.get ⟨↑x, by simp [x.2, B'.h_pivots_eq_rank]⟩) := by
            ext i j
            simp
            rfl
          rw [h₀, Matrix.submatrix_id_id, submatrix_mul_col, B'.h_elim_mat, B'.h_submatrix]
        h_echelon := by

      }
    | some i =>
      ReducedRowEchelonForm := {
        val := C
        pivots := B'.pivots
        rank := B'.rank
        h_pivots_eq_rank := rfl
        h_pivot_ordered := by simp
        h_rank_le_height := by simp
        h_rank_le_width := by simp
        h_submatrix := by simp
        h_echelon := by simp
      }

/-!
def toReducedRowEchelonForm.rec
    (X : (Matrix (Fin m) (Fin m) K)ˣ) (A : Matrix (Fin m) (Fin n) K) (pivots : List (Fin n))
    (k : ℕ) (l : ℕ) :=
  if h_l_ge_n : l ≥ n then
    (X, A, pivots)
  else if h_k_ge_m : k ≥ m then
    (X, A, pivots)
  else
    let k_fin : Fin m := ⟨k, by linarith [h_k_ge_m]⟩
    let l_fin : Fin n := ⟨l, by linarith [h_l_ge_n]⟩
    match Finset.min { x : Fin m | x ≥ k_fin ∧ A x l_fin ≠ 0} with
    | some i =>
      let P := elimSwapReduce A i l_fin k_fin
      toReducedRowEchelonForm.rec
          (P * X)
          (P.val * A)
          (pivots ++ [l_fin]) (k + 1) (l + 1)
    | none =>
      toReducedRowEchelonForm.rec X A pivots k (l+1)

def toReducedRowEchelonForm (A : Matrix (Fin m) (Fin n) K) :=
  toReducedRowEchelonForm.rec 1 A [] 0 0

lemma elim_mul_eq.rec
    (X : (Matrix (Fin m) (Fin m) K)ˣ) (M : Matrix (Fin m) (Fin n) K) (pivot : List (Fin n))
    (k : ℕ) (l : ℕ) :
    let (Y, B, _) := toReducedRowEchelonForm.rec X (X.val * M) pivot k l
    B = Y.val * M := by
  unfold toReducedRowEchelonForm.rec
  split_ifs with h_l_ge_n h_k_ge_m <;> try simp
  let k_fin : Fin m := ⟨k, by linarith [h_k_ge_m]⟩
  let l_fin : Fin n := ⟨l, by linarith [h_l_ge_n]⟩
  match Finset.min {x : Fin m | k_fin ≤ x ∧ (X.val * M) x l_fin ≠ 0} with
  | some i =>
    simp
    let P := (elimSwapReduce (X.val * M) i l_fin k_fin).val
    rw [← Matrix.mul_assoc P X.val M]
    apply elim_mul_eq.rec
  | none =>
    simp
    apply elim_mul_eq.rec

section
variable (A : Matrix (Fin m) (Fin n) K)
theorem elim_mul_eq :
    let (Y, B, _) := toReducedRowEchelonForm A
    B = Y.val * A := by
  unfold toReducedRowEchelonForm
  rw (occs := [1])[← Matrix.one_mul A]
  apply elim_mul_eq.rec

def resize_matrix (k l : ℕ) : Matrix (Fin k) (Fin l) K :=
  (fun i j => if h : i < m ∧ j < n then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0)

def rowRank : ℕ :=
  let (_, _, pivots) := toReducedRowEchelonForm A
  pivots.length

theorem pivot_matrix :
    let (_, B, pivots) := toReducedRowEchelonForm A
    B.submatrix id (fun x => pivots.get x) =
    (fun i j => if i.val = j.val then 1 else 0) := by
  sorry

end

def pivotVector (pivot : List (Fin n)) (v : Fin m → K) : Fin n → K :=
  ∑ j : Fin (pivot.length),
    fun i : Fin n => if i = pivot[j] then if h : i<m then v ⟨i, h⟩ else 0 else 0

def nonTrivialSolution (A : Matrix (Fin m) (Fin n) K) :
    Option (Fin n → K):=
  let (_, B, pivot) := toReducedRowEchelonForm A
  match (Finset.univ \ pivot.toFinset).min with
  | some l =>
    some ((fun i => if i = l then 1 else 0) - pivotVector pivot (B.col l))
  | none => none
-/
