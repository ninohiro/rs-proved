-- Implementation of gaussian elimination

import Mathlib.Data.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank

open Option Matrix

variable {K : Type*} [Field K] [DecidableEq K]
variable {m : ℕ} {n : ℕ}

def select (f : Fin m → K) (k : ℕ) : Option (Fin m) :=
  if h₀ : k ≥ m then
    none
  else if f ⟨k, by linarith [h₀]⟩ ≠ 0 then
    some ⟨k, by linarith [h₀]⟩
  else
    select f (k + 1)

lemma select_ne_zero {i : Fin m} {f : Fin m → K} {k : ℕ}
    (h : select f k = some i) : f i ≠ 0 := by
  unfold select at h
  split_ifs at h with _ h_f_ne_zero
  .
    rw [← some.inj h]
    exact h_f_ne_zero
  .
    apply select_ne_zero (k := k + 1) h

def T (i : Fin m) (f : Fin m → K) : Matrix (Fin m) (Fin m) K
  := (fun k l => if l = i ∧ k ≠ l then f k else 0)

omit [DecidableEq K] in
lemma t_pow_two (i : Fin m) (f : Fin m → K) : (T i f) * (T i f) = 0 := by
  change (fun M N i k => (fun j => M i j) ⬝ᵥ fun j => N j k) (T i f) (T i f) = 0
  unfold dotProduct T
  ext k l
  simp
  let f x:= if l = i ∧ ¬x = l then if x = i ∧ ¬k = x then f k * f x else 0 else 0
  change ∑ x, f x = 0
  have h₀ : f = 0 := by
    ext x
    unfold f
    split_ifs with h₁ h₂ <;> try rfl
    rw [h₂.left, h₁.left] at h₁
    exfalso
    exact h₁.right rfl
  rw [h₀]
  simp

section
variable (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n)

def reduce_row : Matrix (Fin m) (Fin m) K :=
  diagonal (fun x => if x = i then (A i j)⁻¹ else 1)

instance [Invertible (A i j)]: Invertible (reduce_row A i j) where
  invOf := diagonal (fun x => if x = i then A i j else 1)
  invOf_mul_self := by
    unfold reduce_row
    simp
    let f := fun i_1 ↦
      if i_1 = i then if i_1 = i then 1 else (A i j)⁻¹
      else if i_1 = i then A i j else 1
    change diagonal f = 1
    have h₀ : f = (fun x => 1) := by
      unfold f
      ext k
      split_ifs <;> rfl
    simp [h₀]
  mul_invOf_self := by
    unfold reduce_row
    simp
    let f := fun i_1 ↦
      if i_1 = i then if i_1 = i then 1 else A i j
      else if i_1 = i then (A i j)⁻¹ else 1
    change diagonal f = 1
    have h₀ : f = (fun x => 1) := by
      unfold f
      ext k
      split_ifs <;> rfl
    simp [h₀]

def elim : Matrix (Fin m) (Fin m) K :=
  1 + T i (fun x : Fin m => - A x j / A i j)

def elimInv : Matrix (Fin m) (Fin m) K :=
  1 + - T i (fun x : Fin m => - A x j / A i j)

omit [DecidableEq K] in
theorem elim_mul_elim_inv : elim A i j * elimInv A i j = 1 := by
  unfold elim elimInv
  let U := T i (fun x : Fin m => - A x j / A i j)
  change (1 + U) * (1 + - U) = 1
  rw [add_mul, mul_add, mul_add]
  simp [add_assoc]
  exact t_pow_two i (fun x : Fin m => - A x j / A i j)

omit [DecidableEq K] in
theorem elim_inv_mul_elim : elimInv A i j * elim A i j = 1 := by
  unfold elim elimInv
  let U := T i (fun x : Fin m => - A x j / A i j)
  change (1 + - U) * (1 + U) = 1
  rw [add_mul, mul_add, mul_add]
  simp [add_assoc]
  exact t_pow_two i (fun x : Fin m => - A x j / A i j)

instance : Invertible (elim A i j) where
  invOf := elimInv A i j
  invOf_mul_self := elim_inv_mul_elim A i j
  mul_invOf_self := elim_mul_elim_inv A i j

def elim_swap_reduce (k_fin : Fin m) : Matrix (Fin m) (Fin m) K :=
  let B := (swap K i k_fin) * reduce_row A i j * A
  (elim B k_fin j) * (swap K i k_fin) * reduce_row A i j

end

instance InvertibleNonZero {c : K} (h : c ≠ 0) : Invertible c where
  invOf := c⁻¹
  invOf_mul_self := by
    rw [mul_comm]
    exact Field.mul_inv_cancel c h
  mul_invOf_self := Field.mul_inv_cancel c h

def toReducedRowEchelonForm.rec
    (X : Matrix (Fin m) (Fin m) K) (A : Matrix (Fin m) (Fin n) K) (pivot : List (Fin n))
    (k : ℕ) (l : ℕ) :=
  if h_l_ge_n : l ≥ n then
    (X, A, pivot)
  else if h_k_ge_m : k ≥ m then
    (X, A, pivot)
  else
    let k_fin : Fin m := ⟨k, by linarith [h_k_ge_m]⟩
    let l_fin : Fin n := ⟨l, by linarith [h_l_ge_n]⟩
    match select (A.col l_fin) k with
    | some i =>
      let P := elim_swap_reduce A i l_fin k_fin
      toReducedRowEchelonForm.rec
          (P * X)
          (P * A)
          (pivot ++ [l_fin]) (k + 1) (l + 1)
    | none =>
      toReducedRowEchelonForm.rec X A pivot k (l+1)

def toReducedRowEchelonForm (A : Matrix (Fin m) (Fin n) K) :=
  toReducedRowEchelonForm.rec 1 A [] 0 0

lemma elim_mul_eq.rec
    (X : Matrix (Fin m) (Fin m) K) (M : Matrix (Fin m) (Fin n) K) (pivot : List (Fin n))
    (k : ℕ) (l : ℕ) :
    let (Y, B, _) := toReducedRowEchelonForm.rec X (X * M) pivot k l
    B = Y * M := by
  unfold toReducedRowEchelonForm.rec
  split_ifs with h_l_ge_n h_k_ge_m <;> try simp
  let k_fin : Fin m := ⟨k, by linarith [h_k_ge_m]⟩
  let l_fin : Fin n := ⟨l, by linarith [h_l_ge_n]⟩
  match select ((X * M).col ⟨l, _⟩) k with
  | some i =>
    simp
    let P := elim_swap_reduce (X * M) i l_fin k_fin
    rw [← Matrix.mul_assoc P X M]
    apply elim_mul_eq.rec
  | none =>
    simp
    apply elim_mul_eq.rec

theorem elim_mul_eq (A : Matrix (Fin m) (Fin n) K) :
    let (Y, B, _) := toReducedRowEchelonForm A
    B = Y * A := by
  unfold toReducedRowEchelonForm
  rw (occs := [1])[← Matrix.one_mul A]
  apply elim_mul_eq.rec

def row_rank (A : Matrix (Fin m) (Fin n) K) : ℕ :=
  let (_, _, pivot) := toReducedRowEchelonForm A
  pivot.length

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
