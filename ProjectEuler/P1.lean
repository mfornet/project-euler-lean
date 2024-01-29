-- Project Euler - Problem 1
-- Multiples of 3 or 5
-- https://projecteuler.net/problem=1
--
-- The definition of the problem is:
-- Euler1_Def
--
-- The solution to the problem is:
-- Euler1_Sol
--
-- The proof that the two are equivalent is:
-- Euler1_equiv

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Num.Lemmas
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Tactic.LibrarySearch

def SetSum (a : Finset ℕ) : ℕ :=
  Finset.sum a id

-- The sum of the multiples of 3 or 5 below n
-- This is a simpler definition based on the problem description
def Euler1_Def (n : ℕ) : ℕ  :=
  SetSum (Finset.filter (fun n => (3 ∣ n) ∨ (5 ∣ n)) (Finset.range n))

-- This simple definition is fast enough to compute small values of n
#eval Euler1_Def 10
#eval Euler1_Def 1000
-- However, it won't work in reasonable time for computing large values of n
-- #eval Euler1_Def 100000000000

-- The sum of the first n natural numbers
def SumToN (n : ℕ) : ℕ :=
  n * (n - 1) / 2

-- The sum of the multiples of k less than n
def SumMulKToN (k n : ℕ) : ℕ :=
  k * SumToN ((n + k - 1) / k)

-- Efficiently compute the sum of the multiples of 3 or 5 below n
def Euler1_Sol (n : ℕ) : ℕ :=
  SumMulKToN 3 n + SumMulKToN 5 n - SumMulKToN 15 n

-- We can use this to compute the answer to the problem
#eval Euler1_Sol 10
#eval Euler1_Sol 1000
-- And it will allow us to compute the answer for larger values of n
#eval Euler1_Sol 100000000000

def MulFinsetByK (k : ℕ) (h: k > 0) (a : Finset ℕ) : Finset ℕ :=
  Finset.map ⟨fun n => k * n, (by exact mul_right_injective₀ (Iff.mp Nat.pos_iff_ne_zero h) )⟩ a

-- Multiples of k in the range [0, n)
def MulKToN (k n : ℕ) (h: k > 0) : Finset ℕ :=
  MulFinsetByK k h (Finset.range ((n + k - 1) / k))

lemma emod_pos_of_not_dvd {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  rw [Nat.dvd_iff_mod_eq_zero] at h
  exact Nat.pos_of_ne_zero h

lemma lt_ceil_of_lt_floor (n k d : ℕ) (hk: k > 0) : k * d < n ↔ d < (n + k - 1) / k := by
  have ht (a b : ℕ) : a < b ↔ k * a < k * b := by exact Iff.symm (mul_lt_mul_left hk)
  have hf (a b : ℕ) (hs : b < k) : (k * a + b) / k = a := by rw [
                                                          Nat.add_div_of_dvd_right (Nat.dvd_mul_right k a),
                                                          Nat.mul_div_cancel_left _ hk,
                                                          (Nat.div_eq_zero_iff (by linarith)).mpr (by linarith),
                                                          Nat.add_zero]
  have hy (a b d r : ℕ) (h1 : r > 0) (h2 : r < d) (h3 : d ∣ b) : d * a < b + r ↔ a ≤ b / d := by
    rcases h3 with ⟨c, rfl⟩
    rw [Nat.mul_div_cancel_left _ (by linarith)]

    constructor
    . contrapose!
      intro he
      calc
        d * c + r ≤ d * c + d := by linarith
              _ = d * (c + 1) := by ring_nf
              _ ≤ d * a := by exact Nat.mul_le_mul_left _ he
    . intro he
      calc
        d * a ≤ d * c := by exact (mul_le_mul_left (by linarith)).mpr he
            _ < d * c + r := by linarith


  by_cases hd : k ∣ n
  . rcases hd with ⟨m, hm⟩
    rw [hm, ← ht, Nat.add_sub_assoc, hf m (k - 1) (by
      rcases k with (k | h)
      . linarith
      . change h + 1 - 1 < h + 1
        exact Nat.lt_succ_self h
      )]
    linarith
  . rw [← Nat.mod_add_div n k, Nat.add_comm]
    have hu : n % k > 0 := by exact emod_pos_of_not_dvd hd
    rw [hy _ _ _ _ hu (by exact Nat.mod_lt n hk) (by exact Nat.dvd_mul_right _ _), Nat.mul_div_cancel_left]
    . have hu : (k * (n / k) + n % k + k - 1) / k = n / k + 1 := by
        calc (k * (n / k) + n % k + k - 1) / k = (k * (n / k + 1) + n % k - 1) / k := by ring_nf
                                             _ = (k * (n / k + 1) + (n % k - 1)) / k := by rw [Nat.add_sub_assoc (by linarith) _]
                                             _ = n / k + 1 := by rw [hf (n / k + 1) _ (by apply tsub_lt_of_lt; exact Nat.mod_lt n hk)]
      rw [hu, Nat.lt_succ]
    assumption

lemma eq_filter_and_proj (k n : ℕ) (hk: k > 0): Finset.filter (fun x ↦ k ∣ x) (Finset.range n) = MulKToN k n hk := by
  apply Finset.ext_iff.mpr
  intro a
  unfold MulKToN
  unfold MulFinsetByK
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_map]
  constructor
  . rintro ⟨hr, ⟨d, hd⟩⟩
    use d
    constructor
    . rw [Finset.mem_range]
      rw [hd] at hr
      exact Iff.mp (lt_ceil_of_lt_floor n k d hk) hr
    . exact id (Eq.symm hd)
  . intro ⟨a1, ⟨hr, hd⟩ ⟩
    rw [Finset.mem_range] at hr
    constructor
    . change k * a1 = a at hd
      rw [← hd]
      exact Iff.mpr (lt_ceil_of_lt_floor n k a1 hk) hr
    . change k * a1 = a at hd
      rw [← hd]
      exact Nat.dvd_mul_right k a1

def Euler1_Set (n : ℕ) : Finset ℕ :=
  (MulKToN 3 n (by linarith)) ∪ (MulKToN 5 n (by linarith))

def Euler1_Sum (n : ℕ) : ℕ :=
  SetSum (Euler1_Set n)

lemma eq_set_eq_sum (s t : Finset ℕ) : (s = t) → SetSum s = SetSum t := by
  intro h
  rw [h]

lemma def_eq_target (n : ℕ) : Euler1_Def n = Euler1_Sum n := by
  apply eq_set_eq_sum
  unfold Euler1_Set
  rw [Finset.filter_or, eq_filter_and_proj 3 _, eq_filter_and_proj 5 _]

lemma a_plus_b_minus_c (a b c : ℕ) : c ≤ b → a + (b - c) = a + b - c := by
  exact fun a_1 ↦ Eq.symm (Nat.add_sub_assoc a_1 a)

lemma sum_disj_union (a b : Finset ℕ) (h : Disjoint a b) : SetSum (a ∪ b) = SetSum a + SetSum b := by
  unfold SetSum
  rw [← Finset.sum_disjUnion h]
  apply eq_set_eq_sum
  exact Eq.symm (Finset.disjUnion_eq_union a b h)

lemma set_diff_sum (a b : Finset ℕ) : SetSum (a \ b) = SetSum a - SetSum (a ∩ b) := by
  refine Eq.symm (Nat.sub_eq_of_eq_add ?h)
  have h : a = (a \ b) ∪ (a ∩ b) := by exact Eq.symm (Finset.sdiff_union_inter a b)
  nth_rewrite 1 [h]
  apply sum_disj_union
  exact Finset.disjoint_sdiff_inter a b

theorem pie2 (a b : Finset ℕ) : SetSum (a ∪ b) = SetSum a + SetSum b - SetSum (a ∩ b) := by
  have h: SetSum (a ∩ b) ≤ SetSum b := by {
    apply Finset.sum_le_sum_of_subset_of_nonneg
    . exact Finset.inter_subset_right a b
    . exact fun i _ _ ↦ Nat.zero_le (id i)
  }

  calc
    SetSum (a ∪ b) = SetSum (a ∪ (b \ a))  := by apply eq_set_eq_sum; exact Eq.symm Finset.union_sdiff_self_eq_union
                 _ = SetSum a + SetSum (b \ a)  := by apply sum_disj_union; exact Finset.disjoint_sdiff
                 _ = SetSum a + SetSum b - SetSum (a ∩ b) := by rw [set_diff_sum, Finset.inter_comm, a_plus_b_minus_c _ _ _ h]

lemma ex_mul_k_n (a k n : ℕ) (h : k > 0): a ∈ MulKToN k n h ↔ a < n ∧ k ∣ a := by
  unfold MulKToN
  unfold MulFinsetByK
  rw [Finset.mem_map]

  constructor
  . intro ⟨a1, h⟩
    rw [Finset.mem_range] at h
    rcases h with ⟨hl, hf⟩
    change k * a1 = a at hf
    rw [← hf]
    constructor
    . exact Iff.mpr (lt_ceil_of_lt_floor n k a1 h) hl
    . exact Nat.dvd_mul_right k a1
  . intro ⟨ha, hd⟩
    use a / k
    constructor
    . rcases hd with ⟨d, hd⟩
      rw [hd] at ha
      rw [Finset.mem_range, hd, Nat.mul_div_right d h]
      exact Iff.mp (lt_ceil_of_lt_floor n k d h) ha
    . change k * (a / k) = a
      exact Nat.mul_div_cancel' hd

lemma coprime_mul_dvd_iff_dvd_and_dvd (x y n: ℕ) : Nat.Coprime x y → (x ∣ n ∧ y ∣ n ↔ x * y ∣ n) := by
  intro h
  constructor
  . intro ⟨hx, hy⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h hx hy
  . intro hxy
    constructor
    . exact dvd_of_mul_right_dvd hxy
    . exact dvd_of_mul_left_dvd hxy

lemma mul_k_inter (x y n: ℕ) (hx : x > 0) (hy : y > 0) :
    Nat.Coprime x y → MulKToN x n hx ∩ MulKToN y n hy = MulKToN (x * y) n (by exact Nat.mul_pos hx hy) := by
  intro hg
  apply Finset.ext_iff.mpr
  intro a
  rw [Finset.mem_inter, ex_mul_k_n, ex_mul_k_n, ex_mul_k_n]

  calc
    (a < n ∧ x ∣ a) ∧ a < n ∧ y ∣ a ↔ a < n ∧ (x ∣ a  ∧ y ∣ a) := by simp[and_assoc, and_comm]
                                  _ ↔ a < n ∧ x * y ∣ a := by rw[coprime_mul_dvd_iff_dvd_and_dvd _ _ a hg]

lemma k_mul_sum_eq_sum_k_mul {k : ℕ} (a : Finset ℕ) : k * Finset.sum a id = Finset.sum a (fun x => k * x) := by
  let fn: ℕ → ℕ := fun x => k * x
  let fnz: ZeroHom ℕ ℕ := ⟨fn, by simp⟩
  let fna: AddMonoidHom ℕ ℕ := ⟨fnz, by (intro x y; simp; ring)⟩
  have hf : ∀ x, fna x = k * x := by simp
  rw [← hf (Finset.sum a id)]
  rw [map_sum fna id a]
  rfl

lemma cancel_mul_k_finset (k : ℕ) (h : k > 0) (a : Finset ℕ) : k * SetSum a = SetSum (MulFinsetByK k h a) := by
  unfold SetSum
  unfold MulFinsetByK
  rw [Finset.sum_map]
  apply k_mul_sum_eq_sum_k_mul

lemma two_div_choose_two (n : ℕ) : 2 ∣ (n + 1) * n := by
  by_cases h : Even n
  . rcases h with ⟨k, hk⟩
    use k * (n + 1)
    rw [hk]
    ring_nf
  . rw [← Nat.odd_iff_not_even] at h
    rcases h with ⟨k, hk⟩
    use n * (k + 1)
    rw [hk]
    ring_nf

lemma sum_first_n (n : ℕ) : SetSum (Finset.range n) = SumToN n := by
  unfold SetSum
  unfold SumToN
  induction n with
  | zero => rfl
  | succ n ih =>
    change Finset.sum (Finset.range (n + 1)) id = (n + 1) * n / 2
    rw [Finset.sum_range_succ, ih, id.def]

    have mul_left : ∀ a b c : ℕ, c > 0 → (a = b ↔ c * a = c * b) := by
      exact fun a b c h => Iff.symm (mul_left_cancel_iff_of_pos h)

    rw [mul_left _ _ 2 (by linarith)]
    rw [← Nat.mul_div_assoc 2 (by exact two_div_choose_two n)]
    rw [Nat.mul_div_cancel_left _ (by linarith)]

    ring_nf
    calc
      n * 2 + n * (n - 1) / 2 * 2 = n * 2 + 2 * ((n * (n - 1)) / 2) := by ring_nf
                                _ = n * 2 + n * (n - 1) := by rw [← Nat.mul_div_assoc 2 (by
                                                                  rcases n with (_ | h)
                                                                  . change 2 ∣ 0
                                                                    use 0
                                                                  change 2 ∣ (h + 1) * h
                                                                  exact two_div_choose_two h
                                                                ), Nat.mul_div_cancel_left _ (by linarith)]
                                _ = n + n ^ 2 := by (
                                                    rcases n with (_ | h)
                                                    . rfl
                                                    . change (h + 1) * 2 + (h + 1) * h = (h + 1) + (h + 1) ^ 2
                                                      ring_nf
                                                  )

-- The sum of all multiples of `k` between 0 and `n` can be computed quickly
theorem eq_sum_mul_k_to_n (k n : ℕ) (h : k > 0): SumMulKToN k n = SetSum (MulKToN k n h) := by
  unfold MulKToN
  rw [← cancel_mul_k_finset]
  unfold SumMulKToN
  have nat_mul_left_cancel {n m k : ℕ } (h : m = k) : n * m = n * k := by exact congrArg (HMul.hMul n) h
  apply nat_mul_left_cancel
  rw [sum_first_n]

lemma sol_eq_target (n : ℕ) : Euler1_Sol n = Euler1_Sum n := by
  unfold Euler1_Sol
  unfold Euler1_Sum
  unfold Euler1_Set
  rw [pie2, mul_k_inter _ _ _ (by simp), eq_sum_mul_k_to_n, eq_sum_mul_k_to_n, eq_sum_mul_k_to_n]
  rfl

theorem Euler1_equiv (n : ℕ) : Euler1_Def n = Euler1_Sol n := by
  rw [def_eq_target, sol_eq_target]
