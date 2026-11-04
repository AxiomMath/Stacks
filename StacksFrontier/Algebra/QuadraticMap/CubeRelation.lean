module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

/-!
# Maps satisfying the cube relation are polynomial of degree at most two

Let `M` and `G` be abelian groups and let `Q : M → G` satisfy the *cube relation*

`Q (x + y + z) + Q x + Q y + Q z = Q (x + y) + Q (x + z) + Q (y + z)`

for all `x y z : M`. This is the shape of the relation which the theorem of the cube imposes on
the classes `[f^* L]` in `Pic(B)` of the pullbacks of an invertible module `L` on an abelian
variety `A` along morphisms `f : B ⟶ A` ([Stacks, Tag 0BFE], in this library
`Stacks.Groupoids.pullbackPicardClass_cubeRelation`).

Such a map is a polynomial map of degree at most two: `Q 0 = 0`, the map
`B x y = Q (x + y) - Q x - Q y` is biadditive, and for integers `c₁, …, c_r` and elements
`v₁, …, v_r` of `M`,

`2 • Q (∑ c_k • v_k) = ∑_k (c_k (c_k + 1) • Q v_k + c_k (c_k - 1) • Q (-v_k))
  + ∑_{j < k} 2 c_j c_k • B v_j v_k`.

Consequently, for every multilinear map `I : G^d → ℤ`, the integer
`I (Q (∑ c_k • v_k), …, Q (∑ c_k • v_k))` is the value at `c` of a polynomial with rational
coefficients in `r` variables of total degree at most `2 d`. With `I` the intersection pairing
on `Pic(A)` this is the statement that the degree of `∑ c_k a_k`, for endomorphisms `a_k` of an
abelian variety of dimension `g`, is a polynomial of degree at most `2 g` in the `c_k`, the
first step of the proof that the degree of an endomorphism is the determinant of its action on
the Tate module.

## Main definitions

* `Stacks.QuadraticMap.cubeBilin` — the biadditive map `B x y = Q (x + y) - Q x - Q y`.

## Main results

* `Stacks.QuadraticMap.map_zero_of_cube` — `Q 0 = 0`.
* `Stacks.QuadraticMap.cubeBilin_add_left` — `B` is additive in its first argument.
* `Stacks.QuadraticMap.two_smul_map_zsmul_of_cube` —
  `2 • Q (n • v) = n (n + 1) • Q v + n (n - 1) • Q (-v)`.
* `Stacks.QuadraticMap.map_sum_of_cube` —
  `Q (∑_{k ∈ s} x k) = ∑_k Q (x k) + ∑_{j < k} B (x j) (x k)`.
* `Stacks.QuadraticMap.two_smul_map_sum_zsmul_of_cube` — the expansion of `2 • Q (∑ c_k • v_k)`.
* `Stacks.QuadraticMap.exists_mvPolynomial_multilinear_eq` — the polynomiality.
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.QuadraticMap

variable {M G : Type*} [AddCommGroup M] [AddCommGroup G] (Q : M → G)

/-- The biadditive map `B x y = Q (x + y) - Q x - Q y` attached to a map satisfying the cube
relation. -/
def cubeBilin (x y : M) : G := Q (x + y) - Q x - Q y

variable {Q}
variable (hQ : ∀ x y z : M, Q (x + y + z) + Q x + Q y + Q z = Q (x + y) + Q (x + z) + Q (y + z))
include hQ

/-- A map satisfying the cube relation vanishes at zero. -/
theorem map_zero_of_cube : Q 0 = 0 := by
  have h := hQ 0 0 0
  simp only [add_zero] at h
  have : Q 0 + Q 0 + Q 0 + Q 0 - (Q 0 + Q 0 + Q 0) = Q 0 := by abel
  rw [← this, h, sub_self]

/-- The map `B` is additive in its first argument. -/
theorem cubeBilin_add_left (x z y : M) :
    cubeBilin Q (x + z) y = cubeBilin Q x y + cubeBilin Q z y := by
  have h := hQ x z y
  unfold cubeBilin
  have e : Q (x + z + y) = Q (x + z) + Q (x + y) + Q (z + y) - Q x - Q z - Q y := by
    rw [← h]; abel
  rw [e]
  abel

/-- `B (-, y)` as an additive map. -/
def cubeBilinLeft (y : M) : M →+ G :=
  AddMonoidHom.mk' (fun x => cubeBilin Q x y) (fun x z => cubeBilin_add_left hQ x z y)

/-- `cubeBilinLeft hQ y x = B x y`. -/
theorem cubeBilinLeft_apply (y x : M) : cubeBilinLeft hQ y x = cubeBilin Q x y := rfl

/-- The map `B` is symmetric. -/
theorem cubeBilin_comm (x y : M) : cubeBilin Q x y = cubeBilin Q y x := by
  unfold cubeBilin
  rw [add_comm x y]
  abel

/-- The map `B` is additive in its second argument. -/
theorem cubeBilin_add_right (x y z : M) :
    cubeBilin Q x (y + z) = cubeBilin Q x y + cubeBilin Q x z := by
  rw [cubeBilin_comm hQ, cubeBilin_add_left hQ, cubeBilin_comm hQ y, cubeBilin_comm hQ z]

/-- `B (m • x) (n • y) = (m * n) • B x y`. -/
theorem cubeBilin_zsmul (m n : ℤ) (x y : M) :
    cubeBilin Q (m • x) (n • y) = (m * n) • cubeBilin Q x y := by
  have h1 : ∀ (a : ℤ) (u w : M), cubeBilin Q (a • u) w = a • cubeBilin Q u w := fun a u w =>
    (cubeBilinLeft hQ w).map_zsmul a u
  rw [h1, cubeBilin_comm hQ x, h1, cubeBilin_comm hQ y, mul_smul]

/-- The one-step recursion along a line:
`Q ((n + 1) • v) = Q (n • v) + Q v + n • (Q v + Q (-v))`. -/
theorem map_add_one_zsmul_of_cube (n : ℤ) (v : M) :
    Q ((n + 1) • v) = Q (n • v) + Q v + n • (Q v + Q (-v)) := by
  have hB : cubeBilin Q v v = Q v + Q (-v) := by
    have h := cubeBilin_add_left hQ v (-v) v
    rw [add_neg_cancel] at h
    unfold cubeBilin at h ⊢
    rw [zero_add, neg_add_cancel, map_zero_of_cube hQ] at h
    have h' : Q (v + v) - Q v - Q v - (Q v + Q (-v)) =
        -(Q v - 0 - Q v - (Q (v + v) - Q v - Q v + (0 - Q (-v) - Q v))) := by abel
    rw [← sub_eq_zero, h', h, sub_self, neg_zero]
  have h := cubeBilin_zsmul hQ n 1 v v
  rw [one_smul, mul_one, hB] at h
  unfold cubeBilin at h
  rw [add_smul, one_smul, ← h]
  abel

/-- **A map satisfying the cube relation is quadratic along a line.**
`2 • Q (n • v) = n (n + 1) • Q v + n (n - 1) • Q (-v)`. -/
theorem two_smul_map_zsmul_of_cube (n : ℤ) (v : M) :
    (2 : ℤ) • Q (n • v) = (n * (n + 1)) • Q v + (n * (n - 1)) • Q (-v) := by
  induction n using Int.induction_on with
  | zero => simp [map_zero_of_cube hQ]
  | succ n ih =>
    rw [map_add_one_zsmul_of_cube hQ, smul_add, smul_add, ih]
    module
  | pred n ih =>
    have h := map_add_one_zsmul_of_cube hQ (-(n : ℤ) - 1) v
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at h
    have h' : Q ((-(n : ℤ) - 1) • v) =
        Q (-(n : ℤ) • v) - Q v - (-(n : ℤ) - 1) • (Q v + Q (-v)) := by
      rw [h]; abel
    rw [h', smul_sub, smul_sub, ih]
    module

/-- **The cube relation expands a finite sum.** For a finite set `s` of a linearly ordered
type, `Q (∑_{k ∈ s} x k) = ∑_{k ∈ s} Q (x k) + ∑_{j, k ∈ s, j < k} B (x j) (x k)`. -/
theorem map_sum_of_cube {ι : Type*} [LinearOrder ι] (x : ι → M) (s : Finset ι) :
    Q (∑ k ∈ s, x k) = ∑ k ∈ s, Q (x k) +
      ∑ j ∈ s, ∑ k ∈ s, if j < k then cubeBilin Q (x j) (x k) else 0 := by
  refine Finset.induction_on_max s (by simp [map_zero_of_cube hQ]) ?_
  intro a s ha ih
  · have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hB : cubeBilin Q (∑ j ∈ s, x j) (x a) = ∑ j ∈ s, cubeBilin Q (x j) (x a) := by
      simp only [← cubeBilinLeft_apply hQ, map_sum]
    have hQs : Q (∑ k ∈ insert a s, x k) = Q (∑ k ∈ s, x k) + Q (x a) +
        cubeBilin Q (∑ j ∈ s, x j) (x a) := by
      rw [sum_insert has]; unfold cubeBilin; abel_nf
    have hrow : ∀ j ∈ s, (∑ k ∈ insert a s, if j < k then cubeBilin Q (x j) (x k) else 0) =
        (∑ k ∈ s, if j < k then cubeBilin Q (x j) (x k) else 0) + cubeBilin Q (x j) (x a) := by
      intro j hj
      rw [sum_insert has, if_pos (ha j hj), add_comm]
    have hcol : (∑ k ∈ insert a s, if a < k then cubeBilin Q (x a) (x k) else 0) = 0 := by
      refine sum_eq_zero fun k hk => ?_
      rcases mem_insert.mp hk with rfl | hk
      · simp
      · rw [if_neg (not_lt.mpr (ha k hk).le)]
    rw [hQs, ih, hB, sum_insert has, sum_insert has, hcol, zero_add, sum_congr rfl hrow,
      sum_add_distrib]
    abel

/-- **The cube relation expands an integral combination.** For `c : ι → ℤ` and `v : ι → M`,
`2 • Q (∑ c_k • v_k)` is the integral combination of the classes `Q v_k`, `Q (-v_k)` and
`B v_j v_k` with coefficients `c_k (c_k + 1)`, `c_k (c_k - 1)` and `2 c_j c_k` (for `j < k`). -/
theorem two_smul_map_sum_zsmul_of_cube {ι : Type*} [LinearOrder ι] [Fintype ι] (c : ι → ℤ)
    (v : ι → M) :
    (2 : ℤ) • Q (∑ k, c k • v k) =
      ∑ k, ((c k * (c k + 1)) • Q (v k) + (c k * (c k - 1)) • Q (-v k)) +
        ∑ j, ∑ k, (if j < k then 2 * (c j * c k) else 0) • cubeBilin Q (v j) (v k) := by
  rw [map_sum_of_cube hQ, smul_add]
  congr 1
  · rw [smul_sum]
    exact sum_congr rfl fun k _ => two_smul_map_zsmul_of_cube hQ (c k) (v k)
  · rw [smul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [smul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [cubeBilin_zsmul hQ, mul_smul, mul_smul, mul_smul]
    · simp

/-- **Polynomiality of a multilinear form along a map with the cube relation.** For a
multilinear map `I : G^d → ℤ`, a finite linearly ordered index type `ι` and vectors
`v : ι → M`, there is a polynomial `P` with rational coefficients in the variables `ι`, of total
degree at most `2 d`, such that `I (Q (∑ c_k • v_k), …, Q (∑ c_k • v_k)) = P (c)` for every
`c : ι → ℤ`. -/
theorem exists_mvPolynomial_multilinear_eq {ι : Type*} [LinearOrder ι] [Fintype ι] (d : ℕ)
    (I : MultilinearMap ℤ (fun _ : Fin d => G) ℤ) (v : ι → M) :
    ∃ P : MvPolynomial ι ℚ, P.totalDegree ≤ 2 * d ∧ ∀ c : ι → ℤ,
      ((I fun _ => Q (∑ k, c k • v k) : ℤ) : ℚ) = MvPolynomial.eval (fun k => (c k : ℚ)) P := by
  classical
  let T := ι ⊕ ι ⊕ (ι × ι)
  let w : T → G := fun t => match t with
    | Sum.inl k => Q (v k)
    | Sum.inr (Sum.inl k) => Q (-v k)
    | Sum.inr (Sum.inr jk) => cubeBilin Q (v jk.1) (v jk.2)
  let a : T → (ι → ℤ) → ℤ := fun t c => match t with
    | Sum.inl k => c k * (c k + 1)
    | Sum.inr (Sum.inl k) => c k * (c k - 1)
    | Sum.inr (Sum.inr jk) => if jk.1 < jk.2 then 2 * (c jk.1 * c jk.2) else 0
  let A : T → MvPolynomial ι ℚ := fun t => match t with
    | Sum.inl k => MvPolynomial.X k * (MvPolynomial.X k + MvPolynomial.C 1)
    | Sum.inr (Sum.inl k) => MvPolynomial.X k * (MvPolynomial.X k + MvPolynomial.C (-1))
    | Sum.inr (Sum.inr jk) =>
        if jk.1 < jk.2 then MvPolynomial.C 2 * (MvPolynomial.X jk.1 * MvPolynomial.X jk.2) else 0
  have hAa : ∀ t c, MvPolynomial.eval (fun k => (c k : ℚ)) (A t) = (a t c : ℚ) := by
    intro t c
    rcases t with k | k | jk
    · simp [A, a]
    · simp [A, a, sub_eq_add_neg]
    · simp only [A, a]
      split_ifs <;> simp
  have hCm : ∀ (b : ℚ) (P : MvPolynomial ι ℚ),
      (MvPolynomial.C b * P).totalDegree ≤ P.totalDegree := fun b P =>
    (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_C, zero_add])
  have hX : ∀ (b : ℚ) (k : ι), (MvPolynomial.X k + MvPolynomial.C b).totalDegree ≤ 1 := fun b k =>
    (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by rw [MvPolynomial.totalDegree_X]) (by rw [MvPolynomial.totalDegree_C]; simp))
  have hA : ∀ t, (A t).totalDegree ≤ 2 := by
    intro t
    rcases t with k | k | jk
    · exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (by simp) (hX _ _))
    · exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (by simp) (hX _ _))
    · simp only [A]
      split_ifs
      · refine (hCm _ _).trans ((MvPolynomial.totalDegree_mul _ _).trans ?_)
        simp only [MvPolynomial.totalDegree_X]
        norm_num
      · simp
  have hexp : ∀ c : ι → ℤ, (2 : ℤ) • Q (∑ k, c k • v k) = ∑ t, a t c • w t := by
    intro c
    rw [two_smul_map_sum_zsmul_of_cube hQ, Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [a, w, sum_add_distrib, add_assoc]
  refine ⟨MvPolynomial.C ((1 : ℚ) / 2 ^ d) *
    ∑ σ : Fin d → T, MvPolynomial.C ((I fun i => w (σ i) : ℤ) : ℚ) * ∏ i, A (σ i), ?_, ?_⟩
  · refine (hCm _ _).trans ?_
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
    refine (hCm _ _).trans ?_
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    calc ∑ i, (A (σ i)).totalDegree ≤ ∑ _i : Fin d, 2 := sum_le_sum fun i _ => hA (σ i)
      _ = 2 * d := by simp [mul_comm]
  · intro c
    have key : (2 : ℤ) ^ d * I (fun _ => Q (∑ k, c k • v k)) =
        ∑ σ : Fin d → T, (∏ i, a (σ i) c) * I (fun i => w (σ i)) := by
      have h1 : I (fun _ : Fin d => (2 : ℤ) • Q (∑ k, c k • v k)) =
          (2 : ℤ) ^ d * I (fun _ => Q (∑ k, c k • v k)) := by
        rw [MultilinearMap.map_smul_univ, prod_const, card_univ, Fintype.card_fin, smul_eq_mul]
      rw [← h1]
      simp only [hexp]
      rw [MultilinearMap.map_sum]
      refine sum_congr rfl fun σ _ => ?_
      rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    have key' : ((I fun _ => Q (∑ k, c k • v k) : ℤ) : ℚ) =
        1 / 2 ^ d * ∑ σ : Fin d → T, (∏ i, (a (σ i) c : ℚ)) * (I (fun i => w (σ i)) : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) key
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sum, Int.cast_prod] at this
      rw [← this, ← mul_assoc, one_div, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
    rw [key', map_mul, MvPolynomial.eval_C, map_sum]
    congr 1
    refine sum_congr rfl fun σ _ => ?_
    rw [map_mul, MvPolynomial.eval_C, map_prod, mul_comm]
    congr 1
    exact prod_congr rfl fun i _ => (hAa (σ i) c).symm

end Stacks.QuadraticMap
