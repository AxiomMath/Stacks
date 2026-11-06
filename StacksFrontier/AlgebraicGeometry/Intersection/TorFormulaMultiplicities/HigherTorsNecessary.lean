module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.RingTheory.MvPowerSeries.LowDegree

/-!
# The higher Tor modules are needed for intersection multiplicities

Work in `A = ℂ[[x, y, z, w]]`, the local ring at a closed point of a nonsingular fourfold. Let
`V ⊂ X` be the union of the two planes `x = y = 0` and `z = w = 0`, so that its ideal is
`I = (xz, xw, yz, yw)`, and let `W ⊂ X` be the plane with ideal `J = (x - z, y - w)`. The two
subvarieties meet properly in the single point `x = y = z = w = 0`.

The scheme-theoretic intersection `V ∩ W` has length `3`: the sum `I + J` is `J + 𝔪 ^ 2`, so the
quotient is `ℂ[[x, y]] / (x, y) ^ 2`, and the filtration by `𝔪` exhibits the three composition
factors. The intersection multiplicity given by the Tor formula is `2`, because formally `V` is
the union of two smooth planes each meeting `W` transversally. So the naive count `3` is wrong,
and the discrepancy must come from the higher Tor modules: indeed `Tor_1^A(A ⧸ J, A ⧸ I)` is
nonzero, witnessed by the class of `xw - yz`, an element of `I ∩ J` that does not lie in `I · J`.

## Main definitions

* `Stacks.Intersection.TwoPlanes.unionOfPlanes`: the ideal `(xz, xw, yz, yw)` of `V`.
* `Stacks.Intersection.TwoPlanes.diagonalPlane`: the ideal `(x - z, y - w)` of `W`.
* `Stacks.Intersection.TwoPlanes.linearFormVanishing`: the ideal of power series with vanishing
  constant term whose linear part is annihilated by a given linear form.

## Main results

* `Stacks.Intersection.TwoPlanes.length_quotient_sup_eq_three`: the length of
  `ℂ[[x, y, z, w]] / (xz, xw, yz, yw, x - z, y - w)` is `3`, which is the length of
  `Tor_0^A(A ⧸ J, A ⧸ I)`.
* `Stacks.Intersection.TwoPlanes.not_isZero_tor_one`: `Tor_1^A(A ⧸ J, A ⧸ I)` is nonzero, so the
  alternating sum of the lengths of the Tor modules is not the degree-zero term alone.

## Implementation notes

Both results are proved by hand in the power series ring rather than deduced from a statement
about an abstract regular local ring, since the two ideals are given by explicit generators and
all the non-membership facts reduce to coefficient computations.

The length is computed from a three-step filtration. The two intermediate steps adjoin an
element `a` to an ideal `L` with `𝔪 a ⊆ L` and `a ∉ L`; then the ideal `{r | r a ∈ L}` is
proper and contains `𝔪`, hence equals `𝔪`, so the step contributes one composition factor
(`length_quotient_eq_one_add`). The two non-membership facts are read off from two linear forms
on `𝔪 / 𝔪 ^ 2` vanishing on both ideals.

The nonvanishing of `Tor_1` uses the identification of `Tor_1(M, N)` with the kernel of
`ker φ ⊗ N → A ^ t ⊗ N` attached to a finite free presentation `φ : A ^ t ↠ M`
(`torOneIsoKerApp`). Here `M = A ⧸ J` is cyclic, so `t = 1` and `ker φ` is `J` sitting inside
`A ^ 1`; nonvanishing becomes the failure of `J ⊗ (A ⧸ I) → A ⊗ (A ⧸ I)` to be injective, and
`xw - yz` provides the witness because it lies in `J` and in `I` but not in `I · J`.

## References

* [Stacks Project, Tag 0B2S](https://stacks.math.columbia.edu/tag/0B2S)
* [Stacks Project, Tag 0B1I](https://stacks.math.columbia.edu/tag/0B1I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing MvPowerSeries
open scoped TensorProduct

namespace Stacks.Intersection.TwoPlanes

/-! ### Linear coefficients of a power series -/

/-- The Leibniz rule for the coefficient of a degree-one monomial: it is a derivation at the
constant terms. -/
theorem coeff_single_one_mul {n : ℕ} {R : Type*} [CommRing R] (i : Fin n)
    (u v : MvPowerSeries (Fin n) R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (u * v) =
      MvPowerSeries.constantCoeff u * MvPowerSeries.coeff (Finsupp.single i 1) v +
        MvPowerSeries.coeff (Finsupp.single i 1) u * MvPowerSeries.constantCoeff v := by
  have key : ∀ g : MvPowerSeries (Fin n) R,
      MvPowerSeries.coeff (Finsupp.single i 1) g =
        MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := R) i g) := by
    intro g
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp
  rw [key, key, key, (MvPowerSeries.pderiv (R := R) i).leibniz]
  simp [mul_comm]

/-- The coefficient of `x_i` in the variable `x_j` is `1` if `i = j` and `0` otherwise. -/
theorem coeff_single_one_X {n : ℕ} {R : Type*} [CommRing R] (i j : Fin n) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries (Fin n) R) =
      if j = i then 1 else 0 := by
  classical
  by_cases h : j = i
  · subst h; simp
  · have hne : (Finsupp.single i 1 : Fin n →₀ ℕ) ≠ Finsupp.single j 1 := by
      intro hc
      rw [Finsupp.single_eq_single_iff] at hc
      rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h h1.symm
      · exact one_ne_zero h1
    simp [MvPowerSeries.coeff_X, hne, h]

/-- Every variable lies in the maximal ideal of `k[[x_0, …, x_{n-1}]]`. -/
theorem X_mem_maximalIdeal {n : ℕ} {k : Type*} [Field k] (i : Fin n) :
    (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ∈ maximalIdeal (MvPowerSeries (Fin n) k) := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X k n]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The maximal ideal of `ℂ[[x, y, z, w]]`, with the four variables listed explicitly. -/
theorem maximalIdeal_eq_span_four :
    maximalIdeal (MvPowerSeries (Fin 4) ℂ) =
      Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 1, MvPowerSeries.X 2, MvPowerSeries.X 3} := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X ℂ 4]
  congr 1
  ext u
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (h | h | h | h) <;> exact ⟨_, h.symm⟩

/-- The ideal of those power series with vanishing constant term whose linear part is annihilated
by the linear form `t`, that is `∑ i, t i * (coefficient of x_i) = 0`. -/
def linearFormVanishing {n : ℕ} {k : Type*} [Field k] (t : Fin n → k) :
    Ideal (MvPowerSeries (Fin n) k) where
  carrier := {g | MvPowerSeries.constantCoeff g = 0 ∧
    ∑ i, t i * MvPowerSeries.coeff (Finsupp.single i 1) g = 0}
  add_mem' := by
    intro g h hg hh
    refine ⟨by simp [hg.1, hh.1], ?_⟩
    have : ∀ i : Fin n, t i * MvPowerSeries.coeff (Finsupp.single i 1) (g + h) =
        t i * MvPowerSeries.coeff (Finsupp.single i 1) g +
          t i * MvPowerSeries.coeff (Finsupp.single i 1) h := by
      intro i; rw [map_add]; ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, hg.2, hh.2, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c g hg
    refine ⟨by simp [hg.1], ?_⟩
    have : ∀ i : Fin n, t i * MvPowerSeries.coeff (Finsupp.single i 1) (c • g) =
        MvPowerSeries.constantCoeff c * (t i * MvPowerSeries.coeff (Finsupp.single i 1) g) := by
      intro i
      rw [smul_eq_mul, coeff_single_one_mul, hg.1, mul_zero, add_zero]
      ring
    rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, hg.2, mul_zero]

/-- Membership in `linearFormVanishing t` is the pair of conditions defining it. -/
@[simp]
theorem mem_linearFormVanishing_iff {n : ℕ} {k : Type*} [Field k] {t : Fin n → k}
    {g : MvPowerSeries (Fin n) k} :
    g ∈ linearFormVanishing t ↔ MvPowerSeries.constantCoeff g = 0 ∧
      ∑ i, t i * MvPowerSeries.coeff (Finsupp.single i 1) g = 0 :=
  Iff.rfl

/-! ### The two ideals -/

/-- The ideal `(xz, xw, yz, yw)` of `ℂ[[x, y, z, w]]`: the ideal of the union of the two planes
`x = y = 0` and `z = w = 0`, which is the intersection `(x, y) ∩ (z, w)`. -/
def unionOfPlanes : Ideal (MvPowerSeries (Fin 4) ℂ) :=
  Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 2, MvPowerSeries.X 0 * MvPowerSeries.X 3,
    MvPowerSeries.X 1 * MvPowerSeries.X 2, MvPowerSeries.X 1 * MvPowerSeries.X 3}

/-- The ideal `(x - z, y - w)` of `ℂ[[x, y, z, w]]`: the ideal of the plane `x = z`, `y = w`. -/
def diagonalPlane : Ideal (MvPowerSeries (Fin 4) ℂ) :=
  Ideal.span {MvPowerSeries.X 0 - MvPowerSeries.X 2, MvPowerSeries.X 1 - MvPowerSeries.X 3}

/-- The quadric `xz` is a generator of the ideal of the union of the two planes. -/
theorem mul_mem_unionOfPlanes_zero_two :
    (MvPowerSeries.X 0 * MvPowerSeries.X 2 : MvPowerSeries (Fin 4) ℂ) ∈ unionOfPlanes :=
  Ideal.subset_span (by simp)

/-- The quadric `xw` is a generator of the ideal of the union of the two planes. -/
theorem mul_mem_unionOfPlanes_zero_three :
    (MvPowerSeries.X 0 * MvPowerSeries.X 3 : MvPowerSeries (Fin 4) ℂ) ∈ unionOfPlanes :=
  Ideal.subset_span (by simp)

/-- The quadric `yz` is a generator of the ideal of the union of the two planes. -/
theorem mul_mem_unionOfPlanes_one_two :
    (MvPowerSeries.X 1 * MvPowerSeries.X 2 : MvPowerSeries (Fin 4) ℂ) ∈ unionOfPlanes :=
  Ideal.subset_span (by simp)

/-- The quadric `yw` is a generator of the ideal of the union of the two planes. -/
theorem mul_mem_unionOfPlanes_one_three :
    (MvPowerSeries.X 1 * MvPowerSeries.X 3 : MvPowerSeries (Fin 4) ℂ) ∈ unionOfPlanes :=
  Ideal.subset_span (by simp)

/-- The linear form `x - z` is a generator of the ideal of the plane `x = z`, `y = w`. -/
theorem sub_mem_diagonalPlane_zero_two :
    (MvPowerSeries.X 0 - MvPowerSeries.X 2 : MvPowerSeries (Fin 4) ℂ) ∈ diagonalPlane :=
  Ideal.subset_span (by simp)

/-- The linear form `y - w` is a generator of the ideal of the plane `x = z`, `y = w`. -/
theorem sub_mem_diagonalPlane_one_three :
    (MvPowerSeries.X 1 - MvPowerSeries.X 3 : MvPowerSeries (Fin 4) ℂ) ∈ diagonalPlane :=
  Ideal.subset_span (by simp)

/-- The ideal of the union of the two planes is generated by quadrics, so it lies in `𝔪 ^ 2`. -/
theorem unionOfPlanes_le_maximalIdeal_sq :
    unionOfPlanes ≤ maximalIdeal (MvPowerSeries (Fin 4) ℂ) ^ 2 := by
  rw [unionOfPlanes, Ideal.span_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rw [pow_two]
  rcases hu with h | h | h | h <;> subst h <;>
    exact Ideal.mul_mem_mul (X_mem_maximalIdeal _) (X_mem_maximalIdeal _)

/-- The ideal of the plane `x = z`, `y = w` lies in the maximal ideal. -/
theorem diagonalPlane_le_maximalIdeal :
    diagonalPlane ≤ maximalIdeal (MvPowerSeries (Fin 4) ℂ) := by
  rw [diagonalPlane, Ideal.span_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with h | h <;> subst h <;>
    exact Ideal.sub_mem _ (X_mem_maximalIdeal _) (X_mem_maximalIdeal _)

/-- The sum of the two ideals lies in the maximal ideal. -/
theorem sup_le_maximalIdeal :
    unionOfPlanes ⊔ diagonalPlane ≤ maximalIdeal (MvPowerSeries (Fin 4) ℂ) :=
  sup_le (unionOfPlanes_le_maximalIdeal_sq.trans
    (Ideal.pow_le_self (by norm_num))) diagonalPlane_le_maximalIdeal

/-! ### Two linear forms vanishing on both ideals -/

/-- Every generator of the ideal of the union of the two planes is a quadric, hence has
vanishing constant and linear coefficients: the ideal lies in `linearFormVanishing t` for every
linear form `t`. -/
theorem unionOfPlanes_le_linearFormVanishing (t : Fin 4 → ℂ) :
    unionOfPlanes ≤ linearFormVanishing t := by
  have hquad : ∀ i j : Fin 4,
      (MvPowerSeries.X i * MvPowerSeries.X j : MvPowerSeries (Fin 4) ℂ) ∈
        linearFormVanishing t := by
    intro i j
    refine ⟨by simp, ?_⟩
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [coeff_single_one_mul, coeff_single_one_X, coeff_single_one_X]
    simp
  rw [unionOfPlanes, Ideal.span_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with h | h | h | h <;> subst h <;> exact hquad _ _

/-- If the linear form `t` is constant on the two pairs of variables `{x, z}` and `{y, w}`, it
kills the linear parts of `x - z` and `y - w`, so the ideal of the plane `x = z`, `y = w` lies
in `linearFormVanishing t`. -/
theorem diagonalPlane_le_linearFormVanishing {t : Fin 4 → ℂ} (h02 : t 0 = t 2)
    (h13 : t 1 = t 3) : diagonalPlane ≤ linearFormVanishing t := by
  have key : ∀ i j : Fin 4, t i = t j →
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 4) ℂ) ∈
        linearFormVanishing t := by
    intro i j hij
    refine ⟨by simp, ?_⟩
    have hterm : ∀ l : Fin 4,
        t l * MvPowerSeries.coeff (Finsupp.single l 1)
            (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 4) ℂ) =
          (if i = l then t l else 0) - (if j = l then t l else 0) := by
      intro l
      rw [map_sub, coeff_single_one_X, coeff_single_one_X]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_sub_distrib]
    simp [hij]
  rw [diagonalPlane, Ideal.span_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with h | h <;> subst h
  · exact key 0 2 h02
  · exact key 1 3 h13

/-- A variable on which the linear form `t` does not vanish lies outside every ideal contained in
`linearFormVanishing t`. -/
private theorem X_notMem_of_le_linearFormVanishing {t : Fin 4 → ℂ}
    {I : Ideal (MvPowerSeries (Fin 4) ℂ)} (hle : I ≤ linearFormVanishing t) {i : Fin 4}
    (hi : t i ≠ 0) : (MvPowerSeries.X i : MvPowerSeries (Fin 4) ℂ) ∉ I := by
  classical
  intro hmem
  have := (mem_linearFormVanishing_iff (t := t)).1 (hle hmem) |>.2
  rw [Finset.sum_congr rfl fun l _ => by rw [coeff_single_one_X]] at this
  exact hi (by simpa using this)

/-- The linear form `x ↦ x_0 + x_2` on the cotangent space vanishes on both ideals and on the
variable `y`, but not on the variable `x`. -/
theorem X_zero_notMem_sup_sup_span_X_one :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 4) ℂ) ∉
      unionOfPlanes ⊔ diagonalPlane ⊔
        Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)} := by
  classical
  set t : Fin 4 → ℂ := fun i => if i = 0 ∨ i = 2 then 1 else 0 with ht
  have hle : unionOfPlanes ⊔ diagonalPlane ⊔
      Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)} ≤ linearFormVanishing t := by
    refine sup_le (sup_le (unionOfPlanes_le_linearFormVanishing t)
      (diagonalPlane_le_linearFormVanishing (by simp [ht]) (by simp [ht]))) ?_
    rw [Ideal.span_le]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    refine ⟨by simp, ?_⟩
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [coeff_single_one_X]
    by_cases h : (1 : Fin 4) = l
    · subst h; simp [ht]
    · simp [h]
  exact X_notMem_of_le_linearFormVanishing hle (by simp [ht])

/-- The linear form `x ↦ x_1 + x_3` on the cotangent space vanishes on both ideals but not on the
variable `y`. -/
theorem X_one_notMem_sup :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ) ∉ unionOfPlanes ⊔ diagonalPlane := by
  classical
  set t : Fin 4 → ℂ := fun i => if i = 1 ∨ i = 3 then 1 else 0 with ht
  have hle : unionOfPlanes ⊔ diagonalPlane ≤ linearFormVanishing t :=
    sup_le (unionOfPlanes_le_linearFormVanishing t)
      (diagonalPlane_le_linearFormVanishing (by simp [ht]) (by simp [ht]))
  exact X_notMem_of_le_linearFormVanishing hle (by simp [ht])

/-! ### Products of the variables with `x` and with `y` -/

/-- To show that `𝔪 · (X a)` lies in an ideal, it suffices to check the products of `X a` with the
four variables. -/
private theorem maximalIdeal_mul_span_X_le {a : Fin 4} {S : Ideal (MvPowerSeries (Fin 4) ℂ)}
    (h0 : (MvPowerSeries.X 0 * MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ) ∈ S)
    (h1 : (MvPowerSeries.X 1 * MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ) ∈ S)
    (h2 : (MvPowerSeries.X 2 * MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ) ∈ S)
    (h3 : (MvPowerSeries.X 3 * MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ) ∈ S) :
    maximalIdeal (MvPowerSeries (Fin 4) ℂ) *
      Ideal.span {(MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ)} ≤ S := by
  rw [maximalIdeal_eq_span_four, Ideal.span_mul_span, Ideal.span_le]
  rintro _ ⟨s, hs, v, hv, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hv
  subst hv
  rcases hs with rfl | rfl | rfl | rfl <;> assumption

/-- The product `X c * X a` lies in the sum of the two ideals when `X c - X d` lies in the ideal of
the plane and `X a * X d` lies in the ideal of the union. -/
private theorem X_mul_X_mem_sup {a c d : Fin 4}
    (hd : (MvPowerSeries.X c - MvPowerSeries.X d : MvPowerSeries (Fin 4) ℂ) ∈ diagonalPlane)
    (hu : (MvPowerSeries.X a * MvPowerSeries.X d : MvPowerSeries (Fin 4) ℂ) ∈ unionOfPlanes) :
    (MvPowerSeries.X c * MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ) ∈
      unionOfPlanes ⊔ diagonalPlane := by
  have hid : (MvPowerSeries.X c * MvPowerSeries.X a : MvPowerSeries (Fin 4) ℂ) =
      MvPowerSeries.X a * (MvPowerSeries.X c - MvPowerSeries.X d) +
        MvPowerSeries.X a * MvPowerSeries.X d := by ring
  rw [hid]
  exact Ideal.add_mem _ (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ hd))
    (Submodule.mem_sup_left hu)

/-- Products of the variables with `x` lie in the sum of the two ideals. -/
theorem maximalIdeal_mul_span_X_zero_le :
    maximalIdeal (MvPowerSeries (Fin 4) ℂ) *
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 4) ℂ)} ≤
      unionOfPlanes ⊔ diagonalPlane :=
  maximalIdeal_mul_span_X_le (X_mul_X_mem_sup sub_mem_diagonalPlane_zero_two
      mul_mem_unionOfPlanes_zero_two)
    (X_mul_X_mem_sup sub_mem_diagonalPlane_one_three mul_mem_unionOfPlanes_zero_three)
    (Submodule.mem_sup_left (by rw [mul_comm]; exact mul_mem_unionOfPlanes_zero_two))
    (Submodule.mem_sup_left (by rw [mul_comm]; exact mul_mem_unionOfPlanes_zero_three))

/-- Products of the variables with `y` lie in the sum of the two ideals. -/
theorem maximalIdeal_mul_span_X_one_le :
    maximalIdeal (MvPowerSeries (Fin 4) ℂ) *
        Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)} ≤
      unionOfPlanes ⊔ diagonalPlane :=
  maximalIdeal_mul_span_X_le (X_mul_X_mem_sup sub_mem_diagonalPlane_zero_two
      mul_mem_unionOfPlanes_one_two)
    (X_mul_X_mem_sup sub_mem_diagonalPlane_one_three mul_mem_unionOfPlanes_one_three)
    (Submodule.mem_sup_left (by rw [mul_comm]; exact mul_mem_unionOfPlanes_one_two))
    (Submodule.mem_sup_left (by rw [mul_comm]; exact mul_mem_unionOfPlanes_one_three))

/-- Adjoining `x` and `y` to the sum of the two ideals gives the maximal ideal: modulo the ideal
of the plane `x = z`, `y = w` the variables `z` and `w` become `x` and `y`. -/
theorem sup_sup_span_X_one_sup_span_X_zero_eq_maximalIdeal :
    unionOfPlanes ⊔ diagonalPlane ⊔ Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)} ⊔
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 4) ℂ)} =
      maximalIdeal (MvPowerSeries (Fin 4) ℂ) := by
  refine le_antisymm (sup_le (sup_le sup_le_maximalIdeal ?_) ?_) ?_
  · rw [Ideal.span_le]; intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu
    exact X_mem_maximalIdeal 1
  · rw [Ideal.span_le]; intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu
    exact X_mem_maximalIdeal 0
  · rw [maximalIdeal_eq_span_four, Ideal.span_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu | hu | hu <;> subst hu
    · exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))
    · have hid : (MvPowerSeries.X 2 : MvPowerSeries (Fin 4) ℂ) =
          MvPowerSeries.X 0 - (MvPowerSeries.X 0 - MvPowerSeries.X 2) := by ring
      rw [hid]
      exact Ideal.sub_mem _ (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.mem_sup_right sub_mem_diagonalPlane_zero_two)))
    · have hid : (MvPowerSeries.X 3 : MvPowerSeries (Fin 4) ℂ) =
          MvPowerSeries.X 1 - (MvPowerSeries.X 1 - MvPowerSeries.X 3) := by ring
      rw [hid]
      exact Ideal.sub_mem _
        (Submodule.mem_sup_left (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)))
        (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.mem_sup_right sub_mem_diagonalPlane_one_three)))

/-! ### The length of the scheme-theoretic intersection -/

/-- The residue field of a local ring has length one as a module over the ring. -/
private theorem length_quotient_maximalIdeal_eq_one (A : Type*) [CommRing A] [IsLocalRing A] :
    Module.length A (A ⧸ maximalIdeal A) = 1 := by
  have : IsSimpleModule A (A ⧸ maximalIdeal A) :=
    (isSimpleModule_iff_quot_maximal (R := A)).2
      ⟨maximalIdeal A, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  exact Module.length_eq_one A _

/-- One step of a filtration of a local ring by ideals. If `a` is an element outside an ideal `L`
with `𝔪 a ⊆ L`, then the quotient by `L` has exactly one more composition factor than the
quotient by `L + (a)`: the ideal `{r | r a ∈ L}` is proper and contains `𝔪`, hence is `𝔪`, so
the image of `(a)` in `A ⧸ L` is the residue field. -/
theorem length_quotient_eq_one_add {A : Type*} [CommRing A] [IsLocalRing A] (L : Ideal A) (a : A)
    (ha : a ∉ L) (hma : ∀ r ∈ maximalIdeal A, r * a ∈ L) :
    Module.length A (A ⧸ L) = 1 + Module.length A (A ⧸ (L ⊔ Ideal.span {a})) := by
  classical
  set f : A →ₗ[A] (A ⧸ (L : Submodule A A)) :=
    (Submodule.mkQ (L : Submodule A A)) ∘ₗ (LinearMap.toSpanSingleton A A a) with hf
  have hker : LinearMap.ker f = (maximalIdeal A : Submodule A A) := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · intro htop
      have h1 : (1 : A) ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
      simp only [hf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        one_smul] at h1
      exact ha h1
    · intro r hr
      simp only [hf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      exact hma r hr
  have hrange : LinearMap.range f = Submodule.map (Submodule.mkQ (L : Submodule A A))
      (Ideal.span {a} : Submodule A A) := by
    rw [hf, LinearMap.range_comp]
    congr 1
    exact (LinearMap.span_singleton_eq_range A A a).symm
  have hlen1 : Module.length A (LinearMap.range f) = 1 := by
    have e : (A ⧸ LinearMap.ker f) ≃ₗ[A] LinearMap.range f := f.quotKerEquivRange
    rw [← e.length_eq, hker]
    exact length_quotient_maximalIdeal_eq_one A
  have hquot : Module.length A ((A ⧸ (L : Submodule A A)) ⧸ LinearMap.range f)
      = Module.length A (A ⧸ (L ⊔ Ideal.span {a})) := by
    rw [hrange]
    exact (Submodule.quotientQuotientEquivQuotientSup
      (L : Submodule A A) (Ideal.span {a} : Submodule A A)).length_eq
  rw [Module.length_eq_add_of_exact (R := A) (M := A ⧸ (L : Submodule A A))
    (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _), hlen1, hquot]

/-- **The naive count of the intersection of the two planes with the plane `x = z`, `y = w`.**
The length of `ℂ[[x, y, z, w]] / (xz, xw, yz, yw, x - z, y - w)` is `3`: the sum of the two
ideals is `(x - z, y - w) + 𝔪 ^ 2`, whose quotient is `ℂ[[x, y]] / (x, y) ^ 2`. This is the
length of `Tor_0` in the Tor formula for the intersection multiplicity, and it differs from the
true multiplicity `2`. -/
@[stacks 0B2S "the length-3 computation of the example: the naive count for the pair of ideals"]
theorem length_quotient_sup_eq_three :
    Module.length (MvPowerSeries (Fin 4) ℂ)
      (MvPowerSeries (Fin 4) ℂ ⧸ (unionOfPlanes ⊔ diagonalPlane)) = 3 := by
  have hstep1 : Module.length (MvPowerSeries (Fin 4) ℂ)
      (MvPowerSeries (Fin 4) ℂ ⧸ (unionOfPlanes ⊔ diagonalPlane)) =
      1 + Module.length (MvPowerSeries (Fin 4) ℂ)
        (MvPowerSeries (Fin 4) ℂ ⧸ (unionOfPlanes ⊔ diagonalPlane ⊔
          Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)})) :=
    length_quotient_eq_one_add _ _ X_one_notMem_sup fun r hr =>
      maximalIdeal_mul_span_X_one_le (Ideal.mul_mem_mul hr (Ideal.mem_span_singleton_self _))
  have hstep2 : Module.length (MvPowerSeries (Fin 4) ℂ)
      (MvPowerSeries (Fin 4) ℂ ⧸ (unionOfPlanes ⊔ diagonalPlane ⊔
        Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)})) =
      1 + Module.length (MvPowerSeries (Fin 4) ℂ)
        (MvPowerSeries (Fin 4) ℂ ⧸ (unionOfPlanes ⊔ diagonalPlane ⊔
          Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)} ⊔
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 4) ℂ)})) :=
    length_quotient_eq_one_add _ _ X_zero_notMem_sup_sup_span_X_one fun r hr =>
      Submodule.mem_sup_left
        (maximalIdeal_mul_span_X_zero_le (Ideal.mul_mem_mul hr (Ideal.mem_span_singleton_self _)))
  have hlast : Module.length (MvPowerSeries (Fin 4) ℂ)
      (MvPowerSeries (Fin 4) ℂ ⧸ (unionOfPlanes ⊔ diagonalPlane ⊔
        Ideal.span {(MvPowerSeries.X 1 : MvPowerSeries (Fin 4) ℂ)} ⊔
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 4) ℂ)})) = 1 := by
    rw [sup_sup_span_X_one_sup_span_X_zero_eq_maximalIdeal]
    exact length_quotient_maximalIdeal_eq_one _
  rw [hstep1, hstep2, hlast]
  rfl

/-! ### The witness for the nonvanishing of `Tor_1` -/

/-- The quadric `xw - yz` lies in the ideal of the union of the two planes. -/
theorem crossTerm_mem_unionOfPlanes :
    (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
      MvPowerSeries (Fin 4) ℂ) ∈ unionOfPlanes :=
  Ideal.sub_mem _ mul_mem_unionOfPlanes_zero_three mul_mem_unionOfPlanes_one_two

/-- The quadric `xw - yz` lies in the ideal of the plane `x = z`, `y = w`, because
`xw - yz = y (x - z) - x (y - w)`. -/
theorem crossTerm_mem_diagonalPlane :
    (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
      MvPowerSeries (Fin 4) ℂ) ∈ diagonalPlane := by
  have hid : (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
      MvPowerSeries (Fin 4) ℂ) =
      MvPowerSeries.X 1 * (MvPowerSeries.X 0 - MvPowerSeries.X 2) -
        MvPowerSeries.X 0 * (MvPowerSeries.X 1 - MvPowerSeries.X 3) := by ring
  rw [hid]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ sub_mem_diagonalPlane_zero_two)
    (Ideal.mul_mem_left _ _ sub_mem_diagonalPlane_one_three)

/-- The coefficient of the monomial `xw` in `xw - yz` is `1`. -/
theorem coeff_crossTerm :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1)
      (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
        MvPowerSeries (Fin 4) ℂ) = 1 := by
  classical
  have h1 : (MvPowerSeries.X 0 * MvPowerSeries.X 3 : MvPowerSeries (Fin 4) ℂ) =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, mul_one]
  have h2 : (MvPowerSeries.X 1 * MvPowerSeries.X 2 : MvPowerSeries (Fin 4) ℂ) =
      MvPowerSeries.monomial (Finsupp.single (1 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, mul_one]
  have hne : ¬ (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 =
      Finsupp.single (1 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) := by
    intro h
    have := congrArg (fun g => g (0 : Fin 4)) h
    simp at this
  rw [map_sub, h1, h2, MvPowerSeries.coeff_monomial_same, MvPowerSeries.coeff_monomial]
  simp [hne]

/-- The product of the two ideals lies in `𝔪 ^ 3`. -/
theorem unionOfPlanes_mul_diagonalPlane_le :
    unionOfPlanes * diagonalPlane ≤ maximalIdeal (MvPowerSeries (Fin 4) ℂ) ^ 3 := by
  calc unionOfPlanes * diagonalPlane
      ≤ maximalIdeal (MvPowerSeries (Fin 4) ℂ) ^ 2 * maximalIdeal (MvPowerSeries (Fin 4) ℂ) :=
        Ideal.mul_mono unionOfPlanes_le_maximalIdeal_sq diagonalPlane_le_maximalIdeal
    _ = maximalIdeal (MvPowerSeries (Fin 4) ℂ) ^ 3 := by rw [← pow_succ]

/-- **The quadric `xw - yz` lies in the intersection of the two ideals but not in their
product.** Since the product is generated by cubics it lies in `𝔪 ^ 3`, while `xw - yz` has a
nonzero coefficient in total degree `2`. -/
theorem crossTerm_notMem_mul :
    (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
      MvPowerSeries (Fin 4) ℂ) ∉ unionOfPlanes * diagonalPlane := by
  intro hmem
  have hdeg : (∑ i : Fin 4,
      (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 : Fin 4 →₀ ℕ) i) < 3 := by
    simp [Fin.sum_univ_four]
  have hzero := Stacks.MvPowerSeries.RegularParameters.coeff_eq_zero_of_mem_pow_maximalIdeal
    (unionOfPlanes_mul_diagonalPlane_le hmem)
    (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) hdeg
  rw [coeff_crossTerm] at hzero
  exact one_ne_zero hzero

/-! ### `Tor_1` is nonzero -/

/-- The free presentation of `A ⧸ (x - z, y - w)` by `A ^ 1`. -/
def diagonalPlanePresentation :
    (Fin 1 → MvPowerSeries (Fin 4) ℂ) →ₗ[MvPowerSeries (Fin 4) ℂ]
      (MvPowerSeries (Fin 4) ℂ ⧸ diagonalPlane) :=
  (Submodule.mkQ (diagonalPlane : Submodule (MvPowerSeries (Fin 4) ℂ) (MvPowerSeries (Fin 4) ℂ)))
    ∘ₗ LinearMap.proj 0

/-- The presentation is surjective: the quotient is generated by the class of `1`. -/
theorem diagonalPlanePresentation_surjective :
    Function.Surjective diagonalPlanePresentation := by
  intro u
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
    (diagonalPlane : Submodule (MvPowerSeries (Fin 4) ℂ) (MvPowerSeries (Fin 4) ℂ)) u
  exact ⟨fun _ => a, rfl⟩

/-- The kernel of the presentation is the ideal `(x - z, y - w)` sitting in `A ^ 1`. -/
theorem mem_ker_diagonalPlanePresentation_iff {v : Fin 1 → MvPowerSeries (Fin 4) ℂ} :
    v ∈ LinearMap.ker diagonalPlanePresentation ↔ v 0 ∈ diagonalPlane := by
  simp [diagonalPlanePresentation, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The natural transformation of `torOneIsoKerApp` is, on components, the inclusion of the
kernel of a presentation tensored with the second argument. -/
theorem torBaseNT_app_hom {A : Type} [CommRing A] (M : ModuleCat A) {t : ℕ}
    (φ : (Fin t → A) →ₗ[A] M) (N : ModuleCat A) :
    ((torBaseNT M φ).app N).hom = LinearMap.rTensor N (LinearMap.ker φ).subtype := rfl

/-- `Tor_1(M, N)` is nonzero as soon as the inclusion of the kernel of a finite free presentation
of `M` fails to stay injective after tensoring with `N`. -/
theorem not_isZero_tor_one_of_not_injective {A : Type} [CommRing A] (M : ModuleCat A) {t : ℕ}
    (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ) (N : ModuleCat A)
    (hinj : ¬ Function.Injective
      (LinearMap.rTensor (N : Type) (LinearMap.ker φ).subtype)) :
    ¬ IsZero (((Tor (ModuleCat A) 1).obj M).obj N) := by
  intro hz
  have h1 : IsZero (kernel ((torBaseNT M φ).app N)) :=
    hz.of_iso (torOneIsoKerApp M φ hφ N).symm
  have h2 : Mono ((torBaseNT M φ).app N) := (Preadditive.mono_iff_isZero_kernel _).2 h1
  rw [ModuleCat.mono_iff_injective] at h2
  exact hinj (by rw [← torBaseNT_app_hom M φ N]; exact h2)

/-- The witness `xw - yz`, as an element of the kernel of the presentation of
`A ⧸ (x - z, y - w)`. -/
def crossTermKer : LinearMap.ker diagonalPlanePresentation :=
  ⟨fun _ => MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2,
    mem_ker_diagonalPlanePresentation_iff.2 crossTerm_mem_diagonalPlane⟩

/-- An element of `I • ⊤` inside the kernel of the presentation has its coordinate in `I · J`. -/
theorem coord_mem_mul_of_mem_smul_top
    {v : LinearMap.ker diagonalPlanePresentation}
    (hv : v ∈ unionOfPlanes • (⊤ : Submodule (MvPowerSeries (Fin 4) ℂ)
      (LinearMap.ker diagonalPlanePresentation))) :
    (v : Fin 1 → MvPowerSeries (Fin 4) ℂ) 0 ∈ unionOfPlanes * diagonalPlane := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro r hr n _
    have hn : (n : Fin 1 → MvPowerSeries (Fin 4) ℂ) 0 ∈ diagonalPlane :=
      mem_ker_diagonalPlanePresentation_iff.1 n.2
    simpa using Ideal.mul_mem_mul hr hn
  · intro p q hp hq
    simpa using Ideal.add_mem _ hp hq

/-- Acting by a ring element on the class of `1` in a quotient gives the class of that element. -/
theorem smul_mk_one {A : Type*} [CommRing A] (I : Ideal A) (c : A) :
    c • (Ideal.Quotient.mk I (1 : A)) = Ideal.Quotient.mk I c := by
  simpa using ((Submodule.mkQ (I : Submodule A A)).map_smul c 1).symm

/-- The witness `xw - yz`, as an element of `J ⊗ (A ⧸ I)`. -/
def crossTermTensor :
    (↥(LinearMap.ker diagonalPlanePresentation)) ⊗[MvPowerSeries (Fin 4) ℂ]
      (MvPowerSeries (Fin 4) ℂ ⧸ unionOfPlanes) :=
  crossTermKer ⊗ₜ Ideal.Quotient.mk unionOfPlanes (1 : MvPowerSeries (Fin 4) ℂ)

/-- The witness is nonzero in `J ⊗ (A ⧸ I)`: under the identification of that tensor product
with `J / I J`, it is the class of `xw - yz`, which is not in `I · J`. -/
theorem crossTermTensor_ne_zero : crossTermTensor ≠ 0 := by
  intro hzero
  rw [crossTermTensor] at hzero
  have he := congrArg (TensorProduct.tensorQuotEquivQuotSMul
    (LinearMap.ker diagonalPlanePresentation) unionOfPlanes) hzero
  rw [map_zero, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
    Submodule.Quotient.mk_eq_zero] at he
  exact crossTerm_notMem_mul (coord_mem_mul_of_mem_smul_top he)

/-- Tensoring the inclusion `J ↪ A` with `A ⧸ I` is not injective: the class of `xw - yz` is a
nonzero element of `J ⊗ (A ⧸ I)` which dies in `A ⊗ (A ⧸ I)`, since `xw - yz ∈ I`. -/
theorem not_injective_rTensor :
    ¬ Function.Injective (LinearMap.rTensor
      (MvPowerSeries (Fin 4) ℂ ⧸ unionOfPlanes : Type)
      (LinearMap.ker diagonalPlanePresentation).subtype) := by
  intro hinj
  refine crossTermTensor_ne_zero (hinj ?_)
  rw [map_zero, crossTermTensor, LinearMap.rTensor_tmul]
  have hsmul : ((crossTermKer : Fin 1 → MvPowerSeries (Fin 4) ℂ)) =
      (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
          MvPowerSeries (Fin 4) ℂ) • (fun _ => (1 : MvPowerSeries (Fin 4) ℂ)) := by
    funext i; simp [crossTermKer]
  rw [Submodule.subtype_apply, hsmul, TensorProduct.smul_tmul]
  have hz : (MvPowerSeries.X 0 * MvPowerSeries.X 3 - MvPowerSeries.X 1 * MvPowerSeries.X 2 :
      MvPowerSeries (Fin 4) ℂ) • (Ideal.Quotient.mk unionOfPlanes
        (1 : MvPowerSeries (Fin 4) ℂ)) = 0 := by
    rw [smul_mk_one, Ideal.Quotient.eq_zero_iff_mem]
    exact crossTerm_mem_unionOfPlanes
  rw [hz, TensorProduct.tmul_zero]

/-- **The higher Tor modules are necessary in the Tor formula for intersection multiplicities.**
For `V` the union of the two planes `x = y = 0` and `z = w = 0` in `X` a nonsingular fourfold and
`W` the plane `x = z`, `y = w`, the module `Tor_1^A(𝒪_W, 𝒪_V)` at the point of intersection is
nonzero. Hence the alternating sum of the lengths of the Tor modules, which is the intersection
multiplicity `e(X, V · W, p) = 2`, is not the degree-zero term
`length 𝒪_{V ∩ W, p} = 3` on its own. -/
@[stacks 0B2S "higher Tors are necessary: Tor_1 of the two quotients is nonzero, so the \
alternating sum is not its degree-zero term; the value e = 2 itself is not computed here"]
theorem not_isZero_tor_one :
    ¬ IsZero (((Tor (ModuleCat (MvPowerSeries (Fin 4) ℂ)) 1).obj
        (ModuleCat.of (MvPowerSeries (Fin 4) ℂ)
          (MvPowerSeries (Fin 4) ℂ ⧸ diagonalPlane))).obj
      (ModuleCat.of (MvPowerSeries (Fin 4) ℂ)
        (MvPowerSeries (Fin 4) ℂ ⧸ unionOfPlanes))) :=
  not_isZero_tor_one_of_not_injective
    (ModuleCat.of (MvPowerSeries (Fin 4) ℂ) (MvPowerSeries (Fin 4) ℂ ⧸ diagonalPlane))
    diagonalPlanePresentation diagonalPlanePresentation_surjective
    (ModuleCat.of (MvPowerSeries (Fin 4) ℂ) (MvPowerSeries (Fin 4) ℂ ⧸ unionOfPlanes))
    not_injective_rTensor

end Stacks.Intersection.TwoPlanes

end
