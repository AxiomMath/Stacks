module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FourVertices
public import Mathlib

/-!
# No fourfold star of minus-two indices

A numerical type with more than five components has no component meeting four
minus-two indices each with intersection number one: the corresponding vector
would make the quadratic form of the intersection matrix vanish on a proper
subgraph.

## Main results

* `AlgebraicGeometry.NumericalType.not_exists_fourfold_of_five_lt_componentCount`.

## References

* [Stacks Project, Tag 0C86](https://stacks.math.columbia.edu/tag/0C86)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

/-- **Stacks Project, Tag 0C86.** A numerical type with more than five components
does not have five distinct minus-two indices with one meeting all four others. -/
@[stacks 0C86]
public theorem not_exists_fourfold_of_five_lt_componentCount
    (T : NumericalType) (hn : 5 < T.componentCount) :
    ¬ ∃ v : Fin 5 → Fin T.componentCount,
      Function.Injective v ∧
        (∀ r, IsMinusTwoIndex T (v r)) ∧
        (∀ r, r ≠ 0 → 0 < T.intersection (v 0) (v r)) := by
  rintro ⟨v, hv, hminus, hedge⟩
  have hne (r : Fin 5) (hr : r ≠ 0 := by decide) : T.intersection (v 0) (v r) ≠ 0 :=
    (hedge r hr).ne'
  have hhi : v 0 ≠ v 1 := hv.ne (by decide)
  have hhj : v 0 ≠ v 2 := hv.ne (by decide)
  have hhk : v 0 ≠ v 3 := hv.ne (by decide)
  have hhl : v 0 ≠ v 4 := hv.ne (by decide)
  have hij : v 1 ≠ v 2 := hv.ne (by decide)
  have hik : v 1 ≠ v 3 := hv.ne (by decide)
  have hil : v 1 ≠ v 4 := hv.ne (by decide)
  have hjk : v 2 ≠ v 3 := hv.ne (by decide)
  have hjl : v 2 ≠ v 4 := hv.ne (by decide)
  have hkl : v 3 ≠ v 4 := hv.ne (by decide)
  obtain ⟨w, -, -, -, -, -, hd00, hd11, hd22, hd33, he01, he10, he02, he20, he03, he30,
    he12, he21, he13, he31, he23, he32, -, -, -, -, -, -, -⟩ :=
    exists_d4_configuration_of_four_isMinusTwoIndex T (by omega) (v 0) (v 1) (v 2) (v 3)
      hhi hhj hhk hij hik hjk (hminus 0) (hminus 1) (hminus 2) (hminus 3)
      (hne 1) (hne 2) (hne 3)
  obtain ⟨w₂, -, -, -, -, -, -, -, -, hd44₂, he01₂, -, -, -, he04₂, he40₂, -, -, he14₂, he41₂,
    he24₂, he42₂, -, -, -, -, -, -, -⟩ :=
    exists_d4_configuration_of_four_isMinusTwoIndex T (by omega) (v 0) (v 1) (v 2) (v 4)
      hhi hhj hhl hij hil hjl (hminus 0) (hminus 1) (hminus 2) (hminus 4)
      (hne 1) (hne 2) (hne 4)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he34₃, he43₃,
    -, -, -, -, -, -, -⟩ :=
    exists_d4_configuration_of_four_isMinusTwoIndex T (by omega) (v 0) (v 1) (v 3) (v 4)
      hhi hhk hhl hik hil hkl (hminus 0) (hminus 1) (hminus 3) (hminus 4)
      (hne 1) (hne 3) (hne 4)
  obtain rfl : w₂ = w := he01₂.symm.trans he01
  -- Build the rational intersection matrix and the vector supported on the
  -- five-vertex star, with coefficient 2 at its center and 1 at each leaf.
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun a b => (T.intersection a b : ℚ)
  let m : Fin T.componentCount → ℚ := fun a => (T.multiplicity a : ℚ)
  let x : Fin T.componentCount → ℚ := fun a =>
    if a = v 0 then 2 else if a = v 1 then 1 else if a = v 2 then 1 else
      if a = v 3 then 1 else if a = v 4 then 1 else 0
  have hAsymm : A.IsSymm := by
    ext a b
    change (T.intersection b a : ℚ) = (T.intersection a b : ℚ)
    exact_mod_cast (T.intersection_symm a b).symm
  have hAoff : ∀ a b, a ≠ b → 0 ≤ A a b := fun a b hab => by
    change 0 ≤ (T.intersection a b : ℚ)
    exact_mod_cast T.intersection_nonneg a b hab
  have hmpos : ∀ a, 0 < m a := fun a => by
    change 0 < (T.multiplicity a : ℚ)
    exact_mod_cast T.multiplicity_pos a
  have hAm : A *ᵥ m = 0 := by
    ext a
    change (∑ b, (T.intersection a b : ℚ) * (T.multiplicity b : ℚ)) = 0
    exact_mod_cast T.intersection_mul_multiplicity a
  have hx0 : x ⬝ᵥ (A *ᵥ x) = 0 := by
    calc
      x ⬝ᵥ (A *ᵥ x) = _ := by
        simpa [x] using five_coordinate_quadratic A (v 0) (v 1) (v 2) (v 3) (v 4)
          hhi hhj hhk hhl hij hik hil hjk hjl hkl (2 : ℚ) 1 1 1 1
      _ = 0 := by
        simp [A, hd00, hd11, hd22, hd33, hd44₂,
          he01, he10, he02, he20, he03, he30, he04₂, he40₂,
          he12, he21, he13, he31, he23, he32,
          he14₂, he41₂, he24₂, he42₂, he34₃, he43₃]
        ring
  obtain ⟨q, hxq⟩ :=
    (dotProduct_mulVec_eq_zero_iff_of_positive_kernel
      hAsymm hAoff hmpos hAm
      (by
        intro I hIne hIproper hcut
        apply T.connected
        refine ⟨I, hIne, hIproper, ?_⟩
        intro a ha b hb
        have hab := hcut a ha b hb
        change (T.intersection a b : ℚ) = 0 at hab
        exact_mod_cast hab) (x := x)).mp hx0
  obtain ⟨z, hz⟩ : ∃ z : Fin T.componentCount, z ∉ Set.range v := by
    by_contra h
    have hcard := Fintype.card_congr
      (Equiv.ofBijective v ⟨hv, fun z => by_contra fun hz => h ⟨z, hz⟩⟩)
    simp only [Fintype.card_fin] at hcard
    omega
  have hzn (r : Fin 5) : z ≠ v r := fun hzr => hz ⟨r, hzr.symm⟩
  have hxz : x z = 0 := by simp [x, hzn]
  have hqzero : q = 0 := by
    have hzq := congrFun hxq z
    rw [hxz] at hzq
    change 0 = q * m z at hzq
    nlinarith [hmpos z]
  have hxh := congrFun hxq (v 0)
  rw [show x (v 0) = 2 by simp [x], hqzero] at hxh
  norm_num at hxh

end AlgebraicGeometry.NumericalType
