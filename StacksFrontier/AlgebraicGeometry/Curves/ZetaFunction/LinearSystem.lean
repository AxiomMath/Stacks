module

public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.RiemannRochSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointCountMonotone

/-!
# Complete linear systems on a curve

Let `C` be a smooth proper curve of genus `γ` over an algebraically closed field `Ω`. This file
proves:

* a rational function without poles is a constant
  (`Stacks.Zeta.exists_eq_algebraMap_of_ord_nonneg`), from the degree formula: `f - f(x)` would
  have a zero and no pole;
* `dim L(D) = h⁰([D])` for every divisor `D` (`Stacks.Zeta.finrank_rrSpace`), where
  `h⁰(c) = dim H⁰(C, ℒ)` for an invertible `ℒ` of class `c`: both sides only depend on the class,
  `L(D) ≅ L(D + div f)` by multiplication by `f⁻¹`, and `H⁰(ℒ) ≅ L(div s)`;
* Riemann–Roch for large degree: `h⁰(c) = deg c + 1 - γ` when `deg c ≥ 2γ - 1`
  (`Stacks.Zeta.h0_eq_of_le`), from `h⁰ - h¹ = deg + 1 - γ` and Tag 0B90.

The effective divisors of class `[D]` are the `D + div f`, `f` in `ℙ(L(D))`.

## Main definitions

* `Stacks.Zeta.h0`: `h⁰` of a Picard class.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace Stacks.Zeta

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

/-! ### Functions without poles -/

/-- **A rational function without poles is a nonzero constant.** -/
theorem exists_eq_algebraMap_of_ord_nonneg {f : C.functionField} (hf0 : f ≠ 0)
    (hf : ∀ x : ClosedPoint C, 0 ≤ C.ord f x.1) :
    letI := ffAlg g
    ∃ c : Ω, c ≠ 0 ∧ f = algebraMap Ω C.functionField c := by
  let := ffAlg g
  obtain ⟨x₀, hx₀⟩ := (Stacks.EtaleCohomology.infinite_closedPoints_of_isCurve (f := g)).nonempty
  obtain ⟨c, hc⟩ := exists_one_le_ord_sub g hx₀ (hf ⟨x₀, hx₀⟩)
  have hne : f = algebraMap Ω C.functionField c → c ≠ 0 := fun hfc h =>
    hf0 (by rw [hfc, h, map_zero])
  obtain hc | hc := hc
  · exact ⟨c, hne hc, hc⟩
  obtain ⟨d, hd_def⟩ : ∃ d, d = f - algebraMap Ω C.functionField c := ⟨_, rfl⟩
  have hc' : 1 ≤ C.ord d x₀ := by rw [hd_def]; exact hc
  by_cases hd : d = 0
  · have hfc : f = algebraMap Ω C.functionField c := sub_eq_zero.1 (hd_def ▸ hd)
    exact ⟨c, hne hfc, hfc⟩
  exfalso
  have hnonneg : ∀ y : ClosedPoint C, 0 ≤ C.ord d y.1 := fun y => by
    have := dvr_closedPoint g y
    by_cases hc0 : c = 0
    · rw [hd_def, hc0, map_zero, sub_zero]; exact hf y
    have h1 := Scheme.ord_add (x := y.1) (f := f) (g := -algebraMap Ω C.functionField c)
      (by rw [← sub_eq_add_neg, ← hd_def]; exact hd)
    have h2 : C.ord (-algebraMap Ω C.functionField c) y.1 = 0 := by
      rw [← map_neg]; exact ord_algebraMap_const g (neg_ne_zero.2 hc0) y
    rw [← sub_eq_add_neg, ← hd_def] at h1
    have := hf y
    omega
  have hdeg := degree_divOf g hd
  have hx₀mem : (⟨x₀, hx₀⟩ : ClosedPoint C) ∈ (divOf g hd).support := by
    rw [Finsupp.mem_support_iff, divOf_apply]
    show C.ord d x₀ ≠ 0
    omega
  have hle := Finset.single_le_sum (f := fun y => divOf g hd y)
    (fun y _ => by rw [divOf_apply]; exact hnonneg y) hx₀mem
  rw [Finsupp.sum] at hdeg
  simp only [divOf_apply] at hle hdeg
  change 1 ≤ C.ord d x₀ at hc'
  omega

/-! ### Multiplication by a function -/

omit [IsAlgClosed Ω] in
/-- For `f ≠ 0`, `a ∈ L(D + div f)` if and only if `f * a ∈ L(D)`. -/
theorem mem_rrSpace_add_divOf_iff {D : ClosedPoint C →₀ ℤ} {f : C.functionField} (hf : f ≠ 0)
    (a : C.functionField) :
    letI := ffAlg g
    a ∈ rrSpace g (D + divOf g hf) ↔ f * a ∈ rrSpace g D := by
  let := ffAlg g
  rw [mem_rrSpace, mem_rrSpace]
  by_cases ha : a = 0
  · simp [ha]
  have hfa : f * a ≠ 0 := mul_ne_zero hf ha
  simp only [ha, hfa, false_or, Finsupp.coe_add, Pi.add_apply, divOf_apply,
    Scheme.ord_mul hf ha]
  constructor <;> intro h x <;> have := h x <;> omega

omit [IsAlgClosed Ω] in
/-- **`L(D + div f) ≅ L(D)`**, by multiplication by `f`. -/
theorem finrank_rrSpace_add_divOf (D : ClosedPoint C →₀ ℤ) {f : C.functionField} (hf : f ≠ 0) :
    letI := ffAlg g
    Module.finrank Ω (rrSpace g (D + divOf g hf)) = Module.finrank Ω (rrSpace g D) := by
  let := ffAlg g
  have hinj : Function.Injective (LinearMap.mulLeft Ω f) := fun a b h =>
    mul_left_cancel₀ hf h
  have hmap : (rrSpace g (D + divOf g hf)).map (LinearMap.mulLeft Ω f) = rrSpace g D := by
    ext b
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (mem_rrSpace_add_divOf_iff g hf a).1 ha
    · intro hb
      refine ⟨f⁻¹ * b, (mem_rrSpace_add_divOf_iff g hf _).2 ?_, ?_⟩
      · rwa [mul_inv_cancel_left₀ hf]
      · exact mul_inv_cancel_left₀ hf b
  rw [← hmap]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq

/-! ### `h⁰` of a Picard class -/

/-- `h⁰(c) = dim H⁰(C, ℒ)` for the chosen invertible module `ℒ` of class `c`. -/
def h0 (c : Stacks.Picard.ofScheme C) : ℕ :=
  Module.finrank Ω (cohomologyOverField Ω g
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj 0)

omit [IsAlgClosed Ω] in
/-- **`dim L(D) = h⁰([D])`.** -/
theorem finrank_rrSpace (D : ClosedPoint C →₀ ℤ) :
    letI := ffAlg g
    Module.finrank Ω (rrSpace g D) = h0 g (divisorClass g D) := by
  let := ffAlg g
  set c := divisorClass g D
  set L := (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
  have hL : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  have : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  obtain ⟨s, hs⟩ := exists_isRegularMeromorphicSection_of_isIntegral C L
  have hcls : divisorClass g (sectionDivisor g L s hs) = c :=
    (divisorClass_sectionDivisor g L s hs hL).trans
      (Stacks.Picard.classOf_picardRepresentative C.toRingedSpace c)
  obtain ⟨f, hf, hfD⟩ := exists_divOf_eq_of_divisorClass_eq_zero g
    (D := D - sectionDivisor g L s hs) (by rw [map_sub, hcls, sub_self])
  have hD : D = sectionDivisor g L s hs + divOf g hf := by rw [hfD]; abel
  conv_lhs => rw [hD]
  rw [finrank_rrSpace_add_divOf]
  exact finrank_rrSpace_sectionDivisor g L s hs

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
include g in
/-- The curve `C` has topological Krull dimension at most `1`. -/
theorem topologicalKrullDim_le_one' : topologicalKrullDim C ≤ 1 :=
  topologicalKrullDim_le_one g

omit [Smooth g] [IsLocallyNoetherian C] in
/-- `h⁰(c) - h¹(c) = deg c + 1 - γ`, Riemann–Roch. -/
theorem h0_sub_h1 (c : Stacks.Picard.ofScheme C) :
    (h0 g c : ℤ) - (Module.finrank Ω (cohomologyOverField Ω g
        (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj 1) : ℤ) =
      Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c + 1 - (genus g : ℤ) := by
  have hRR := finrank_cohomologyOverField_zero_sub_one_eq Ω g (topologicalKrullDim_le_one g)
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
    (Stacks.Picard.picardRepresentative C.toRingedSpace c).property
  have hO : Module.finrank Ω
      (cohomologyOverField Ω g (SheafOfModules.unit C.ringCatSheaf) 0) = 1 := by
    rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
    exact finrank_globalSections_eq_one Ω g
  rw [hO] at hRR
  exact hRR

omit [Smooth g] [IsLocallyNoetherian C] in
/-- **Riemann–Roch in large degree**: `h⁰(c) = deg c + 1 - γ` when `deg c ≥ 2γ - 1`. -/
theorem h0_eq_of_le (c : Stacks.Picard.ofScheme C)
    (hc : 2 * (genus g : ℤ) - 1 ≤ Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c) :
    (h0 g c : ℤ) =
      Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c + 1 - (genus g : ℤ) := by
  have h1 : Module.finrank Ω (cohomologyOverField Ω g
      (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj 1) = 0 := by
    have := isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree Ω g
      (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj
      (Stacks.Picard.picardRepresentative C.toRingedSpace c).property hc
    have := ModuleCat.subsingleton_of_isZero this
    exact Module.finrank_zero_of_subsingleton
  have := h0_sub_h1 g c
  rw [h1, Nat.cast_zero, sub_zero] at this
  exact this

omit [Smooth g] [IsLocallyNoetherian C] in
/-- `h⁰(c) ≥ 1` when `deg c ≥ γ`. -/
theorem one_le_h0 (c : Stacks.Picard.ofScheme C)
    (hc : (genus g : ℤ) ≤ Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c) :
    1 ≤ h0 g c := by
  have := h0_sub_h1 g c
  have h1 : (0 : ℤ) ≤ Module.finrank Ω (cohomologyOverField Ω g
      (Stacks.Picard.picardRepresentative C.toRingedSpace c).obj 1) := Int.natCast_nonneg _
  omega

end Stacks.Zeta

end
