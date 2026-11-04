module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.PseudoCoherentCycles

/-! # The complex of homogeneous pieces of a graded differential algebra

Let `A` be a differential graded algebra over a commutative coefficient algebra `P` sitting in
degree zero. Each homogeneous piece `Aᵢ n` is then a `P`-module, the differential restricts to a
`P`-linear map `Aᵢ (n + 1) → Aᵢ n`, and the pieces assemble into a chain complex of `P`-modules

`⋯ → Aᵢ 2 → Aᵢ 1 → Aᵢ 0`

with `Aᵢ n` in chain degree `n`. This is the unaugmented companion of
`DividedPowers.TateResolution.augmentedChainComplex`, which instead places a prescribed target of
an augmentation in degree `0` and shifts every homogeneous piece up by one.

The point of the construction is the identification of its homology with the concrete cycles
modulo boundaries of `A`: `gradedChainComplexHomologyEquiv` is a `P`-linear equivalence between
the degree-`n` homology of the complex and `coefficientCycles Aᵢ d h0 n` modulo the differentials
of the degree-`n + 1` elements, and `gradedChainComplexHomologyEquiv_apply` computes it on the
class of a cycle.

## Main definitions

* `DividedPowers.TateResolution.gradedChainComplex` — the complex of homogeneous pieces,
  `ℕ`-indexed, with `Aᵢ n` in degree `n`.
* `DividedPowers.TateResolution.gradedCochainComplex` — the same complex, placed in the
  non-positive integer degrees.
* `DividedPowers.TateResolution.coefficientBoundaries` and
  `DividedPowers.TateResolution.coefficientHomology` — the degree-`n` boundaries over the
  coefficient algebra, and the degree-`n` cycles modulo them.
* `DividedPowers.TateResolution.coefficientCyclesToHomology` — the map sending a degree-`n`
  cycle of `A` to its homology class in the complex.

## Main results

* `DividedPowers.TateResolution.gradedChainComplex_X` and
  `DividedPowers.TateResolution.gradedChainComplex_d` — the terms and the differentials of the
  complex are the homogeneous pieces and the restricted differential.
* `DividedPowers.TateResolution.coefficientCyclesToHomology_eq_zero_iff` — a cycle has
  vanishing class exactly when it is a boundary.
* `DividedPowers.TateResolution.gradedChainComplexHomologyEquiv` and
  `DividedPowers.TateResolution.gradedChainComplexHomologyEquiv_apply` — the homology of the
  complex is the cycles modulo the boundaries, by a `P`-linear equivalence sending the class of a
  cycle to the class of that cycle.

## Implementation notes

The cycles of the complex in degree `n` are the elements of `Aᵢ n` killed by the differential of
the complex out of degree `n`. For `n = m + 1` that differential is the restricted differential
of `A`, so they are the cycles of `A`; for `n = 0` it is the zero map, but there every element of
`Aᵢ 0` is a cycle of `A` anyway, the differential vanishing in degree zero. So the concrete
description of the homology is uniform in `n` and `coefficientCycles` can be used in every
degree; `mem_coefficientCycles_of_d_eq_zero` is where the two cases are separated.

The equivalence of `gradedChainComplexHomologyEquiv` is the first isomorphism theorem applied to
`coefficientCyclesToHomology`: that map is surjective because the homology is a quotient of the
cycles of the complex and those are exactly the cycles of `A`, and its kernel is the boundaries
because the homology is the cokernel of the map from the term one degree up.

## References

* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
-/

open CategoryTheory CategoryTheory.Limits

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Ring A] [Algebra R A] [Algebra P A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra Aᵢ d] (h0 : ∀ p : P, algebraMap P A p ∈ Aᵢ 0)

/-! ### The complex -/

/-- **The complex of homogeneous pieces of `A` over its coefficient algebra**, with the
degree-`n` piece in chain degree `n` and the restricted differential of `A` between consecutive
pieces. It is a complex because the differential squares to zero. -/
public noncomputable def gradedChainComplex : ChainComplex (ModuleCat.{w} P) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of P ↥(coefficientGrade Aᵢ h0 n))
    (fun n => ModuleCat.ofHom (coefficientDifferential Aᵢ d h0 n))
    fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
      coefficientDifferential_comp Aᵢ d h0 n x)

/-- The degree-`n` term of the complex is the degree-`n` homogeneous piece. -/
@[simp]
public theorem gradedChainComplex_X (n : ℕ) :
    (gradedChainComplex Aᵢ d h0).X n = ModuleCat.of P ↥(coefficientGrade Aᵢ h0 n) := rfl

/-- The differential of the complex from degree `n + 1` to degree `n` is the restricted
differential of `A`. -/
public theorem gradedChainComplex_d (n : ℕ) :
    (gradedChainComplex Aᵢ d h0).d (n + 1) n =
      ModuleCat.ofHom (coefficientDifferential Aᵢ d h0 n) :=
  ChainComplex.of_d (fun n => ModuleCat.of P ↥(coefficientGrade Aᵢ h0 n))
    (fun n => ModuleCat.ofHom (coefficientDifferential Aᵢ d h0 n)) n

/-- The complex has no differential between two degrees that are not consecutive. -/
public theorem gradedChainComplex_d_eq_zero {i j : ℕ} (h : j + 1 ≠ i) :
    (gradedChainComplex Aᵢ d h0).d i j = 0 :=
  (gradedChainComplex Aᵢ d h0).shape i j h

/-- The restricted differential of `A` is the differential of the complex, on an element of the
degree-`n + 1` piece. -/
public theorem coefficientDifferential_eq_gradedChainComplex_d_apply (n : ℕ)
    (y : ↥(coefficientGrade Aᵢ h0 (n + 1))) :
    coefficientDifferential Aᵢ d h0 n y = (gradedChainComplex Aᵢ d h0).d (n + 1) n y := by
  rw [gradedChainComplex_d]
  rfl

/-- **The complex of homogeneous pieces, placed in the non-positive integer degrees**, with the
degree-`n` piece in degree `-n`. -/
public noncomputable def gradedCochainComplex : CochainComplex (ModuleCat.{w} P) ℤ :=
  (gradedChainComplex Aᵢ d h0).extend ComplexShape.embeddingDownNat

/-- The degree-`-n` term of the cochain complex is the degree-`n` homogeneous piece. -/
public noncomputable def gradedCochainComplexXIso (n : ℕ) :
    (gradedCochainComplex Aᵢ d h0).X (-n) ≅ ModuleCat.of P ↥(coefficientGrade Aᵢ h0 n) :=
  (gradedChainComplex Aᵢ d h0).extendXIso ComplexShape.embeddingDownNat rfl

/-- The cochain complex vanishes in every positive degree. -/
public theorem isZero_gradedCochainComplex_X {i : ℤ} (hi : 0 < i) :
    IsZero ((gradedCochainComplex Aᵢ d h0).X i) :=
  (gradedChainComplex Aᵢ d h0).isZero_extend_X ComplexShape.embeddingDownNat i
    (fun n hn => by simp only [ComplexShape.embeddingDownNat_f] at hn; omega)

/-- The cochain complex is bounded above by degree `0`. -/
public theorem isStrictlyLE_gradedCochainComplex :
    (gradedCochainComplex Aᵢ d h0).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun _ hi => isZero_gradedCochainComplex_X Aᵢ d h0 hi

/-! ### Cycles and boundaries over the coefficient algebra -/

/-- **The degree-`n` boundaries, as a module over a coefficient algebra sitting in degree
zero**: the differentials of the degree-`n + 1` homogeneous elements. -/
public def coefficientBoundaries (n : ℕ) : Submodule P A :=
  (LinearMap.range (coefficientDifferential Aᵢ d h0 n)).map (coefficientGrade Aᵢ h0 n).subtype

/-- Membership in the degree-`n` boundaries over the coefficient algebra. -/
@[simp]
public theorem mem_coefficientBoundaries {n : ℕ} {x : A} :
    x ∈ coefficientBoundaries Aᵢ d h0 n ↔ ∃ y ∈ Aᵢ (n + 1), d y = x := by
  simp only [coefficientBoundaries, Submodule.mem_map, LinearMap.mem_range,
    Submodule.coe_subtype]
  constructor
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨(y : A), y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨coefficientDifferential Aᵢ d h0 n ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

/-- Boundaries are cycles, the differential squaring to zero and lowering degree by one. -/
public theorem coefficientBoundaries_le_coefficientCycles (n : ℕ) :
    coefficientBoundaries Aᵢ d h0 n ≤ coefficientCycles Aᵢ d h0 n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_coefficientBoundaries Aᵢ d h0).1 hx
  exact ⟨IsDifferentialGradedAlgebra.d_mem (𝒜 := Aᵢ) (d := d) hy,
    IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := Aᵢ) (d := d) y⟩

/-- **The degree-`n` homology over the coefficient algebra**: the degree-`n` cycles modulo the
degree-`n` boundaries. -/
public abbrev coefficientHomology (n : ℕ) : Type w :=
  ↥(coefficientCycles Aᵢ d h0 n) ⧸
    (coefficientBoundaries Aᵢ d h0 n).comap (coefficientCycles Aᵢ d h0 n).subtype

/-- **An element of the degree-`n` piece killed by every differential of the complex out of
degree `n` is a cycle of `A`.** In a positive degree the differential of the complex is the
differential of `A`; in degree zero the differential of `A` vanishes anyway. -/
public theorem mem_coefficientCycles_of_d_eq_zero (n : ℕ) (x : ↥(coefficientGrade Aᵢ h0 n))
    (hx : ∀ j : ℕ, (gradedChainComplex Aᵢ d h0).d n j x = 0) :
    (x : A) ∈ coefficientCycles Aᵢ d h0 n := by
  refine ⟨x.2, ?_⟩
  match n with
  | 0 => exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := Aᵢ) (d := d) x.2
  | m + 1 =>
      have h : coefficientDifferential Aᵢ d h0 m x = 0 := by
        rw [coefficientDifferential_eq_gradedChainComplex_d_apply Aᵢ d h0 m x]
        exact hx m
      exact congrArg Subtype.val h

/-! ### The homology of the complex -/

/-- The inclusion of the degree-`n` cycles of `A` into the degree-`n` term of the complex. -/
public def coefficientCyclesInclusion (n : ℕ) :
    ModuleCat.of P ↥(coefficientCycles Aᵢ d h0 n) ⟶ (gradedChainComplex Aᵢ d h0).X n :=
  ModuleCat.ofHom (Submodule.inclusion (coefficientCycles_le_coefficientGrade Aᵢ d h0 n))

/-- A cycle of `A` is killed by every differential of the complex out of its degree. -/
public theorem coefficientCyclesInclusion_comp_d (n j : ℕ) :
    coefficientCyclesInclusion Aᵢ d h0 n ≫ (gradedChainComplex Aᵢ d h0).d n j = 0 := by
  by_cases h : j + 1 = n
  · subst h
    rw [gradedChainComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext x.2.2)
  · rw [gradedChainComplex_d_eq_zero Aᵢ d h0 h, comp_zero]

/-- The degree-`n` cycles of `A`, mapped into the cycles of the complex. -/
public noncomputable def toCyclesGradedChainComplex (n : ℕ) :
    ModuleCat.of P ↥(coefficientCycles Aᵢ d h0 n) ⟶ (gradedChainComplex Aᵢ d h0).cycles n :=
  (gradedChainComplex Aᵢ d h0).liftCycles (coefficientCyclesInclusion Aᵢ d h0 n)
    ((ComplexShape.down ℕ).next n) rfl (coefficientCyclesInclusion_comp_d Aᵢ d h0 n _)

/-- The map into the cycles of the complex is the inclusion of the cycles of `A`. -/
@[simp]
public theorem toCyclesGradedChainComplex_iCycles (n : ℕ) :
    toCyclesGradedChainComplex Aᵢ d h0 n ≫ (gradedChainComplex Aᵢ d h0).iCycles n =
      coefficientCyclesInclusion Aᵢ d h0 n :=
  (gradedChainComplex Aᵢ d h0).liftCycles_i _ _ _ _

/-- The map into the cycles of the complex does not change the underlying element. -/
public theorem inclusion_eq_iCycles_toCyclesGradedChainComplex (n : ℕ)
    (z : ↥(coefficientCycles Aᵢ d h0 n)) :
    Submodule.inclusion (coefficientCycles_le_coefficientGrade Aᵢ d h0 n) z =
      (gradedChainComplex Aᵢ d h0).iCycles n (toCyclesGradedChainComplex Aᵢ d h0 n z) :=
  (LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    (toCyclesGradedChainComplex_iCycles Aᵢ d h0 n)) z).symm

/-- **Every cycle of the complex comes from a cycle of `A`**: the cycles of the complex in
degree `n` are the degree-`n` elements killed by the differential, which are the degree-`n`
cycles of `A`. -/
public theorem surjective_toCyclesGradedChainComplex (n : ℕ) :
    Function.Surjective (toCyclesGradedChainComplex Aᵢ d h0 n) := by
  intro z
  obtain ⟨x, hxz⟩ : ∃ x : ↥(coefficientGrade Aᵢ h0 n),
      (gradedChainComplex Aᵢ d h0).iCycles n z = x :=
    ⟨(gradedChainComplex Aᵢ d h0).iCycles n z, rfl⟩
  have hx : (x : A) ∈ coefficientCycles Aᵢ d h0 n := by
    refine mem_coefficientCycles_of_d_eq_zero Aᵢ d h0 n x fun j => ?_
    rw [← hxz]
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      ((gradedChainComplex Aᵢ d h0).iCycles_d n j)) z
  refine ⟨⟨(x : A), hx⟩, ?_⟩
  refine (ModuleCat.mono_iff_injective ((gradedChainComplex Aᵢ d h0).iCycles n)).1
    inferInstance ?_
  rw [hxz, ← inclusion_eq_iCycles_toCyclesGradedChainComplex Aᵢ d h0 n ⟨(x : A), hx⟩]
  exact Subtype.ext rfl

/-- **The homology class of a degree-`n` cycle of `A`** in the complex of homogeneous
pieces. -/
public noncomputable def coefficientCyclesToHomology (n : ℕ) :
    ↥(coefficientCycles Aᵢ d h0 n) →ₗ[P] ((gradedChainComplex Aᵢ d h0).homology n) :=
  (toCyclesGradedChainComplex Aᵢ d h0 n ≫ (gradedChainComplex Aᵢ d h0).homologyπ n).hom

/-- The class of a cycle of `A` is the class of its image in the cycles of the complex. -/
public theorem coefficientCyclesToHomology_apply (n : ℕ)
    (z : ↥(coefficientCycles Aᵢ d h0 n)) :
    coefficientCyclesToHomology Aᵢ d h0 n z =
      (gradedChainComplex Aᵢ d h0).homologyπ n (toCyclesGradedChainComplex Aᵢ d h0 n z) := rfl

/-- **Every homology class of the complex is the class of a cycle of `A`**: the homology is a
quotient of the cycles of the complex, and those are the cycles of `A`. -/
public theorem surjective_coefficientCyclesToHomology (n : ℕ) :
    Function.Surjective (coefficientCyclesToHomology Aᵢ d h0 n) :=
  ((ModuleCat.epi_iff_surjective ((gradedChainComplex Aᵢ d h0).homologyπ n)).1
    inferInstance).comp (surjective_toCyclesGradedChainComplex Aᵢ d h0 n)

/-- A cycle of `A` and a homogeneous element have the same image in the cycles of the complex
exactly when the differential of the element is the cycle. -/
private theorem toCycles_eq_toCyclesGradedChainComplex_iff (n : ℕ)
    (y : ↥(coefficientGrade Aᵢ h0 (n + 1))) (z : ↥(coefficientCycles Aᵢ d h0 n)) :
    (gradedChainComplex Aᵢ d h0).toCycles (n + 1) n y = toCyclesGradedChainComplex Aᵢ d h0 n z ↔
      coefficientDifferential Aᵢ d h0 n y =
        Submodule.inclusion (coefficientCycles_le_coefficientGrade Aᵢ d h0 n) z := by
  have hyd : (gradedChainComplex Aᵢ d h0).iCycles n
        ((gradedChainComplex Aᵢ d h0).toCycles (n + 1) n y) =
      (gradedChainComplex Aᵢ d h0).d (n + 1) n y :=
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      ((gradedChainComplex Aᵢ d h0).toCycles_i (n + 1) n)) y
  rw [← (ModuleCat.mono_iff_injective ((gradedChainComplex Aᵢ d h0).iCycles n)).1
      inferInstance |>.eq_iff, hyd, ← inclusion_eq_iCycles_toCyclesGradedChainComplex Aᵢ d h0 n z,
    ← coefficientDifferential_eq_gradedChainComplex_d_apply Aᵢ d h0 n y]
  exact Iff.rfl

/-- **The class of a degree-`n` cycle of `A` vanishes exactly when the cycle is a boundary.**
The forward direction uses that the homology is the cokernel of the map from the degree-`n + 1`
term to the cycles, the reverse that that composite vanishes. -/
public theorem coefficientCyclesToHomology_eq_zero_iff (n : ℕ)
    (z : ↥(coefficientCycles Aᵢ d h0 n)) :
    coefficientCyclesToHomology Aᵢ d h0 n z = 0 ↔
      (z : A) ∈ coefficientBoundaries Aᵢ d h0 n := by
  let S : ShortComplex (ModuleCat.{w} P) :=
    { X₁ := (gradedChainComplex Aᵢ d h0).X (n + 1),
      X₂ := (gradedChainComplex Aᵢ d h0).cycles n,
      X₃ := (gradedChainComplex Aᵢ d h0).homology n,
      f := (gradedChainComplex Aᵢ d h0).toCycles (n + 1) n,
      g := (gradedChainComplex Aᵢ d h0).homologyπ n,
      zero := (gradedChainComplex Aᵢ d h0).toCycles_comp_homologyπ (n + 1) n }
  have hS : S.Exact := S.exact_of_g_is_cokernel
    ((gradedChainComplex Aᵢ d h0).homologyIsCokernel (n + 1) n (by simp))
  rw [coefficientCyclesToHomology_apply]
  constructor
  · intro hz
    obtain ⟨y, hy⟩ : ∃ y : ↥(coefficientGrade Aᵢ h0 (n + 1)),
        (gradedChainComplex Aᵢ d h0).toCycles (n + 1) n y =
          toCyclesGradedChainComplex Aᵢ d h0 n z :=
      (ShortComplex.moduleCat_exact_iff S).1 hS (toCyclesGradedChainComplex Aᵢ d h0 n z) hz
    exact (mem_coefficientBoundaries Aᵢ d h0).2 ⟨(y : A), y.2, congrArg Subtype.val
      ((toCycles_eq_toCyclesGradedChainComplex_iff Aᵢ d h0 n y z).1 hy)⟩
  · intro hz
    obtain ⟨y, hy, hdy⟩ := (mem_coefficientBoundaries Aᵢ d h0).1 hz
    rw [← (toCycles_eq_toCyclesGradedChainComplex_iff Aᵢ d h0 n ⟨y, hy⟩ z).2 (Subtype.ext hdy)]
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
      ((gradedChainComplex Aᵢ d h0).toCycles_comp_homologyπ (n + 1) n)) ⟨y, hy⟩

/-- The kernel of the class map is exactly the boundaries. -/
public theorem ker_coefficientCyclesToHomology (n : ℕ) :
    LinearMap.ker (coefficientCyclesToHomology Aᵢ d h0 n) =
      (coefficientBoundaries Aᵢ d h0 n).comap (coefficientCycles Aᵢ d h0 n).subtype := by
  ext z
  simpa only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype] using
    coefficientCyclesToHomology_eq_zero_iff Aᵢ d h0 n z

/-- **The homology of the complex of homogeneous pieces is the cycles modulo the boundaries.**
The class map is onto with kernel the boundaries, so the first isomorphism theorem identifies the
degree-`n` homology of the complex with the concrete degree-`n` homology of `A` over its
coefficient algebra. -/
public noncomputable def gradedChainComplexHomologyEquiv (n : ℕ) :
    ((gradedChainComplex Aᵢ d h0).homology n) ≃ₗ[P] coefficientHomology Aᵢ d h0 n :=
  (LinearMap.quotKerEquivOfSurjective _
      (surjective_coefficientCyclesToHomology Aᵢ d h0 n)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_coefficientCyclesToHomology Aᵢ d h0 n))

/-- **The equivalence sends the homology class of a cycle to the class of that cycle.** -/
@[simp]
public theorem gradedChainComplexHomologyEquiv_apply (n : ℕ)
    (z : ↥(coefficientCycles Aᵢ d h0 n)) :
    gradedChainComplexHomologyEquiv Aᵢ d h0 n (coefficientCyclesToHomology Aᵢ d h0 n z) =
      Submodule.Quotient.mk z := by
  simp only [gradedChainComplexHomologyEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk]

/-- The inverse of the equivalence sends the class of a cycle to its homology class. -/
@[simp]
public theorem gradedChainComplexHomologyEquiv_symm_apply (n : ℕ)
    (z : ↥(coefficientCycles Aᵢ d h0 n)) :
    (gradedChainComplexHomologyEquiv Aᵢ d h0 n).symm (Submodule.Quotient.mk z) =
      coefficientCyclesToHomology Aᵢ d h0 n z :=
  (LinearEquiv.symm_apply_eq _).2 (gradedChainComplexHomologyEquiv_apply Aᵢ d h0 n z).symm

end DividedPowers.TateResolution

end
