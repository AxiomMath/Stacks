module

public import Mathlib.LinearAlgebra.Isomorphisms
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZeroHomology

/-!
# Graded homology of a differential graded algebra

Let `A` be a nonnegatively graded algebra with a differential `d` that lowers degrees by one.
Because `d` is homogeneous, the cycles and the boundaries of `A` are spanned by their homogeneous
elements, and the homology splits into one quotient for each degree: the degree-`n` cycles are the
elements of `𝒜 n` killed by `d`, the degree-`n` boundaries are the differentials of the elements
of `𝒜 (n + 1)`, and `gradeHomology 𝒜 d n` is their quotient.

The degree-`n` homology is compared with two other models of homology. In degree zero the
differential vanishes identically, so there is no kernel to take and the quotient is the one used
by `degreeZeroHomology`. In every degree the quotient is the degree-`n` graded piece of the total
homology `Homology d`, which is the span of the classes of the degree-`n` cycles; the comparison is
an isomorphism precisely because a homogeneous element that is a boundary at all is the
differential of a homogeneous element one degree up.

## Main definitions

* `DividedPowers.TateResolution.gradeCycles` and
  `DividedPowers.TateResolution.gradeBoundaries` — the degree-`n` cycles inside `𝒜 n` and the
  degree-`n` elements that are differentials of degree-`n + 1` elements.
* `DividedPowers.TateResolution.gradeHomology` — the degree-`n` homology, as a quotient of the
  degree-`n` cycles.
* `DividedPowers.TateResolution.totalHomologyGrade` — the degree-`n` graded piece of the total
  homology, the span of the classes of the degree-`n` cycles.

## Main results

* `DividedPowers.TateResolution.gradeCycles_zero` — in degree zero every element is a cycle.
* `DividedPowers.TateResolution.exists_homogeneous_of_mem_boundaries` — a homogeneous element
  which is a boundary is the differential of a homogeneous element one degree up.
* `DividedPowers.TateResolution.gradeHomologyZeroEquiv` — degree-zero homology agrees with
  `degreeZeroHomology`.
* `DividedPowers.TateResolution.gradeHomologyEquivTotalGrade` — degree-`n` homology agrees with
  the degree-`n` graded piece of the total homology.

## Implementation notes

The degree-`n` cycles and boundaries are submodules of `𝒜 n` rather than of `A`, so that the
degree-`n` homology is a quotient of a module of degree-`n` elements and matches the shape of
`degreeZeroHomology`. The comparison with the total homology is obtained from the first
isomorphism theorem applied to the map sending a degree-`n` cycle to its class: its range is the
graded piece because that piece is spanned by such classes, and its kernel is the degree-`n`
boundaries because a homogeneous boundary has a homogeneous preimage.

Quotients of the degree-`n` cycles need the `HasQuotient` instance of this file, because the
generic one of `Mathlib` is stated for an additive group written as such: the degree-`n` cycles
are a submodule of a submodule of `A`, and for them the additive monoid structure is found
through `Submodule.addCommMonoid` instead, which is only definitionally the one that instance
asks for.

## References

* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  [IsDifferentialGradedAlgebra 𝒜 d]

/-- The degree-`n` cycles of a differential graded algebra: the degree-`n` elements killed by
the differential. -/
public def gradeCycles (n : ℕ) : Submodule R (𝒜 n) :=
  Submodule.comap (𝒜 n).subtype (LinearMap.ker d)

/-- The degree-`n` boundaries of a differential graded algebra: the degree-`n` elements that are
differentials of degree-`n + 1` elements. -/
public def gradeBoundaries (n : ℕ) : Submodule R (𝒜 n) :=
  Submodule.comap (𝒜 n).subtype (LinearMap.range (d.comp (𝒜 (n + 1)).subtype))

omit [GradedAlgebra 𝒜] [IsDifferentialGradedAlgebra 𝒜 d] in
/-- A degree-`n` element is a degree-`n` cycle if and only if the differential kills it. -/
@[simp]
public theorem mem_gradeCycles_iff {n : ℕ} {x : 𝒜 n} :
    x ∈ gradeCycles 𝒜 d n ↔ d (x : A) = 0 :=
  Iff.rfl

omit [GradedAlgebra 𝒜] [IsDifferentialGradedAlgebra 𝒜 d] in
/-- A degree-`n` element is a degree-`n` boundary if and only if it is the differential of a
degree-`n + 1` element. -/
@[simp]
public theorem mem_gradeBoundaries_iff {n : ℕ} {x : 𝒜 n} :
    x ∈ gradeBoundaries 𝒜 d n ↔ ∃ y : A, y ∈ 𝒜 (n + 1) ∧ d y = (x : A) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(y : A), y.property, hy⟩
  · rintro ⟨y, hy, hdy⟩
    exact ⟨⟨y, hy⟩, hdy⟩

/-- Boundaries are cycles, because the differential squares to zero. -/
public theorem gradeBoundaries_le_gradeCycles (n : ℕ) :
    gradeBoundaries 𝒜 d n ≤ gradeCycles 𝒜 d n := by
  intro x hx
  obtain ⟨y, -, hdy⟩ := (mem_gradeBoundaries_iff 𝒜 d).mp hx
  rw [mem_gradeCycles_iff, ← hdy]
  exact IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := d) y

/-- Quotients of the degree-`n` cycles by a submodule of them.

This is `Submodule.hasQuotient`, which does not apply as it stands: the additive structure of
`𝒜 n` is found through `Submodule.addCommMonoid`, while a submodule of a submodule of `𝒜 n`
needs it through `AddCommGroup.toAddCommMonoid`, and the two are only definitionally equal. -/
public instance hasQuotientGradeCycles (n : ℕ) :
    HasQuotient (gradeCycles 𝒜 d n) (Submodule R (gradeCycles 𝒜 d n)) :=
  @Submodule.hasQuotient R (gradeCycles 𝒜 d n) CommRing.toRing
    (Submodule.addCommGroup (gradeCycles 𝒜 d n)) (Submodule.module (gradeCycles 𝒜 d n))

/-- The degree-`n` homology of a differential graded algebra: the degree-`n` cycles modulo the
degree-`n` boundaries. -/
public abbrev gradeHomology (n : ℕ) : Type v :=
  (gradeCycles 𝒜 d n) ⧸ ((gradeBoundaries 𝒜 d n).comap (gradeCycles 𝒜 d n).subtype)

/-- In degree zero the differential vanishes, so every degree-zero element is a cycle. -/
public theorem gradeCycles_zero : gradeCycles 𝒜 d 0 = ⊤ :=
  eq_top_iff.mpr fun x _ => (mem_gradeCycles_iff 𝒜 d).mpr
    (IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) x.property)

/-- A homogeneous element which is a boundary is the differential of a homogeneous element one
degree up. -/
public theorem exists_homogeneous_of_mem_boundaries {n : ℕ} {x : A} (hx : x ∈ 𝒜 n)
    (hb : ∃ y : A, d y = x) : ∃ y : A, y ∈ 𝒜 (n + 1) ∧ d y = x :=
  exists_homogeneous_boundary_preimage 𝒜 d hx (LinearMap.mem_range.mpr hb)

/-! ### Comparison with degree-zero homology -/

/-- Degree-zero cycles are all of the degree-zero graded piece, as a linear equivalence. -/
public def gradeCyclesZeroEquiv : gradeCycles 𝒜 d 0 ≃ₗ[R] 𝒜 0 :=
  (LinearEquiv.ofEq _ _ (gradeCycles_zero 𝒜 d)).trans Submodule.topEquiv

/-- `gradeCyclesZeroEquiv` sends a degree-zero cycle to itself as a degree-zero element. -/
@[simp]
public theorem gradeCyclesZeroEquiv_apply (x : gradeCycles 𝒜 d 0) :
    gradeCyclesZeroEquiv 𝒜 d x = (x : 𝒜 0) :=
  rfl

/-- Under the identification of degree-zero cycles with the degree-zero graded piece, the
degree-zero boundaries are the submodule by which `degreeZeroHomology` is formed. -/
public theorem map_gradeCyclesZeroEquiv_gradeBoundaries :
    Submodule.map (gradeCyclesZeroEquiv 𝒜 d : gradeCycles 𝒜 d 0 →ₗ[R] 𝒜 0)
        ((gradeBoundaries 𝒜 d 0).comap (gradeCycles 𝒜 d 0).subtype) =
      gradeBoundaries 𝒜 d 0 := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, by rw [gradeCycles_zero]; trivial⟩, hy, rfl⟩

/-- Degree-zero homology is `degreeZeroHomology`, as a linear equivalence. -/
public noncomputable def gradeHomologyZeroEquiv :
    gradeHomology 𝒜 d 0 ≃ₗ[R] degreeZeroHomology 𝒜 d :=
  Submodule.Quotient.equiv _ _ (gradeCyclesZeroEquiv 𝒜 d)
    (map_gradeCyclesZeroEquiv_gradeBoundaries 𝒜 d)

/-- `gradeHomologyZeroEquiv` sends the class of a degree-zero cycle `x` to the class of `x` in
`degreeZeroHomology`. -/
@[simp]
public theorem gradeHomologyZeroEquiv_mk (x : 𝒜 0) (hx : x ∈ gradeCycles 𝒜 d 0) :
    gradeHomologyZeroEquiv 𝒜 d (Submodule.Quotient.mk ⟨x, hx⟩) =
      Submodule.Quotient.mk x :=
  rfl

/-! ### Comparison with the total homology -/

/-- The degree-`n` cycles, included into all cycles. -/
public def gradeCyclesToCycles (n : ℕ) : gradeCycles 𝒜 d n →ₗ[R] cycles d :=
  ((𝒜 n).subtype.comp (gradeCycles 𝒜 d n).subtype).codRestrict (cycles d) fun x => x.2

omit [GradedAlgebra 𝒜] [IsDifferentialGradedAlgebra 𝒜 d] in
/-- `gradeCyclesToCycles` sends a degree-`n` cycle to the same element of `A`. -/
@[simp]
public theorem coe_gradeCyclesToCycles (n : ℕ) (x : gradeCycles 𝒜 d n) :
    (gradeCyclesToCycles 𝒜 d n x : A) = (x : A) :=
  rfl

/-- The class in the total homology of a degree-`n` cycle. -/
public def gradeCyclesToHomology (n : ℕ) :
    gradeCycles 𝒜 d n →ₗ[R] Homology (𝒜 := 𝒜) d :=
  (boundaries (𝒜 := 𝒜) d).mkQ.comp (gradeCyclesToCycles 𝒜 d n)

/-- `gradeCyclesToHomology` sends a degree-`n` cycle to the class of its image under
`gradeCyclesToCycles`. -/
@[simp]
public theorem gradeCyclesToHomology_apply (n : ℕ) (x : gradeCycles 𝒜 d n) :
    gradeCyclesToHomology 𝒜 d n x =
      Submodule.Quotient.mk (gradeCyclesToCycles 𝒜 d n x) :=
  rfl

/-- The degree-`n` graded piece of the total homology: the span of the classes of the degree-`n`
cycles. -/
public def totalHomologyGrade (n : ℕ) : Submodule R (Homology (𝒜 := 𝒜) d) :=
  Submodule.span R {z | ∃ x : cycles d, (x : A) ∈ 𝒜 n ∧
    (Submodule.Quotient.mk x : Homology (𝒜 := 𝒜) d) = z}

/-- The degree-`n` graded piece of the total homology is the set of classes of degree-`n`
cycles; no span is needed. -/
public theorem totalHomologyGrade_eq_range (n : ℕ) :
    totalHomologyGrade 𝒜 d n = LinearMap.range (gradeCyclesToHomology 𝒜 d n) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨⟨(x : A), hx⟩, x.property⟩, rfl⟩
  · rintro z ⟨x, rfl⟩
    exact Submodule.subset_span ⟨gradeCyclesToCycles 𝒜 d n x, x.1.property, rfl⟩

/-- A degree-`n` cycle has trivial class in the total homology exactly when it is a degree-`n`
boundary: a homogeneous boundary has a homogeneous preimage. -/
public theorem ker_gradeCyclesToHomology (n : ℕ) :
    LinearMap.ker (gradeCyclesToHomology 𝒜 d n) =
      (gradeBoundaries 𝒜 d n).comap (gradeCycles 𝒜 d n).subtype := by
  have hcomp : gradeCyclesToHomology 𝒜 d n =
      (boundaries (𝒜 := 𝒜) d).mkQ.comp (gradeCyclesToCycles 𝒜 d n) := rfl
  rw [hcomp, LinearMap.ker_comp, Submodule.ker_mkQ]
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply, mem_gradeBoundaries_iff,
    coe_gradeCyclesToCycles, mem_boundaries_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact exists_homogeneous_of_mem_boundaries 𝒜 d x.1.property ⟨y, hy⟩
  · rintro ⟨y, -, hdy⟩
    exact ⟨y, hdy⟩

/-- The degree-`n` homology is the degree-`n` graded piece of the total homology. -/
public noncomputable def gradeHomologyEquivTotalGrade (n : ℕ) :
    gradeHomology 𝒜 d n ≃ₗ[R] totalHomologyGrade 𝒜 d n :=
  (Submodule.quotEquivOfEq _ _ (ker_gradeCyclesToHomology 𝒜 d n).symm).trans
    ((LinearMap.quotKerEquivRange (gradeCyclesToHomology 𝒜 d n)).trans
      (LinearEquiv.ofEq _ _ (totalHomologyGrade_eq_range 𝒜 d n).symm))

/-- `gradeHomologyEquivTotalGrade` sends the class of a degree-`n` cycle `y` to the class of `y` in
the total homology. -/
@[simp]
public theorem gradeHomologyEquivTotalGrade_mk (n : ℕ) (y : cycles d) (hy : (y : A) ∈ 𝒜 n) :
    (gradeHomologyEquivTotalGrade 𝒜 d n
        (Submodule.Quotient.mk ⟨⟨(y : A), hy⟩, y.property⟩) : Homology (𝒜 := 𝒜) d) =
      Submodule.Quotient.mk y :=
  rfl

end DividedPowers.TateResolution

end
