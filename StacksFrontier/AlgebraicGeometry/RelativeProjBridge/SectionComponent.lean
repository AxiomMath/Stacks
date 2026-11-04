module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing

/-!
# Homogeneous sections and the internal grading of the section ring

Let `𝒜` be a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN) and `U` an open of `S`. Its
graded ring of sections over `U` is presented twice:

* as the direct sum `A = ⨁_{n ≥ 0} Γ(𝒜_n, U)` of the modules of homogeneous sections, the
  summands being `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces`;
* as a ring with an internal grading by the additive subgroups
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading`.

An element of the degree-`n` subgroup is the summand inclusion of its degree-`n` component, so the
two presentations of each degree agree as additive groups, and under that identification
multiplication by the image of `r : Γ(S, U)` in degree `0` is the module action of `r` on
homogeneous sections.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.ofGrading`: the summand
  inclusion `Γ(𝒜_n, U) →+ A_n`, valued in the degree-`n` subgroup.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.componentEquiv`: the
  degree-`n` part of the section ring is the module of degree-`n` homogeneous sections, as
  additive groups.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.gradeZeroHom`: the structure map
  `Γ(S, U) →+* A_0`, corestricted to the degree-`0` part of the section ring.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.coe_ofGrading_smul`: the
  degree-`0` scalar of `r` multiplies a homogeneous section by acting on it.

## Implementation notes

The ring structure on the degree-`0` part is Mathlib's `SetLike.GradeZero.instCommRing` for the
internal grading.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-! ### The two presentations of a homogeneous degree -/

/-- The summand inclusion of the degree-`n` homogeneous sections into the degree-`n` part of the
section ring. -/
public noncomputable def ofGrading (n : ℕ) : A.sectionPieces U n →+ A.grading U n :=
  (DirectSum.of (A.sectionPieces U) n).rangeRestrict

/-- The image of `ofGrading` in the section ring is the summand inclusion. -/
@[simp]
public theorem coe_ofGrading {n : ℕ} (y : A.sectionPieces U n) :
    ((A.ofGrading U n y : A.grading U n) : A.sectionRing U)
      = DirectSum.of (A.sectionPieces U) n y := rfl

/-- An element of the degree-`n` part of the section ring is the summand inclusion of its
degree-`n` component. -/
public theorem of_component {n : ℕ} (a : A.grading U n) :
    DirectSum.of (A.sectionPieces U) n ((a : A.sectionRing U) n) = (a : A.sectionRing U) := by
  obtain ⟨y, hy⟩ := a.2
  rw [← hy, DirectSum.of_eq_same]

/-- The degree-`n` part of the section ring is the module of degree-`n` homogeneous sections, as
additive groups, by taking the degree-`n` component. -/
public noncomputable def componentEquiv (n : ℕ) : A.grading U n ≃+ A.sectionPieces U n where
  toFun a := (a : A.sectionRing U) n
  invFun y := A.ofGrading U n y
  left_inv a := Subtype.ext (A.of_component U a)
  right_inv y := DirectSum.of_eq_same n y
  map_add' _ _ := rfl

/-- `componentEquiv` takes the degree-`n` component. -/
@[simp]
public theorem componentEquiv_apply (n : ℕ) (a : A.grading U n) :
    A.componentEquiv U n a = (a : A.sectionRing U) n := rfl

/-- The inverse of `componentEquiv` is `ofGrading`. -/
@[simp]
public theorem componentEquiv_symm_apply (n : ℕ) (y : A.sectionPieces U n) :
    (A.componentEquiv U n).symm y = A.ofGrading U n y := rfl

/-! ### The degree-zero scalars -/

/-- The structure map `Γ(S, U) ⟶ A_0`, the corestriction of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` to the degree-`0` part of
the section ring. -/
public noncomputable def gradeZeroHom : Γ(S, U) →+* A.grading U 0 where
  toFun r := ⟨A.strHom U r, A.strHom_mem U r⟩
  map_one' := Subtype.ext (map_one (A.strHom U))
  map_mul' r s := Subtype.ext (map_mul (A.strHom U) r s)
  map_zero' := Subtype.ext (map_zero (A.strHom U))
  map_add' r s := Subtype.ext (map_add (A.strHom U) r s)

/-- The image of `gradeZeroHom U r` in the section ring is `strHom U r`. -/
@[simp]
public theorem coe_gradeZeroHom (r : Γ(S, U)) :
    ((A.gradeZeroHom U r : A.grading U 0) : A.sectionRing U) = A.strHom U r := rfl

/-- The summand inclusion of `r • y` is the product, in the section ring, of the summand inclusion
of `y` with the degree-`0` scalar of `r`. -/
public theorem coe_ofGrading_smul {n : ℕ} (r : Γ(S, U)) (y : A.sectionPieces U n) :
    ((A.ofGrading U n (r • y) : A.grading U n) : A.sectionRing U)
      = ((A.ofGrading U n y : A.grading U n) : A.sectionRing U)
        * ((A.gradeZeroHom U r : A.grading U 0) : A.sectionRing U) :=
  (A.strHom_mul_of U r y).symm.trans (_root_.mul_comm _ _)

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
