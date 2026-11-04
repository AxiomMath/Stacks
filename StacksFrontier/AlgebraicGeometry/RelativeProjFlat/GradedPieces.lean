module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlatOverBase

/-!
# Flatness of the graded pieces of a quasi-coherent graded algebra over the base

Let `A` be a quasi-coherent graded `𝒪_S`-algebra, in the sheaf-level form of Situation 01NN. Its
homogeneous piece `A_n` is a quasi-coherent `𝒪_S`-module, and the assertion that it is a flat
`𝒪_S`-module is `AlgebraicGeometry.IsFlatOver` for the identity of the base. This file translates
that assertion into commutative algebra: over an affine open `U` of the base, the degree-`n`
summand of the graded ring of sections `A(U)` is a flat module over `Γ(S, U)`, and consequently
the degree-zero localization of `A(U)` at a homogeneous element of positive degree is a flat
`Γ(S, U)`-algebra as soon as the pieces of all large degrees are flat.

The second statement is the local form of Stacks tag 0D4C.

## Main results

* `AlgebraicGeometry.flat_sections_of_isFlatOver_id`: a quasi-coherent module which is flat over
  its own scheme has flat modules of sections over affine opens.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.gradingEquiv`: the degree-`n`
  summand of the ring of sections is the sections of the degree-`n` piece, `Γ(S, U)`-linearly.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.toGradeZero_eq`: the two
  descriptions of the structure map into the degree-zero summand agree.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.flat_grading`: the degree-`n`
  summand is a flat `Γ(S, U)`-module when `A_n` is a flat `𝒪_S`-module.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.flat_away`: the degree-zero
  localization at a homogeneous element of positive degree is a flat `Γ(S, U)`-algebra when the
  pieces of all large degrees are flat.

## Implementation notes

The `Γ(S, U)`-algebra structure on the graded ring of sections is the one its structure map
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` defines, and it is
introduced by `let` rather than globally: the ring of sections is a direct sum, so a global
instance keyed on it would apply to direct sums generally. Everything below that mentions it
carries the `let` in its statement for the same reason.

The degree-`n` summand of the ring of sections is an `AddSubgroup`, namely the range of the
inclusion of the summand, and `GradedRing.toSubmodules` is what makes it a `Γ(S, U)`-submodule;
the identification with `Γ(A_n, U)` is the range restriction of that inclusion.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u

namespace AlgebraicGeometry

/-- The identity morphism of a scheme acts on sections over an open as the identity ring map. -/
public theorem Scheme.Hom.id_appLE_hom {S : Scheme.{u}} (U : S.Opens) :
    ((𝟙 S : S ⟶ S).appLE U U le_rfl).hom = RingHom.id Γ(S, U) := by
  have h1 : (𝟙 S : S ⟶ S).appLE U U le_rfl = (𝟙 S : S ⟶ S).app U :=
    Scheme.Hom.appLE_eq_app _
  rw [h1, Scheme.Hom.id_app]
  rfl

/-- **The sections of a quasi-coherent module over an affine open are flat over the functions on
that open, when the module is flat over its own scheme.** -/
public theorem flat_sections_of_isFlatOver_id {S : Scheme.{u}} (F : S.Modules)
    [F.IsQuasicoherent] (hF : IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom F)
    (U : S.Opens) (hU : IsAffineOpen U) :
    Module.Flat Γ(S, U) Γ(F, U) := by
  have hcrit := ((isFlatOver_tfae (𝟙 S : S ⟶ S) F).out 1 2).mp hF
  have h := hcrit U hU U hU le_rfl
  rwa [Scheme.Hom.id_appLE_hom U] at h

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

open Stacks.AlgebraicGeometry.RelativeProjBridge

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- The `Γ(S, U)`-algebra structure on the graded ring of sections over an open, defined by the
structure map of the graded algebra. -/
@[instance_reducible]
public def sectionRingAlgebra : Algebra Γ(S, U) (A.sectionRing U) :=
  (A.strHom U).toAlgebra

/-- **The degree-`n` summand of the ring of sections is the sections of the degree-`n` piece,**
`Γ(S, U)`-linearly. The map is the inclusion of the summand, corestricted to its range. -/
public def gradingEquiv (n : ℕ) :
    letI := A.sectionRingAlgebra U
    A.sectionPieces U n ≃ₗ[Γ(S, U)]
      GradedRing.toSubmodules (A.grading U) (A.strHom_mem U) n :=
  letI := A.sectionRingAlgebra U
  { __ := AddMonoidHom.ofInjective (DirectSum.of_injective (β := A.sectionPieces U) n)
    map_smul' r y := Subtype.ext (A.strHom_mul_of U r y).symm }

include A in
/-- **The corestriction of the structure map to degree zero is the degree-zero projection of the
structure map.** -/
public theorem toGradeZero_eq :
    letI := A.sectionRingAlgebra U
    GradedRing.toGradeZero (A.grading U) (A.strHom_mem U) =
      (GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U) :=
  let := A.sectionRingAlgebra U
  RingHom.ext fun r =>
    (GradedRing.projZeroRingHom'_apply_coe _ ⟨_, A.strHom_mem U r⟩).symm

include A in
/-- **The degree-`n` summand of the ring of sections over an affine open is a flat
`Γ(S, U)`-module** when the degree-`n` piece of the graded algebra is a flat `𝒪_S`-module. -/
public theorem flat_grading {n : ℕ}
    (hflat : IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ)))
    (hU : IsAffineOpen U) :
    letI := A.sectionRingAlgebra U
    Module.Flat Γ(S, U) (GradedRing.toSubmodules (A.grading U) (A.strHom_mem U) n) :=
  let := A.sectionRingAlgebra U
  (Module.Flat.equiv_iff (A.gradingEquiv U n)).mp
    (flat_sections_of_isFlatOver_id (A.piece (n : ℤ)) hflat U hU)

include A in
/-- **The degree-zero localization of the ring of sections at a homogeneous element of positive
degree is a flat `Γ(S, U)`-algebra** when all the homogeneous pieces of the graded algebra of
large enough degree are flat `𝒪_S`-modules. -/
public theorem flat_away (N : ℕ)
    (hflat : ∀ n : ℕ, N ≤ n →
      IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ)))
    (hU : IsAffineOpen U) {d : ℕ} (hd : 0 < d) {f : A.sectionRing U}
    (hf : f ∈ A.grading U d) :
    RingHom.Flat ((fromZeroRingHom (A.grading U) (Submonoid.powers f)).comp
      (GradedRing.projZeroRingHom' (A.grading U) |>.comp (A.strHom U))) := by
  let _ := A.sectionRingAlgebra U
  rw [← A.toGradeZero_eq U]
  exact Away.flat_fromZeroRingHom_comp (A.grading U) (A.strHom_mem U) f hf N
    fun n hn => A.flat_grading U (hflat (n • d) (hn.trans (Nat.le_mul_of_pos_right n hd))) hU

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

end
