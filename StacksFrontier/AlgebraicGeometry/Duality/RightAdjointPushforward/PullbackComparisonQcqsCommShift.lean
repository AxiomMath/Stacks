module

public import
 StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidalCommShift
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonQcqsTriangles
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwoField
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalModelsCommShift
import StacksCore.Tactic.StacksAttribute

/-!
# Equation 48.8.0.1 is compatible with distinguished triangles

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes and `a = f^×` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. The map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`

of Equation 48.8.0.1 ([Stacks, Tag 0A9S]), `Stacks.Duality.qcqsCompareWithPullback`, is a morphism
of exact functors of `K` which commutes with the shift; so it is compatible with distinguished
triangles.

The one input that
`Stacks.Duality.commShift_qcqsCompareWithPullback_of_commShift_oplaxNatTransLeft` leaves open is
that the tensorator `Lf^*(K ⊗ᴸ M) ⟶ Lf^*K ⊗ᴸ Lf^*M` of `Lf^*` on `D_QCoh` commutes with the shift
in `K`. On `D(𝒪)` at the locally small model this is
`Stacks.Cohomology.DerivedPullbackTensor.commShift_derivedPullbackCanonicalMonoidalδLeft`, the
comparison of [Stacks, Tag 079U] transported from the standard model; the commutation of the
derived tensor product with the shift used there is the transported one, which is the structure
field of the derived tensor product by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`; and
`Stacks.Duality.commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback_of` restricts it to
`D_QCoh`.

## Main results

* `Stacks.Duality.commShift_derivedPullbackTensoratorLeft`: the tensorator of `Lf^*` on `D(𝒪)`
  commutes with the shift in its first variable.
* `Stacks.Duality.commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback`: the same on
  `D_QCoh`.
* `Stacks.Duality.commShift_qcqsCompareWithPullback`: **[Stacks, Tag 0A9S]**, compatibility of
  Equation 48.8.0.1 with distinguished triangles.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The structure-field commutation of `- ⊗ᴸ M` with the shift is the transported one. -/
theorem commShiftDerivedTensorFlipObj_eq (Z : Scheme.{u}) (M : DerivedCategory Z.Modules) :
    commShiftDerivedTensorFlipObj Z M =
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int
        Z.toRingedSpace.sheaf).commShiftFlipObj M := by
  exact congrArg (fun d => d.commShiftFlipObj M)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq
      Z.toRingedSpace.sheaf)

/-- **The tensorator of `Lf^*` on `D(𝒪)` commutes with the shift in its first variable**, at the
locally small model, for the left derived commutation of `Lf^*` with the shift and the
commutation of the derived tensor product with the shift. -/
theorem commShift_derivedPullbackTensoratorLeft (M : DerivedCategory Y.Modules) :
    letI : (derivedPullback f).CommShift ℤ :=
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift
        f.toLRSHom.toShHom
    letI := commShiftDerivedTensorFlipObj Y M
    letI := commShiftDerivedTensorFlipObj X ((derivedPullback f).obj M)
    NatTrans.CommShift (show (derivedTensor Y).flip.obj M ⋙ derivedPullback f ⟶
        derivedPullback f ⋙ (derivedTensor X).flip.obj ((derivedPullback f).obj M) from
      Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidalδLeft
        f.toLRSHom.toShHom M) ℤ := by
  have h := Stacks.Cohomology.DerivedPullbackTensor.commShift_derivedPullbackCanonicalMonoidalδLeft
    f.toLRSHom.toShHom M
  exact NatTrans.commShift_of_eq_data (by rw [commShiftDerivedTensorFlipObj_eq]; rfl)
    (by rw [commShiftDerivedTensorFlipObj_eq]; rfl) _ h

/-- **The tensorator of `Lf^*` on `D_QCoh` commutes with the shift in its first variable**, for
the commutation of `Lf^*` with the shift as the left adjoint of `Rf_*` and that of the derived
tensor product. -/
theorem commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (M : quasiCoherentDerivedCategory Y) :
    letI := quasiCoherentDerivedMonoidal X
    letI := quasiCoherentDerivedMonoidal Y
    letI := quasiCoherentDerivedPullbackMonoidal f
    letI := commShift_quasiCoherentDerivedPullback f
      (isQuasicoherent_homology_derivedPullback' f) hpush
    NatTrans.CommShift
      (MonoidalProjectionFormula.oplaxNatTransLeft (quasiCoherentDerivedPullback' f) M) ℤ :=
  commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback_of f hpush M
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidalδLeft
      f.toLRSHom.toShHom M.obj)
    (fun K => (derivedPullbackCanonicalMonoidal_δ_eq f K M.obj).symm)
    (commShift_derivedPullbackTensoratorLeft f M.obj)

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **[Stacks, Tag 0A9S]: Equation 48.8.0.1 is compatible with distinguished triangles.** For a
morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes, the map
`Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` commutes with the shift, `Lf^*` carrying its commutation with
the shift as the left adjoint of `Rf_*` and `a` its commutation as the right adjoint of `Rf_*`.
Its source and target are exact functors (`isTriangulated_qcqsCompareWithPullback_source`,
`isTriangulated_qcqsTwistedInverseImage`), so it is a morphism of exact functors. -/
@[stacks 0A9S "compatible with distinguished triangles: the map of 48.8.0.1 commutes with the \
  shift, between exact functors"]
theorem commShift_qcqsCompareWithPullback :
    letI := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    letI := (twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).rightAdjointCommShift ℤ
    NatTrans.CommShift (qcqsCompareWithPullback f) ℤ :=
  commShift_qcqsCompareWithPullback_of_commShift_oplaxNatTransLeft f
    (fun M => commShift_oplaxNatTransLeft_quasiCoherentDerivedPullback f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) M)

end Stacks.Duality

end
