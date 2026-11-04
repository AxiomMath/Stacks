module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage

/-! # The two shift binders of the internal-hom dévissage are a composition

The dévissage of Stacks 08I3/0GM7 in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage` runs
over the two functors

`comparisonSourceFunctor P H₁ F = H₁.flip.obj F ⋙ P`  and
`comparisonTargetFunctor P H₂ F = P.op ⋙ H₂.flip.obj (P.obj F)`

of `D₁ᵒᵖ`, and carries a `CategoryTheory.Functor.CommShift ℤ` for each of them as an instance
binder it cannot discharge.  This file discharges both from the commutation of the *contravariant
internal hom* `H.flip.obj -` with the shift, together with the commutation of `P`: the first is a
composition of functors, and the second is a composition in which the opposite functor `P.op`
commutes with the shift by Mathlib's
`CategoryTheory.Pretriangulated.Opposite.commShiftFunctorOpInt`.

Everything here is over arbitrary categories with a shift, so it is free of the recursion-depth
cost that the same identification carries at the derived categories of module sheaves on a
ringed space.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.commShift_comparisonSourceFunctor`
* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.commShift_comparisonTargetFunctor`

## What this settles, and what it does not

The dévissage's conclusion
`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_generatedByOp`
carries *five* shift data: a `CategoryTheory.Functor.CommShift` and a
`CategoryTheory.Functor.IsTriangulated` for each of the two comparison functors, and a
`CategoryTheory.NatTrans.CommShift` for `derivedPullbackSheafHomNatTrans`.  The two declarations
below discharge exactly the two `CommShift` binders, given the commutation of `RSheafHom(-, M)`
with the shift.  The two `IsTriangulated` binders and the `NatTrans.CommShift` are *not*
consequences of them: `CategoryTheory.Functor.IsTriangulated` of a composite needs each factor
to be triangulated, which for `RSheafHom(-, M)` is a statement strictly stronger than the
existential exactness
`Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first` the development has — see the
implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness` on why
`map_distinguished` asks for a *specific* connecting morphism — and the shift compatibility of
`derivedPullbackSheafHomNatTrans` is a further statement about that transformation.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Pretriangulated.Opposite

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  (P : D₁ ⥤ D₂) [P.CommShift ℤ] (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)

/-- **The source side of the dévissage commutes with the shift.**  It is
`H₁.flip.obj F ⋙ P`, so the commutation of the contravariant internal hom into `F` and the
commutation of `P` compose. -/
@[instance_reducible]
def commShift_comparisonSourceFunctor (F : D₁) [(H₁.flip.obj F).CommShift ℤ] :
    (comparisonSourceFunctor P H₁ F).CommShift ℤ :=
  inferInstanceAs ((H₁.flip.obj F ⋙ P).CommShift ℤ)

/-- **The target side of the dévissage commutes with the shift.**  It is
`P.op ⋙ H₂.flip.obj (P.obj F)`, and `P.op` commutes with the shift for the opposite shift of
`CategoryTheory.Pretriangulated.Opposite` whenever `P` does, so again the two compose. -/
@[instance_reducible]
def commShift_comparisonTargetFunctor (F : D₁) [(H₂.flip.obj (P.obj F)).CommShift ℤ] :
    (comparisonTargetFunctor P H₂ F).CommShift ℤ :=
  inferInstanceAs ((P.op ⋙ H₂.flip.obj (P.obj F)).CommShift ℤ)

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose

end
