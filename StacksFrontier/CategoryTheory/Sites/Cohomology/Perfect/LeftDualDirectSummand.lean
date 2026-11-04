module

public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.RetractOfAPerfectObject

/-!
# The direct-summand step of Stacks 0FPV, first assertion

Let `(C, O)` be a ringed site, let `N` be a left dual of `M` in the monoidal category `D(O)` of
Stacks 0FPT — an exact pairing, Categories, Definition 0FFP — and suppose the coevaluation
`η : 𝟙 ⟶ M ⊗^L N` of the pairing factors as `coev ≫ f ▷ N = η_ M N` through `K ⊗^L N`, along a
morphism `f : K ⟶ M`. If `K` is perfect then `M` is perfect.

This is the step the source of Stacks 0FPV announces as "we are going to use the following
argument several times": a subcomplex `K^• ⊆ M^•` containing the finitely many sections occurring
in `η(1)` receives the coevaluation, and *"since the composition of the upper row is the identity
on `M` we conclude that `M` is a direct summand of `K` in `D(O)`"*.

Nothing below is a clause of a tag; this is a step of a proof, so no `@[stacks …]` attribute is
attached. No hypothesis below stands in for a theorem: `f`, `coev` and the factorization are
morphism data, and `hK` is perfectness of the object the coevaluation factors through, which the
source constructs rather than assumes.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_coevaluationFactors`: the statement
  above.

## What this is made of

* `CategoryTheory.ExactPairing.retractOfCoevaluationFactors`
  (`StacksFrontier.CategoryTheory.Monoidal.Rigid`) turns the factorization into a
  `CategoryTheory.Retract M K`. It is pure monoidal yoga — one of the two triangle identities and
  the unitors — and assumes nothing about `D(O)`.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract_general`
  (`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.RetractOfAPerfectObject`) carries
  perfectness back along the retract. It is Stacks 08GA strengthened from a biproduct to a
  retract, using that a retract in a pretriangulated category is a direct summand.

The ringed-space twin is `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_coevaluationFactors` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualDirectSummand`, the same
composition for the monoidal structure of Stacks 0FPB on a ringed space.

## Implementation notes

**The universe seat.** `RingedSite.{u, u, u}`. The monoidal structure
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` is available on the diagonal
`RingedSite.{u, u, u}` with the derived-category hom universe free, and Stacks 08GA — through
which perfectness travels back along the retract — is available on the same diagonal; the seat
below is therefore the common one, with no restriction beyond the diagonal itself. Why the
diagonal and not three free universes is recorded in the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/PerfectnessCriterion.lean`.

**The instance block** is the one Stacks 08GA is stated under, together with the tensor
additivity and total-complex hypotheses of the base site that the monoidal structure needs and
that Stacks 08GA asks for only on the slices.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08GA](https://stacks.math.columbia.edu/tag/08GA)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, u, u}}
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  critGenIterHasSheafify critGenIterWEq critGenTripleHasSheafify critGenTripleWEq

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Z)]
  [∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Z.over U))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived
  critGenIterDerived critGenIterRingSheafDerived

variable [∀ U : Z.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor
  critGenIterTensorAdditive critGenIterTensorObjAdditive critGenIterHasMapBifunctor


variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj A).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Z) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ)]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj A).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Z) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ)] in
/-- **The direct-summand step of Stacks 0FPV, first assertion.** Let `N` be a left dual of `M`
in `D(O)` for the monoidal structure of Stacks 0FPT, and suppose the coevaluation of the pairing
factors as `coev ≫ f ▷ N = η_ M N` through `K ⊗^L N`, along a morphism `f : K ⟶ M`. If `K` is
perfect then `M` is perfect.

The factorization makes `M` a retract of `K` —
`CategoryTheory.ExactPairing.retractOfCoevaluationFactors`, which is the triangle identity
`(1 ⊗ ε) ∘ (η ⊗ 1) = id` read through the factorization — and a retract of a perfect object is
perfect, `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract_general`. -/
theorem isPerfect_of_coevaluationFactors (M N K : RingedSite.DerivedModules.{u, u, u, d} Z)
    (hK : Z.IsPerfect K) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O
    ∀ [ExactPairing M N] (f : K ⟶ M)
      (coev : 𝟙_ (RingedSite.DerivedModules.{u, u, u, d} Z) ⟶ K ⊗ N),
      coev ≫ f ▷ N = η_ M N → Z.IsPerfect M := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O
  intro _ f coev hcoev
  let R := ExactPairing.retractOfCoevaluationFactors f coev hcoev
  exact isPerfect_of_retract_general R.i R.r R.retract hK

end Stacks.SheafOfModules.DerivedTensorProduct

end
