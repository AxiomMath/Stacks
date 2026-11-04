module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DirectSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject

/-!
# A retract of a perfect object of `D(O)` is perfect

Let `(C, O)` be a ringed site and let `M` be a *retract* of an object `K` of `D(O)`: there are
`i : M ⟶ K` and `r : K ⟶ M` with `i ≫ r = 𝟙 M`. If `K` is perfect (Stacks 08G5) then so is `M`.

Stacks 08GA is the biproduct form of this — both summands of a perfect biproduct are perfect —
and it is `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_left_of_biprod` and
`isPerfect_right_of_biprod` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DirectSummands`. The retract form is what a
factorization argument produces, and nothing on the site side turned a retract in `D(O)` into a
biproduct decomposition. That step is supplied here.

Nothing below is a clause of a tag: Stacks 08GA carries its tag where it is proved, and this is a
reduction to it, so no `@[stacks …]` attribute is attached.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_iso`: perfectness of an object of
  `D(O)` transports along an isomorphism. Immediate from the shape of
  `AlgebraicGeometry.RingedSite.IsPerfect`, which asserts the existence of a perfect *complex*
  together with an isomorphism from its image.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract`: **a retract of a perfect
  object of `D(O)` is perfect**, with no hypothesis beyond the retraction.

## Implementation notes

The splitting of a retract is not redone here. It is
`CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject`, which is
stated for an arbitrary pretriangulated category and is therefore as usable on a site as on a
space: a map with a retraction is a monomorphism, the connecting map of a distinguished triangle
whose first map is a monomorphism vanishes, and a distinguished triangle with vanishing
connecting map exhibits its second vertex as a biproduct. That module is in the ringed-space tree
only because it was written for Stacks 0FPD; the statement used here mentions no space.

**Universes.** The ringed site is `RingedSite.{0, 0, 0}`, which is where Stacks 08GA is stated
and where the duality cluster of Stacks 0FPT, 0FPU and 0FPV lives, so the retract statement is
available exactly where its consumers are. The universes of Stacks 08GA are no obstruction to a
site-side retract statement: what it needs is the passage from a retract in `D(O)` to a biproduct
decomposition, which `exists_iso_biprod_of_retraction` supplies, and nothing in the argument asks
for a universe beyond the ones 08GA is stated at.

The instance arguments are exactly those of Stacks 08GA; the hypotheses on the twofold slices are
the ones that the biproduct lemmas carry, and they are not weakened here.

## References

* [Stacks Project, Tag 08GA](https://stacks.math.columbia.edu/tag/08GA)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{0, 0, 0}}
  [HasSheafify Z.J AddCommGrpCat.{0}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{0}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  critIterHasSheafify critIterWEq critTripleHasSheafify critTripleWEq

variable [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} Z)]
  [∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} (Z.over U))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived
  critIterDerived critIterRingSheafDerived

omit [∀ (U : Z.C) (W : Over U), HasSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Z.C, HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} (Z.over U))]
  [∀ (U : Z.C) (W : (Z.over U).C),
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W))] in
/-- **Perfectness of an object of `D(O)` transports along an isomorphism.**
`AlgebraicGeometry.RingedSite.IsPerfect K` asserts that some perfect complex has `K` as the
image of its class, so an isomorphism `K ≅ L` is composed onto that one. -/
theorem isPerfect_of_iso {K L : RingedSite.DerivedModules.{0, 0, 0, d} Z} (e : K ≅ L)
    (hK : Z.IsPerfect K) : Z.IsPerfect L := by
  obtain ⟨E, hE, ⟨f⟩⟩ := hK
  exact ⟨E, hE, ⟨f ≪≫ e⟩⟩

variable [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]
  [∀ (U : Z.C) (W : (Z.over U).C),
    (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0} ((Z.over U).over W).O).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0}
      ((Z.over U).over W).O).obj M).Additive]
  [∀ (U : Z.C) (W : (Z.over U).C)
    (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} ((Z.over U).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((Z.over U).over W).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor
  critIterTensorAdditive critIterTensorObjAdditive critIterHasMapBifunctor

/-- **A retract of a perfect object of `D(O)` is perfect.** If `i : M ⟶ K` admits a retraction
`r` and `K` is perfect (Stacks 08G5), then `M` is perfect.

The retract is turned into a direct summand by
`CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction` — `D(O)` is pretriangulated —
and then Stacks 08GA, `isPerfect_left_of_biprod`, applies; perfectness is carried across
the decomposition by `isPerfect_of_iso`.

This is the conclusion half of the direct-summand step of the proof of the first assertion of
Stacks 0FPV, where `M` is exhibited as a retract of a finitely generated subcomplex of a
representative of itself. -/
theorem isPerfect_of_retract {M K : RingedSite.DerivedModules.{0, 0, 0, d} Z}
    (i : M ⟶ K) (r : K ⟶ M) (hir : i ≫ r = 𝟙 M) (hK : Z.IsPerfect K) : Z.IsPerfect M := by
  obtain ⟨W, e, -⟩ := exists_iso_biprod_of_retraction i r hir
  exact isPerfect_left_of_biprod M W (isPerfect_of_iso e hK)

end Stacks.SheafOfModules.DerivedTensorProduct

end
