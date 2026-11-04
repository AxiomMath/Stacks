module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DirectSummandsGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject

/-!
# A retract of a perfect object of `D(O)` on a ringed site is perfect

Let `(C, O)` be a ringed site and let `M` be a *retract* of an object `K` of `D(O)`: there are
`i : M ⟶ K` and `r : K ⟶ M` with `i ≫ r = 𝟙 M`. If `K` is perfect (Stacks 08G5) then so is `M`.

Stacks 08GA is the biproduct form of this — both summands of a perfect biproduct are perfect —
and it is proved, for the ringed site, as
`Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_left_of_biprod_general`. The retract form is
what a factorization argument produces, and nothing in the site development turned a retract in
`D(O)` into a biproduct decomposition. That step is supplied here.

Nothing below is a clause of a tag: the biproduct form of Stacks 08GA carries the tag where it is
proved, and these are a strengthening and a transport, so no `@[stacks …]` attribute is attached.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_of_iso`: perfectness of an object of `D(O)` transports
  along an isomorphism. Immediate from Stacks 08G5, which asks for a perfect complex together
  with an isomorphism from its image, and the only reason it is stated is that the site
  development had no such transport and the retract argument needs one.
* `Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract_general`: **a retract of a
  perfect object of `D(O)` is perfect.**

## What this is made of

`CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction`, stated for an arbitrary
pretriangulated category in
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject`, splits the
retract into a biproduct — `D(O)` is pretriangulated — and Stacks 08GA then applies to the first
summand. The splitting is the one the ringed-space form
`Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract` of that module uses.

This is the conclusion half of the direct-summand step of the proof of Stacks 0FPV, first
assertion; the monoidal half is `CategoryTheory.ExactPairing.retractOfCoevaluationFactors`, and
the two are composed in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualDirectSummand`.

## Implementation notes

**Two universe seats.** The transport `isPerfect_of_iso` is stated where Stacks 08G5 is, at a
ringed site `RingedSite.{u, v, w}` with the module sections in an independent universe `m`. The
retract statement is stated where Stacks 08GA is, on the diagonal `RingedSite.{u, u, u}`: the
biproduct form it reduces to is stated there, for the reason recorded in the implementation notes
of `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/PerfectnessCriterion.lean` — the flat
representative of an object of finite Tor amplitude and the flatness of a direct summand of a
finite free module both want the structure-sheaf sections in `max u v`, which on the diagonal is
the universe the module sections live in.

The instance block is the one Stacks 08GA is stated under, which is why this file is separate
from the statement of the transport: the three layers of slices it carries are needed for the
biproduct form and for nothing else here.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08GA](https://stacks.math.columbia.edu/tag/08GA)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w m d

namespace AlgebraicGeometry.RingedSite

section Transport

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify X.J AddCommGrpCat.{m}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **Perfectness of an object of `D(O)` transports along an isomorphism.** Stacks 08G5 asks for
a perfect complex together with an isomorphism from its image to the object, so an isomorphism of
objects is absorbed into that isomorphism. -/
theorem isPerfect_of_iso
    {K L : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : X.IsPerfect K) (e : K ≅ L) : X.IsPerfect L := by
  obtain ⟨E, hE, ⟨f⟩⟩ := h
  exact ⟨E, hE, ⟨f ≪≫ e⟩⟩

end Transport

end AlgebraicGeometry.RingedSite

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

variable
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).Additive]
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

/-- **A retract of a perfect object of `D(O)` is perfect.** Let `(C, O)` be a ringed site and let
`i : M ⟶ K` admit a retraction `r : K ⟶ M`. If `K` is perfect then so is `M`.

The retract is split into a biproduct `K ≅ M ⊞ W` by
`CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction`, perfectness is carried across
that isomorphism by `AlgebraicGeometry.RingedSite.isPerfect_of_iso`, and Stacks 08GA,
`Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_left_of_biprod_general`, reads perfectness
off the first summand. -/
theorem isPerfect_of_retract_general {M K : RingedSite.DerivedModules.{u, u, u, d} Z}
    (i : M ⟶ K) (r : K ⟶ M) (hir : i ≫ r = 𝟙 M) (hK : Z.IsPerfect K) :
    Z.IsPerfect M := by
  obtain ⟨W, e, -⟩ := CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction i r hir
  exact isPerfect_left_of_biprod_general M W (RingedSite.isPerfect_of_iso Z hK e)

end Stacks.SheafOfModules.DerivedTensorProduct

end
