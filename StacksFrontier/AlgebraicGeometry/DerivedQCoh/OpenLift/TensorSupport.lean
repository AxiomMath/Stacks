module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.RestrictionSpellings
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenSubspaceBaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASlice

/-!
# The derived tensor product preserves a closed support

Let `X` be a scheme, `V ⊆ X` an open and `E` an object of `D(𝒪_X)` whose cohomology is supported
on the closed set `X \ V`. Then so is `K ⊗^L_{𝒪_X} E`, for every object `K` of `D(𝒪_X)`: the
objects supported on a closed subset form a tensor ideal.

The reason is that cohomological support on the complement of an open is the same thing as
vanishing after restriction to that open
(`Stacks.DerivedQCoh.isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl` and
`Stacks.DerivedQCoh.cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict`), that the derived
tensor product commutes with restriction to an open
(`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso`), and that tensoring with a
fixed object is an exact, hence additive, functor and so carries a zero object to a zero object.

This is what step 6 of [Stacks, Tag 08EK] runs on: there the object supported on the closed set
`T` is an iterated cone `C_s`, the second factor is the perfect object `I` produced by
[Stacks, Tag 08EH], and what has to be known is that `C_s ⊗^L I` is still supported on `T`.

## Main results

* `Stacks.DerivedTensor.SliceRestriction.isZero_restriction_derivedTensor_of_isZero_restriction`:
  the statement on a ringed site, in the vanishing-after-restriction form. This is the
  mathematical content.
* `Stacks.DerivedQCoh.OpenLift.isZero_sliceDerivedRestrict_iff`: the two spellings of
  "restricting to zero on an open of a scheme" agree.
* `Stacks.DerivedQCoh.OpenLift.cohomologySupportedOn_compl_derivedTensor`: the statement for a
  scheme, in the `AlgebraicGeometry.CohomologySupportedOn` form of [Stacks, Tag 08DA].

## Implementation notes

*The three spellings of restriction to an open, and why all three appear.* The derived tensor
product of [Stacks, Tag 06YU] is built on a ringed *site*, and its restriction compatibility is
stated for the slice site `Opens X / V`, whose modules are
`SheafOfModules ((structureSheaf Rc).over V)`. The support condition of [Stacks, Tag 08DA] is
stated for a scheme, whose restriction is `AlgebraicGeometry.Scheme.Modules.restrictFunctor` of
the open immersion `V ⟶ X`, landing in the modules on the open *subspace*. Between them sits
`Stacks.Cohomology.OpenSubspace.derivedRestriction`, the total right derived functor of
restriction to the subspace, which is the spelling [Stacks, Tag 08EH] and the rest of the
08EG--08EI chain are stated in.

`Stacks.DerivedQCoh.OpenLift.isZero_sliceDerivedRestrict_iff` crosses all three at once, on the
one predicate that is needed here. Going from the slice to the subspace is
`Stacks.SheafOfModules.derivedRestrictToSubspaceIso` together with the fact that the passage
between the two models of `𝒪_V`-modules is an equivalence, so it both preserves and reflects
zero objects; going from the subspace to the scheme is uniqueness of right derived functors,
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, composed with
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor` -- the same composite
that `Stacks.DerivedQCoh.derivedRestrictionOpenSubspace_linear` uses, here named
`Stacks.DerivedQCoh.OpenLift.schemeDerivedRestrictIsoOpenSubspace`.

The slice-site restriction functor of the derived tensor product,
`Stacks.DerivedTensor.ExtensionByZero.restriction (Stacks.SheafOfModules.ringedSite X.sheaf) V`,
is `SheafOfModules.overFunctor (structureSheaf X.sheaf) V` by `rfl`, so the statement on the
ringed site applies to `Stacks.SheafOfModules.derivedRestrict X.sheaf V` with no bridge.

*The derived tensor products are arbitrary data.* Both are carried as arguments, one on
`Opens X` and one on the slice `Opens X / V`, since [Stacks, Tag 06YU] is an existence statement
and only the comparison fields are used; the result therefore holds in particular at the
canonical datum of each site.

*No `@[stacks]` attribute.* [Stacks, Tag 08DA] defines the support condition and asserts nothing
about the tensor product, and no assertion of [Stacks, Tag 08EK] follows from what is below --
08EK needs this together with the iterated-cone construction, which is not here.

## References

* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)

namespace Stacks.DerivedTensor.SliceRestriction

universe d u

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]

/-- **The derived tensor product preserves vanishing after restriction to an open.** If the
restriction of `L` to the site over `U` is a zero object, so is the restriction of `K ⊗^L_O L`:
the two agree by `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso`, and tensoring
with a fixed object over `U` is an exact, hence additive, functor. -/
theorem isZero_restriction_derivedTensor_of_isZero_restriction
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    (K L : DerivedCategory (Modules X.O))
    (hL : IsZero ((restriction X U).mapDerivedCategory.obj L)) :
    IsZero ((restriction X U).mapDerivedCategory.obj ((T.tensor.obj K).obj L)) := by
  refine IsZero.of_iso ?_ (derivedTensorRestrictIso X U T TU K L)
  let := TU.commShift_right ((restriction X U).mapDerivedCategory.obj K)
  let := TU.exact_right ((restriction X U).mapDerivedCategory.obj K)
  exact Functor.map_isZero _ hL

/-- **The same in the left variable.** If the restriction of `K` to the site over `U` is a zero
object, so is the restriction of `K ⊗^L_O L`; tensoring with a fixed object in the right variable
is exact, hence additive. -/
theorem isZero_restriction_derivedTensor_of_isZero_restriction_left
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    (K L : DerivedCategory (Modules X.O))
    (hK : IsZero ((restriction X U).mapDerivedCategory.obj K)) :
    IsZero ((restriction X U).mapDerivedCategory.obj ((T.tensor.obj K).obj L)) := by
  refine IsZero.of_iso ?_ (derivedTensorRestrictIso X U T TU K L)
  let := TU.commShift_left ((restriction X U).mapDerivedCategory.obj L)
  let := TU.exact_left ((restriction X U).mapDerivedCategory.obj L)
  exact Functor.map_isZero (TU.tensor.flip.obj ((restriction X U).mapDerivedCategory.obj L)) hK

end Stacks.DerivedTensor.SliceRestriction

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.DerivedTensor.SliceRestriction
  (isZero_restriction_derivedTensor_of_isZero_restriction
   isZero_restriction_derivedTensor_of_isZero_restriction_left)

variable (X : Scheme.{u}) (V : X.Opens)

/-- **Restriction to an open subspace of a scheme, in the two derived spellings.** The functor
that degreewise restriction induces on derived categories is the chosen total right derived
functor of the same restriction; the comparison is uniqueness of right derived functors. This is
the isomorphism the proof of
`Stacks.DerivedQCoh.derivedRestrictionOpenSubspace_linear` is built on, given a name. -/
def schemeDerivedRestrictIsoOpenSubspace :
    Stacks.Duality.OpenImmersion.derivedRestrict V.ι ≅
      Stacks.Cohomology.OpenSubspace.derivedRestriction X.ringCatSheaf V :=
  (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X V).symm ≪≫
    Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
      (AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace V)

/-- **An object of `D(𝒪_X)` restricts to zero on the slice site over `V` exactly when it
restricts to zero on the open subscheme `V`.** The passage between the slice-site and the
open-subspace models of `𝒪_V`-modules is an equivalence, so it preserves and reflects zero
objects, and the two restrictions are identified through it by
`Stacks.SheafOfModules.derivedRestrictToSubspaceIso` and
`Stacks.DerivedQCoh.OpenLift.schemeDerivedRestrictIsoOpenSubspace`. -/
theorem isZero_sliceDerivedRestrict_iff (E : DerivedCategory X.Modules) :
    IsZero ((Stacks.SheafOfModules.derivedRestrict X.sheaf V).obj E) ↔
      IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) := by
  have hslice : IsZero ((Stacks.SheafOfModules.derivedRestrict X.sheaf V).obj E) ↔
      IsZero ((Stacks.SheafOfModules.sliceToSubspaceFunctor X.sheaf V).mapDerivedCategory.obj
        ((Stacks.SheafOfModules.derivedRestrict X.sheaf V).obj E)) := by
    refine ⟨fun h => Functor.map_isZero _ h, fun h => ?_⟩
    rw [IsZero.iff_id_eq_zero]
    refine (Stacks.SheafOfModules.sliceToSubspaceFunctor X.sheaf V).mapDerivedCategory.map_injective
      ?_
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 h
  rw [hslice]
  refine Iso.isZero_iff ?_
  exact ((Stacks.SheafOfModules.derivedRestrictToSubspaceIso X.sheaf V).app E) ≪≫
    ((schemeDerivedRestrictIsoOpenSubspace X V).app E).symm

/-- Support on the complement of `V` gives vanishing of the slice-site restriction to `V`. -/
private theorem isZero_sliceDerivedRestrict_of_cohomologySupportedOn_compl
    (E : DerivedCategory X.Modules)
    (hE : CohomologySupportedOn X.ringCatSheaf ((V : Set X)ᶜ) E) :
    IsZero ((Stacks.SheafOfModules.derivedRestrict X.sheaf V).obj E) :=
  (isZero_sliceDerivedRestrict_iff X V E).2
    (Stacks.DerivedQCoh.isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl
      ((V : Set X)ᶜ) V (by simp) E hE)

/-- Vanishing of the slice-site restriction to `V` gives support on the complement of `V`. -/
private theorem cohomologySupportedOn_compl_of_isZero_sliceDerivedRestrict
    (E : DerivedCategory X.Modules)
    (h : IsZero ((Stacks.SheafOfModules.derivedRestrict X.sheaf V).obj E)) :
    CohomologySupportedOn X.ringCatSheaf ((V : Set X)ᶜ) E :=
  Stacks.DerivedQCoh.cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict V _
    ((isZero_sliceDerivedRestrict_iff X V _).1 h)

/-- **The derived tensor product preserves a closed cohomological support.** If every cohomology
sheaf of `E` has vanishing stalks on the open `V`, the same holds for `K ⊗^L_{𝒪_X} E`.

Support on the complement of `V` is vanishing of the restriction to `V`, the derived tensor
product commutes with that restriction, and tensoring with a fixed object is additive. -/
theorem cohomologySupportedOn_compl_derivedTensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf).O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct
      ((Stacks.SheafOfModules.ringedSite X.sheaf).O.over V))
    (K E : DerivedCategory X.Modules)
    (hE : CohomologySupportedOn X.ringCatSheaf ((V : Set X)ᶜ) E) :
    CohomologySupportedOn X.ringCatSheaf ((V : Set X)ᶜ) ((T.tensor.obj K).obj E) :=
  cohomologySupportedOn_compl_of_isZero_sliceDerivedRestrict X V _
    (isZero_restriction_derivedTensor_of_isZero_restriction
      (Stacks.SheafOfModules.ringedSite X.sheaf) V T TU K E
      (isZero_sliceDerivedRestrict_of_cohomologySupportedOn_compl X V E hE))

/-- **The same with the support hypothesis on the left factor.** -/
theorem cohomologySupportedOn_compl_derivedTensor_left
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf).O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct
      ((Stacks.SheafOfModules.ringedSite X.sheaf).O.over V))
    (K E : DerivedCategory X.Modules)
    (hK : CohomologySupportedOn X.ringCatSheaf ((V : Set X)ᶜ) K) :
    CohomologySupportedOn X.ringCatSheaf ((V : Set X)ᶜ) ((T.tensor.obj K).obj E) :=
  cohomologySupportedOn_compl_of_isZero_sliceDerivedRestrict X V _
    (isZero_restriction_derivedTensor_of_isZero_restriction_left
      (Stacks.SheafOfModules.ringedSite X.sheaf) V T TU K E
      (isZero_sliceDerivedRestrict_of_cohomologySupportedOn_compl X V K hK))

end Stacks.DerivedQCoh.OpenLift

end
