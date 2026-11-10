module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityAlongDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaLocalizationOnTheBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShifts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for a perfect complex on the base

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.  If
`K` is perfect — or, more generally, if `Y` has an open cover over whose members the derived
pullback of `K` is isomorphic to a strictly perfect complex — then the projection-formula
morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism.  This is [Stacks, Tag 0B54].

All names below are in the namespace `Stacks.Cohomology.DerivedProjectionFormula`.

## Main definitions

* `derivedPullbackRestrictModulesIso`: the derived pullback along the inclusion of an open
  subspace is the functor induced on derived categories by `StrictlyPerfect.restrictModules`.

## Main results

* `isIso_projectionFormulaMap_of_locallyStrictlyPerfect`: the projection-formula morphism is an
  isomorphism when `Y` has an open cover over whose members the derived pullback of `K` is
  isomorphic to a strictly perfect complex.
* `isIso_projectionFormulaMap_of_isPerfect`: the projection-formula morphism is an isomorphism
  when `K` is perfect in the sense of [Stacks, Tag 08CM].

## Implementation notes

`projectionFormulaMap` carries `HasSheafify` and `WEqualsLocallyBijective` hypotheses for the two
spaces.  They hold for every ringed space (`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`) but are not global instances, so
they appear as binders for `X` and `Y`.

## References

* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.ProjectionFormulaPerfect
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [local instance] StrictlyPerfect.preservesFiniteLimits_restrictModules
  StrictlyPerfect.preservesFiniteColimits_restrictModules

/-- **The projection formula for a complex locally isomorphic to a strictly perfect one on the
base**, for an arbitrary morphism of ringed spaces and an arbitrary `E ∈ D(𝒪_X)`.

If `⨆ i, U i = ⊤` and over each `U i` the derived pullback of `K` is isomorphic to a strictly
perfect complex, then the projection-formula morphism of [Stacks, Tag 0B53] at `E` and `K` is
invertible. -/
@[sga "6 IV 2.11.1" "more general"]
theorem isIso_projectionFormulaMap_of_locallyStrictlyPerfect
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {ι : Type*} (U : ι → Opens Y.carrier) (hU : iSup U = ⊤)
    (hK : ∀ i, ∃ P : CochainComplex (OXMod.{u, u} (Y.restrict (U i).isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧
        Nonempty ((derivedPullback (Y.ofRestrict (U i).isOpenEmbedding)).obj K ≅
          DerivedCategory.Q.obj P)) :
    IsIso (projectionFormulaMap f E K) := by
  refine Stacks.Cohomology.isIso_of_isIso_derivedPullback_ofRestrict U hU _ fun i => ?_
  obtain ⟨P, hP, ⟨e⟩⟩ := hK i
  let := Stacks.AssociatedSheaf.hasModuleSheafify.{u, u}
    (Y.restrict (U i).isOpenEmbedding)
  let := Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u}
    (Y.restrict (U i).isOpenEmbedding)
  let := Stacks.AssociatedSheaf.hasModuleSheafify.{u, u}
    (Limits.pullback f (Y.ofRestrict (U i).isOpenEmbedding))
  let := Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u}
    (Limits.pullback f (Y.ofRestrict (U i).isOpenEmbedding))
  have hsq : IsPullback (Limits.pullback.fst f (Y.ofRestrict (U i).isOpenEmbedding))
      (Limits.pullback.snd f (Y.ofRestrict (U i).isOpenEmbedding)) f
      (Y.ofRestrict (U i).isOpenEmbedding) :=
    IsPullback.of_hasPullback _ _
  exact isIso_derivedPullback_map_projectionFormulaMap _ _ f _ hsq.w E K
    (isIso_derivedBaseChangeMap_of_isOpenImmersions _ _ _ _ hsq E)
    (isIso_derivedBaseChangeMap_of_isOpenImmersions _ _ _ _ hsq _)
    (isIso_projectionFormulaMap_of_iso_right _ _ e.symm
      (isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit _ _ P hP))

/-! ### Tag 0B54 -/

/-- The derived pullback along the inclusion of an open subspace `U` of `Y` is isomorphic to the
functor induced on derived categories by the restriction functor
`StrictlyPerfect.restrictModules Y U`. -/
def derivedPullbackRestrictModulesIso (Y : RingedSpace.{u, u}) (U : Opens Y.carrier) :
    derivedPullback (Y.ofRestrict U.isOpenEmbedding) ≅
      (StrictlyPerfect.restrictModules Y U).mapDerivedCategory :=
  DerivedOpenImmersion.derivedPullbackModuleRestrictionIso Y U

/-- Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let
`E ∈ D(𝒪_X)` and let `K ∈ D(𝒪_Y)` be perfect.  Then the projection-formula morphism of
[Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism.

Perfectness is `Stacks.Cohomology.PerfectComplexes.IsPerfect` of [Stacks, Tag 08CM]: `K` is
represented by a complex which on the members of some open cover of `Y` receives a
quasi-isomorphism from a strictly perfect complex. -/
@[stacks 0B54, sga "6 IV 2.11.1" "more general"]
theorem isIso_projectionFormulaMap_of_isPerfect
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y) K) :
    IsIso (projectionFormulaMap f E K) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hK
  refine isIso_projectionFormulaMap_of_iso_right f E e ?_
  obtain ⟨I, U, hU, hlocal⟩ := hA
  refine isIso_projectionFormulaMap_of_locallyStrictlyPerfect f E _ U hU fun i => ?_
  obtain ⟨P, hP, q, hq⟩ := hlocal i
  have : QuasiIso q := hq
  exact ⟨P, hP, ⟨(derivedPullbackRestrictModulesIso Y (U i)).app (DerivedCategory.Q.obj A) ≪≫
    (StrictlyPerfect.restrictModules Y (U i)).mapDerivedCategoryFactors.app A ≪≫
      (asIso (DerivedCategory.Q.map q)).symm⟩⟩

end Stacks.Cohomology.DerivedProjectionFormula

end
