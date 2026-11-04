module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Excision for the local cohomology sheaves, in every degree

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an **open immersion** of ringed spaces, let `Z ⊆ X` be
closed and let `Z' = f^{-1}(Z)`.  The local cohomology sheaves `ℋ ⁿ_Z` of [Stacks, Tag 0G6N],
that is the right derived functors of the sections supported on `Z`, commute with pullback
along `f`:

`ℋ ⁿ_Z(ℱ)|_{Z'} ≅ ℋ ⁿ_{Z'}(f^*ℱ)`,

naturally in the `𝒪_X`-module `ℱ`.  That is `localCohomologySheafPullbackNatIso`, the main
result.  Here `(-)|_{Z'}` is pullback along the restriction
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)`, which is itself an open immersion by
`isOpenImmersion_closedSubsetRestriction`.

This is the derived excision of
`derivedSupportedSectionsOnClosedPullbackNatIso` read on degreewise cohomology: the degree-`n`
cohomology sheaf of `R𝓗_Z(ℱ[0])` *is* `ℋ ⁿ_Z(ℱ)` by
`localCohomologySheafOfComplexFunctorIso`, and the comparison built here is the one induced by
`supportedSectionsOnClosedPullbackNatIso`, which is also the single degreewise input the
derived comparison is built from.  See the implementation notes for what is and is not claimed
about that.

## Main results

* `localCohomologySheafPullbackNatIso`: **excision for `ℋ ⁿ_Z` along an open immersion of
  ringed spaces, in every degree.**

## Implementation notes

**The route, and why it is the same one the abelian excision takes.**  The proof is the
standard one and reuses the two derived-functor comparisons the project already has, so no
homological algebra is redone, and it is step for step the proof of
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` with the subsheaf `H_T`
of sections supported on `T` replaced by the functor `H_Z` of [Stacks, Tag 0G6N] on the closed
subset:

* `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` moves the pullback *out* of a right
  derived functor, using only that pullback along `f|_{Z'}` is exact: deriving `H_Z` and then
  pulling back is deriving the composite `H_Z(-)|_{Z'}`.
* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` ([Stacks, Tag 015Z]) moves
  the pullback *in*, using that pullback along `f` is exact and preserves injective objects:
  deriving `H_{Z'}(f^*(-))` is pulling back and then deriving `H_{Z'}`.

Composed along the degreewise comparison `supportedSectionsOnClosedPullbackNatIso`, these give
the result.  The mathematical content is therefore exactly the degreewise statement together
with the fact that pullback along an open immersion preserves injective objects, which is
`Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects`, i.e. that
the pullback of an injective resolution is again one.

**Only an open immersion, and where each half of that is used.**  `f` carries
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion` throughout.  Exactness of `f^*` and of
`(f|_{Z'})^*` comes from `Stacks.Cohomology.openImmersionModulePullback_preservesHomology`, the
preservation of injectives from
`Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects`, and the fact
that `f|_{Z'}` is an open immersion at all from
`isOpenImmersion_closedSubsetRestriction`.  Closedness of `Z` and of `Z'` is needed only for
`H_Z` and `H_{Z'}` to exist, exactly as in
`Stacks.Cohomology.SupportedComplexes.LocalCohomologyExcisionRingedSpace`.

**No `@[stacks ...]` attribute is attached to any declaration here**, exactly as none is
attached to `supportedSectionsOnClosedPullbackNatIso` or to
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`.  Excision in this shape
is not the statement of a tag: [Stacks, Tag 0G78] is the canonical *map*
`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`, and nothing below is compared with it; [Stacks,
Tag 0G7U] is base change for the supported map of a family of equations, of which this is one
input and not the statement.

**What is *not* claimed here.**  Three further statements are what a consumer of
[Stacks, Tag 0G7U] *in the abelian spelling* needs on top of this, and none of them is proved in
this module; the first of them is now proved, in the sibling module
`LocalCohomologySheafExcisionDerived.lean`.
None of them is needed by the Gysin globalisation of [Stacks, Tag 0G86]: since
`Stacks.Gysin.gysinTarget` is the degree-`c` cohomology sheaf of `i_* R𝓗_Z(ℱ[0])` in the
spelling `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, the chart transport
there is `Stacks.Perfect.SupportPushExcision.supportPushPullbackIso` with
`DerivedCategory.homologyFunctor _ c` applied to it — that is
`Stacks.Gysin.supportCohomologyRestrictIso` — and
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso` no longer
appears in the chart chain, so the comparison built here is not one of the two sides of any
match that globalisation has to make.

* The comparison built here is not compared *in this module* with the unbounded derived
  comparison `derivedSupportedSectionsOnClosedPullbackNatIso` whiskered into
  `DerivedCategory.homologyFunctor _ n` and read across
  `localCohomologySheafOfComplexFunctorIso`.  Both are induced by the single degreewise
  isomorphism `supportedSectionsOnClosedPullbackNatIso`, the first through
  `Functor.rightDerived` and the second through `CategoryTheory.Functor.rightDerivedNatIso`.

  **That comparison is now proved**, in the sibling module
  `LocalCohomologySheafExcisionDerived.lean`, as
  `derivedSupportedSectionsOnClosedPullbackNatIso_eq_classical` of this namespace, whose
  abstract form — the same square for an arbitrary `δ : w ⋙ G ≅ F ⋙ w'` — is
  `Stacks.DerivedIndexing.derivedExcisionSquare`.  What it took is three coherences for
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, one per factor of the
  comparison built above, together with the identification of the two spellings of
  `rightDerivedCompIso` for a general comparison
  (`Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso`).  Writing `H_Z` for
  `supportedSectionsOnClosedFunctor`, `H_{Z'}` for its counterpart on `X'`, `F = f^*` and
  `G = (f|_{Z'})^*`, the comparison above is `rightDerivedCompIso` for
  `δ : H_Z ⋙ G ≅ F ⋙ H_{Z'}` followed by `compRightDerivedNatIso`, and the derived one is the
  derived pullback comparisons around `CategoryTheory.Functor.rightDerivedNatIso` taken at the
  derived-category form of the same `δ`.  So the three are:

  - *the degreewise comparison itself*: that the bridge carries the morphism of right derived
    functors on the unbounded derived category which the universal property produces from `δ` to
    `CategoryTheory.NatTrans.rightDerived δ`.  This is
    `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality`, proved, and
    `Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso` in the same module transports the
    units so that it applies at the shape in which the units of
    `derivedSupportedSectionsOnClosedPullbackNatIso` are presented.
  - *post-composition with an exact functor*: that the bridge for `H_Z ⋙ G` taken at
    `R𝓗_Z ⋙ G.mapDerivedCategory` is the bridge for `H_Z`, read through
    `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
    `CategoryTheory.Functor.rightDerivedCompIso`.  **Proved**, as
    `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app`.  Its
    classical half — the `ℕ`-to-`ℤ` indexing coherence that
    `CategoryTheory.Functor.rightDerivedCompIso` needs — is
    `Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_comp_rightDerivedIsoRes`, which is what
    `Stacks.DerivedIndexing.homologyMap_mapExtendIso_hom_comp` was proved for; the two
    derived-category statements it needed on top of that are
    `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh` and the pair
    `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`,
    `Stacks.DerivedFunctor.postcomposeUnit_app` — the second of which discharges, for
    post-composition, the presupposition that the composite *is* a right derived functor.

    Two claims recorded here previously were wrong.  The comparison is
    `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, not
    `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` — those are two
    independent `CategoryTheory.Localization.liftNatIso`s of the same datum, and they are not
    identified either.  And the obstruction was recorded as Mathlib lacking component lemmas for
    `DerivedCategory.homologyFunctorFactorsh` and
    `CategoryTheory.Functor.mapDerivedCategoryFactorsh` at the class of a complex; Mathlib has
    both.
  - *pre-composition with an exact functor preserving injectives*: that the bridge for
    `F ⋙ H_{Z'}` taken at `F.mapDerivedCategory ⋙ R𝓗_{Z'}` is the bridge for `H_{Z'}` read
    through `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.  **Proved**, as
    `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp`, with its
    componentwise form `..._preComp_app`; the resolution content sits in
    `..._mapDerivedCategorySingleFunctor_comp_singleIsoResCompQh`, the unbounded analogue of the
    augmentation square.  Its classical half is
    `Stacks.DerivedIndexing.compRightDerivedNatIso_inv_app_comp_rightDerivedIsoRes`.

    The remaining half does not require identifying the unit of a
    right derived functor on the *unbounded* derived category with
    `Stacks.DerivedIndexing.extendResolutionComparison`: no such identification is needed, and
    invertibility of the unit at `F(resH X)` is never used.  Only the unit's *naturality* at the
    comparison of the two resolutions is used, and invertibility only at the two chosen
    resolutions, where `Stacks.DerivedFunctor.resCompUnitIso` already supplies it.  The heavy
    apparatus around equation (K) of `Homology/DerivedIndexing/Composite.lean` is what a
    derived functor *constructed* by `rightDerivedDesc` needs, its unit being reachable only
    through the universal property; it is not needed when the functor and unit are data.

    The comparison built above uses `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`,
    a `CategoryTheory.NatIso.ofComponents` through `isoRightDerivedObj`, which is a different
    spelling from `CategoryTheory.Functor.rightDerivedCompIso`.  The two are now identified, at
    the identity comparison by
    `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_refl` and for a general
    `e : F ⋙ G ≅ H` by `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso`, the two
    targets being related by `CategoryTheory.Functor.rightDerivedIsoOfNatIso e n`.  An earlier
    version of this note said the general case needed the `ModuleComparison` comparison for
    varying `H`; it does not — read on the chosen injective resolution it needs only that
    `CategoryTheory.NatTrans.rightDerived e.hom n` is there `e` applied termwise, which is
    Mathlib's `CategoryTheory.InjectiveResolution.rightDerived_app_eq`.

    That `F.mapDerivedCategory ⋙ R𝓗_{Z'}` is a right derived functor of `F ⋙ H_{Z'}` — what
    "taken at" means in the bullet above — is
    `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose`, whose unit is computed by
    `Stacks.DerivedFunctor.precomposeUnit_app`: that is the hypothesis `hα'` of the
    pre-composition coherence verbatim, so the coherence's hypotheses are dischargeable.
    Unlike the post-composition analogue it is not a consequence of absoluteness — it asks that
    `F` carry K-injective complexes to K-injective ones, which for restriction to an open subset
    holds by [Stacks, Tag 08BJ], extension by zero being an exact left adjoint
    (`Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`).
* Nothing is said about the direct image along the inclusion `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)`.  The
  spelling in which
  `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`
  and `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso` state the local cohomology
  sheaves is `ℋ ⁿ_Z ⋙ i_*`, and moving the pullback past `i_*` is the base-change isomorphism
  `i_* ⋙ f^* ≅ (f|_{Z'})^* ⋙ i'_*` of the Cartesian square of
  `isPullback_closedSubsetRestriction`.  That isomorphism **is in the library**, underived and
  for modules on ringed spaces: `Stacks.Cohomology.pushforwardRestrictMap` is the canonical
  base-change map of such a square and `Stacks.Cohomology.pushforwardRestrictMap_isIso` inverts
  it when the two relevant legs are open immersions.  It is instantiated at the closed-subset
  square as `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso`, whose
  `hom` is that canonical map definitionally, and with `ℋ ⁿ_Z ⋙ i_*` folded in as
  `...localCohomologySheafPushforwardPullbackNatIso`.

  Three claims recorded here previously were wrong, and are corrected rather than deleted
  because each sent work in a direction it did not need to go.  There is no declaration
  `Stacks.Cohomology.FlatBaseChange.moduleBaseChange` — every `moduleBaseChange` in the library
  is a structure field of the flattening development, an unrelated notion.  The underived
  statement was never missing, so this was not "the one genuinely geometric step left"; only its
  instantiation at this square was absent, and that is four associators.  And it does not amount
  to `f^*(i_*M)` lying in the essential image of `i'_*`: no support statement and no
  essential-image argument is involved, nor is the mate route
  `Stacks.Cohomology.DerivedBaseChange.isIso_mateEquiv_app_of_isIso_counit` needed.
* The two constructions of the degree-zero comparison in the library,
  `Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` here and
  `Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso` at a scheme and an
  open subscheme, **are identified**, by
  `Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso_hom_app_modulePullback`
  of `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset`
  `/LocalCohomologyExcisionPullback.lean`: they correspond under
  `Stacks.Gysin.modulePullbackRestrictFunctorIso`.  The two spellings,
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` on one side and
  `RingedSpaceModuleAdjunction.modulePullback` on the other, are not in the
  way of *this* statement: both comparisons are pinned down by compatibility with the inclusion
  into `ℱ|_{X'}`, which is a monomorphism
  (`Stacks.SheafOfModules.SupportedSections.supportedSectionsSheafι_mono`,
  `supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι` of this namespace
  and `Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso`'s
  `choose_spec`), and cancelling it needs no instance at a mixed spelling.  Where the spelling
  *does* stand in the way is the same crossing in every degree, for the right derived functors:
  see the implementation notes of `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/LocalCohomologyExcisionPullback.lean`.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-! ### Exactness of the two pullbacks -/

/-- Pullback along `f` preserves finite limits, `f` being an open immersion and so `f^*` exact. -/
theorem preservesFiniteLimits_modulePullback_of_isOpenImmersion :
    PreservesFiniteLimits (modulePullback f) :=
  let := Stacks.Cohomology.openImmersionModulePullback_preservesHomology f
  (modulePullback f).preservesFiniteLimits_of_preservesHomology

/-! ### Excision in every degree -/

/-- **Excision for the local cohomology sheaves.**  For an open immersion of ringed spaces
`f : X' ⟶ X`, a closed `Z ⊆ X`, `Z' = f^{-1}(Z)` and a degree `n`, the local cohomology sheaves
of [Stacks, Tag 0G6N] commute with pullback along `f`:

`ℋ ⁿ_Z(ℱ)|_{Z'} ≅ ℋ ⁿ_{Z'}(f^*ℱ)`,

naturally in the `𝒪_X`-module `ℱ`, the left-hand side being pullback along the restriction
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` of `f`.

This is the degreewise form of the derived excision
`derivedSupportedSectionsOnClosedPullbackNatIso`, induced by the same degreewise isomorphism
`supportedSectionsOnClosedPullbackNatIso`; no comparison of the two induced maps is claimed,
see the implementation notes. -/
@[sga "4 V 6.4" "Clause 1), special case"]
def localCohomologySheafPullbackNatIso (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z)) (n : ℕ) :
    localCohomologySheafFunctor X Z hZ n ⋙ modulePullback (closedSubsetRestriction f Z) ≅
      modulePullback f ⋙
        localCohomologySheafFunctor X' (closedSubsetPreimage f Z) hZ' n :=
  letI := Stacks.Cohomology.openImmersionModulePullback_preservesHomology
    (closedSubsetRestriction f Z)
  letI := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  letI := preservesFiniteColimits_modulePullback f
  letI := Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects f
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z)) _
      (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ') n ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ') n

/-! ### The same for the subsheaf of supported sections, read on `X` -/

/-- **Excision for the right derived functors of the subsheaf of supported sections**, the form
in which both sides are sheaves of modules on `X'`:

`(Rⁿ H_Z ℱ)|_{X'} ≅ Rⁿ H_{Z'}(f^*ℱ)`,

naturally in the `𝒪_X`-module `ℱ`, where `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X)` is the subsheaf
`Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor` of sections supported on `Z`
and the pullback is along `f` itself on both sides.

This is the ringed-space counterpart of
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`, built by the same
recipe — `rightDerivedCompIso` then `compRightDerivedNatIso` — from the ringed-space subsheaf
comparison `Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso`, which is
also the only mathematical input of `supportedSectionsOnClosedPullbackNatIso` and hence of the
derived excision.  The two degree-zero comparisons are *not* identified in the library; see the
implementation notes.  Having the abelian side in this spelling is what lets the two excisions
be compared without crossing between `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (structureSheafRing _)`.  No closedness of `Z` is needed. -/
def supportedSectionsRightDerivedPullbackNatIso (n : ℕ) :
    (supportedSectionsFunctor X Z).rightDerived n ⋙ modulePullback f ≅
      modulePullback f ⋙
        (supportedSectionsFunctor X' (closedSubsetPreimage f Z)).rightDerived n :=
  letI := Stacks.Cohomology.openImmersionModulePullback_preservesHomology f
  letI := preservesFiniteLimits_modulePullback_of_isOpenImmersion f
  letI := preservesFiniteColimits_modulePullback f
  letI := Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects f
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (supportedSectionsFunctor X Z)
      (modulePullback f) _ (supportedSectionsPullbackNatIso f Z) n ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (modulePullback f)
      (supportedSectionsFunctor X' (closedSubsetPreimage f Z)) n

end Stacks.Cohomology.SupportedComplexes

end
