module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedClassicalExcisionSquare
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportPushExcision
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedPullbackComparison
public import StacksFrontier.Homology.DerivedIndexing.ExcisionPostcomposeFold
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExcisionDerivedClassicalBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcision

/-!
# Excision for `i_* R𝓗_Z` is the fold-in of its degree-zero datum

Let `f : X' ⟶ X` be an open immersion of ringed spaces, `Z ⊆ X` closed and `Z' = f^{-1}(Z)`.
The repository has excision for the **pushed-forward** local cohomology of [Stacks, Tag 0G78]
as `Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso`, built from the
canonical map of that tag: the comparison of the exact direct image, the base change of
[Stacks, Tag 08HY] for the square of the restriction, the comparison back on `X'`, and the
canonical map under `i'_*`.

This file identifies it with the comparison that the **uniqueness of right derived functors**
produces for the endofunctors `H_Z ⋙ i_*` of `Mod(𝒪_X)` and `H_{Z'} ⋙ i'_*` of `Mod(𝒪_{X'})`
out of their degree-zero excision.  That degree-zero excision is `foldZeroIso`, the degreewise
excision `Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedPullbackNatIso` with the
base change `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso` of the
two direct images folded in; `foldZeroIso_hom_app` reads it as excision for the *subsheaf* of
supported sections, through the identification `i_* H_Z ≅ S_Z` of [Stacks, Tag 0G6N] on each
space.  The main result is `derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision`.

## Main definitions

* `Stacks.Perfect.SupportPushExcision.foldZeroIso`: **the degree-zero excision for the
  composites**, `(H_Z ⋙ i_*) ⋙ f^* ≅ f^* ⋙ (H_{Z'} ⋙ i'_*)`.  Four associators and two
  whiskerings, mirroring `Stacks.DerivedFunctor.foldZero`.
* `Stacks.Perfect.SupportPushExcision.innerDerivedComparison`: the comparison
  `R𝓗_Z ⋙ D((f|_{Z'})^*) ⟶ D(f^*) ⋙ R𝓗_{Z'}` that the uniqueness of right derived functors
  produces from the degreewise excision for the **inner** functors.

## Main results

* `foldZeroIso_hom` and `foldZeroIso_hom_app`: `foldZeroIso` is `Stacks.DerivedFunctor.foldZero`
  on the nose, and its components are excision for the subsheaf of supported sections conjugated
  by the identification of [Stacks, Tag 0G6N].
* the five `isRightDerivedFunctor_*` statements: the presuppositions, that each of the four
  composites in play is a right derived functor of the corresponding composite of degree-zero
  functors, at the canonical units `Stacks.DerivedFunctor.postcomposeUnit` and
  `Stacks.DerivedFunctor.precomposeUnit`.
* `innerDerivedComparison_fac`, `rightDerivedNatIso_hom_eq_innerDerivedComparison` and
  `supportedPullbackNatTrans_app_eq_innerDerivedComparison`: the factorization that pins
  `innerDerivedComparison` down, its identification with the comparison that
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso` is built
  from, and the resulting three-factor description of the canonical map of [Stacks, Tag 0G78].
* `derivedSupportedPushforwardPullbackIso_hom_app_eq_foldDerived` and
  `derivedExcisionNatIso_hom_eq_foldDerived`: excision is the derived fold-in, read between the
  two copies of `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` it
  carries; and the derived fold-in is the derived excision of the composites.
* `derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision`: **the two are equal.**

## Implementation notes

**The one place the mathematics is not formal** is
`supportedPullbackNatTrans_app_eq_innerDerivedComparison`, and even there the work is already
done: the canonical map of [Stacks, Tag 0G78] is the comparison of right derived functors by
`Stacks.Cohomology.SupportedComplexes`
`.supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso`, and that
comparison is, by definition, `innerDerivedComparison` between the two copies of the derived
pullback's identification — the transport of the units being
`Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso`, with
`Stacks.DerivedFunctor.postcomposeUnit_whiskerRight` and
`Stacks.DerivedFunctor.precomposeUnit_whisker` discharging its two hypotheses.  Everything else
is `Stacks.DerivedFunctor.eq_foldDerived`, the degreewise base change
`Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory`, and
three associativity chases.

**Every chase is a `private` helper at a variable category** with the objects implicit and the
morphisms explicit, applied with `exact`: on `DerivedCategory` the two spellings
`(w ⋙ P).mapHomotopyCategory c` and `w.mapHomotopyCategory c ⋙ P.mapHomotopyCategory c` of one
object are definitionally but not syntactically equal, so a `rw` whose motive crosses them is
not type-correct, `CategoryTheory.Functor.map_comp` included.  This is the discipline of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcisionDerived`.

**Exactness of the two direct images is carried, not assumed.**  Right-exactness of `i_*` needs
`Z` closed, so `Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits` cannot
be a local instance — `IsClosed Z` is not a class.  It therefore appears either as a `letI` in a
statement (as in `Stacks.Perfect.SupportPushExcision`
`.derivedSupportedPushforwardPullbackIso_hom_app`) or, where the statement is consumed inside
another proof, as an instance-implicit hypothesis.  Left-exactness needs nothing, and
`pushforward_preservesFiniteLimits` is a local instance here.

**`hZ' : IsClosed (closedSubsetPreimage f Z)` is a hypothesis** although
`Stacks.Cohomology.SupportedComplexes.isClosed_closedSubsetPreimage` supplies it, because every
degreewise input of the fold-in is stated with it; the two proofs are interchangeable by proof
irrelevance, which is what makes the main statement typecheck against
`derivedSupportedPushforwardPullbackIso`, whose type carries the derived one.

**No `@[stacks ...]` attribute is attached**: every statement here is an identification of two
constructions, not the statement of a tag, exactly as recorded for
`derivedSupportedPushforwardPullbackIso` itself.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.4 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion (derivedPullbackOpenImmersionIso)
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)

universe u

namespace Stacks.Perfect.SupportPushExcision

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.openImmersionModulePullback_preservesHomology
attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback
attribute [local instance]
  Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects
attribute [local instance] pushforward_preservesFiniteLimits
attribute [local instance] isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp
attribute [local instance]
  isRightDerivedFunctor_modulePullback_comp_derivedSupportedSectionsOnClosed

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier) (hZ : IsClosed Z) (hZ' : IsClosed (closedSubsetPreimage f Z))

/-! ### The degree-zero excision for the composites -/

/-- **The degree-zero excision for the endofunctors `H_Z ⋙ i_*` and `H_{Z'} ⋙ i'_*`**,

`(H_Z ⋙ i_*) ⋙ f^* ≅ f^* ⋙ (H_{Z'} ⋙ i'_*)`,

obtained from the degreewise excision
`Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedPullbackNatIso` for the sections
supported on the closed subset by folding in the base change
`Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso` of the two direct
images.

Four associators and two whiskerings, and no further mathematics: the composite is written to
mirror `Stacks.DerivedFunctor.foldZero` factor by factor, which is what makes
`foldZeroIso_hom` hold by `rfl`. -/
def foldZeroIso :
    (supportedSectionsOnClosedFunctor X Z hZ ⋙
          modulePushforward (closedSubsetInclusion X Z)) ⋙ modulePullback f ≅
      modulePullback f ⋙ (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' ⋙
        modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))) :=
  Functor.associator (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePushforward (closedSubsetInclusion X Z)) (modulePullback f) ≪≫
    Functor.isoWhiskerLeft (supportedSectionsOnClosedFunctor X Z hZ)
      (closedSubsetPushforwardPullbackNatIso f Z) ≪≫
    (Functor.associator (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z))
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))).symm ≪≫
    Functor.isoWhiskerRight (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))) ≪≫
    Functor.associator (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))

/-- **`foldZeroIso` is `Stacks.DerivedFunctor.foldZero` of the degreewise excision and the base
change 2-square**, on the nose: the two are the same five-factor composite.  This is what makes
the abstract fold-in results of
`StacksFrontier.Homology.DerivedIndexing.ExcisionPostcomposeFold` applicable here.

Right-exactness of the two direct images is an instance-implicit hypothesis rather than a `letI`
because this equation is only ever consumed inside a proof that already has it; it is
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits` at `hZ` and at
`hZ'`. -/
theorem foldZeroIso_hom
    [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
    [PreservesFiniteColimits
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] :
    (foldZeroIso f Z hZ hZ').hom =
      Stacks.DerivedFunctor.foldZero (supportedSectionsOnClosedFunctor X Z hZ)
        (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
        (modulePushforward (closedSubsetInclusion X Z))
        (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
        (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom
        (CategoryTheory.TwoSquare.mk _ _ _ _
          (closedSubsetPushforwardPullbackNatIso f Z).hom) := rfl

/-- **The degree-zero excision for the composites, at a module, is excision for the subsheaf of
supported sections.**  At an `𝒪_X`-module `ℱ` the component of `foldZeroIso` is

`f^*(i_* H_Z ℱ) ≅ f^*(S_Z ℱ) ≅ S_{Z'}(f^* ℱ) ≅ i'_*(H_{Z'}(f^* ℱ))`,

the outer two steps being the identification `i_* H_Z ≅ S_Z` of [Stacks, Tag 0G6N],
`Stacks.SheafOfModules.SupportedSections`
`.supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`, on `X` and on `X'`, and the
middle step
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso`.

This is `Stacks.DerivedFunctor.foldZero_app` composed with
`Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso_comp_map_eq`. -/
theorem foldZeroIso_hom_app (ℱ : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (foldZeroIso f Z hZ hZ').hom.app ℱ =
      (modulePullback f).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ) ≫
        (supportedSectionsPullbackNatIso f Z).hom.app ℱ ≫
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
            (closedSubsetPreimage f Z) hZ').inv.app ((modulePullback f).obj ℱ) := by
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  refine (congrFun (congrArg NatTrans.app (foldZeroIso_hom f Z hZ hZ')) ℱ).trans ?_
  exact (Stacks.DerivedFunctor.foldZero_app (supportedSectionsOnClosedFunctor X Z hZ)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (modulePushforward (closedSubsetInclusion X Z))
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
      (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
      (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom
      (CategoryTheory.TwoSquare.mk _ _ _ _
        (closedSubsetPushforwardPullbackNatIso f Z).hom) ℱ).trans
    (closedSubsetPushforwardPullbackNatIso_comp_map_eq f Z hZ hZ' ℱ)

/-! ### The presuppositions -/

/-- The pullback along an open immersion carries K-injective complexes to K-injective ones. -/
private theorem isKInjective_map_modulePullback
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := hI
  Stacks.Cohomology.openImmersionModulePullback_preservesKInjective f I

/-- **`i_* R𝓗_T` is a right derived functor of `H_T ⋙ i_*` at the canonical unit.**  The direct
image from a closed subset is exact, so this is absoluteness of a right derived functor computed
by K-injective resolutions, `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, whose
only input is `Stacks.Cohomology.Localization.enoughKInjectives`.

`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward_isRightDerivedFunctor` is the
same functor exhibited at the unit `Stacks.Perfect.SupportedQuasicoherent`
`.derivedSupportedPushforwardUnit`, whose source is `S_T(-)` rather than `(H_T ⋙ i_*)(-)`; the
statement here is the one the fold-in results are written at. -/
theorem isRightDerivedFunctor_postcompose_closedPushforward (Y : RingedSpace.{u, u})
    (T : Set Y.carrier) (hT : IsClosed T)
    [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion Y T))] :
    (derivedSupportedSectionsOnClosed Y T hT ⋙
        (modulePushforward (closedSubsetInclusion Y T)).mapDerivedCategory).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor Y T hT)
        (modulePushforward (closedSubsetInclusion Y T))
        (derivedSupportedSectionsOnClosed Y T hT) (derivedSupportedSectionsOnClosedUnit Y T hT))
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose _ _ _ _
    Stacks.Cohomology.Localization.enoughKInjectives

attribute [local instance] isRightDerivedFunctor_postcompose_closedPushforward

/-- **`R𝓗_Z ⋙ D((f|_{Z'})^*)` is a right derived functor of `H_Z ⋙ (f|_{Z'})^*` at the canonical
unit.**  The restriction of an open immersion to the closed subsets is an open immersion
(`Stacks.Cohomology.SupportedComplexes.isOpenImmersion_closedSubsetRestriction`), so its
pullback is exact and `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose` applies.

`Stacks.Cohomology.SupportedComplexes.isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp`
is the same functor at the whiskered unit; the two units agree by
`Stacks.DerivedFunctor.postcomposeUnit_whiskerRight`. -/
theorem isRightDerivedFunctor_postcompose_restrictPullback :
    (derivedSupportedSectionsOnClosed X Z hZ ⋙
        (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
        (modulePullback (closedSubsetRestriction f Z))
        (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ))
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose _ _ _ _
    Stacks.Cohomology.Localization.enoughKInjectives

attribute [local instance] isRightDerivedFunctor_postcompose_restrictPullback

/-- **`D(f^*) ⋙ R𝓗_{Z'}` is a right derived functor of `f^* ⋙ H_{Z'}` at the canonical unit.**
Unlike the post-composition statements this is not formal: it needs that `f^*` carries
K-injective complexes to K-injective ones, which holds for an open immersion by
`Stacks.Cohomology.openImmersionModulePullback_preservesKInjective`.  That is
`Stacks.DerivedFunctor.isRightDerivedFunctor_precompose`. -/
theorem isRightDerivedFunctor_precompose_openImmersionPullback :
    ((modulePullback f).mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z)
          hZ').IsRightDerivedFunctor
      (Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
        (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
        (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_precompose _ _ _ _
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
    (isKInjective_map_modulePullback f)

attribute [local instance] isRightDerivedFunctor_precompose_openImmersionPullback

/-- **`(i_* R𝓗_Z) ⋙ D(f^*)` is a right derived functor of `(H_Z ⋙ i_*) ⋙ f^*`.**  The
post-composition statement one level up: the source is already a right derived functor by
`isRightDerivedFunctor_postcompose_closedPushforward`, and `f^*` is exact.  This is the
left-hand presupposition of the derived excision of the composites. -/
theorem isRightDerivedFunctor_derivedSupportedPushforward_comp_pullback
    [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))] :
    ((derivedSupportedSectionsOnClosed X Z hZ ⋙
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory) ⋙
        (modulePullback f).mapDerivedCategory).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.postcomposeUnit
        (supportedSectionsOnClosedFunctor X Z hZ ⋙
          modulePushforward (closedSubsetInclusion X Z))
        (modulePullback f)
        (derivedSupportedSectionsOnClosed X Z hZ ⋙
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
          (modulePushforward (closedSubsetInclusion X Z))
          (derivedSupportedSectionsOnClosed X Z hZ)
          (derivedSupportedSectionsOnClosedUnit X Z hZ)))
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose _ _ _ _
    Stacks.Cohomology.Localization.enoughKInjectives

attribute [local instance] isRightDerivedFunctor_derivedSupportedPushforward_comp_pullback

/-- **`D(f^*) ⋙ (i'_* R𝓗_{Z'})` is a right derived functor of `f^* ⋙ (H_{Z'} ⋙ i'_*)`.**  The
pre-composition statement one level up, again by
`Stacks.Cohomology.openImmersionModulePullback_preservesKInjective`.  This is the right-hand
presupposition of the derived excision of the composites. -/
theorem isRightDerivedFunctor_pullback_comp_derivedSupportedPushforward
    [PreservesFiniteColimits
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] :
    ((modulePullback f).mapDerivedCategory ⋙
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' ⋙
          (modulePushforward (closedSubsetInclusion X'
            (closedSubsetPreimage f Z))).mapDerivedCategory)).IsRightDerivedFunctor
      (Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
        (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' ⋙
          modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' ⋙
          (modulePushforward (closedSubsetInclusion X'
            (closedSubsetPreimage f Z))).mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
          (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ')))
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.isRightDerivedFunctor_precompose _ _ _ _
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
    (isKInjective_map_modulePullback f)

attribute [local instance] isRightDerivedFunctor_pullback_comp_derivedSupportedPushforward

/-! ### The comparison for the inner functors -/

/-- **The comparison `R𝓗_Z ⋙ D((f|_{Z'})^*) ⟶ D(f^*) ⋙ R𝓗_{Z'}`** that the uniqueness of right
derived functors produces from the degreewise excision
`Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedPullbackNatIso`, at the canonical
units `Stacks.DerivedFunctor.postcomposeUnit` and `Stacks.DerivedFunctor.precomposeUnit`.

This is the inner datum the derived fold-in consumes.  It is the inner factor of
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso` —
that isomorphism is this comparison read between the two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` it carries, which is
`supportedPullbackNatTrans_app_eq_innerDerivedComparison`. -/
def innerDerivedComparison :
    derivedSupportedSectionsOnClosed X Z hZ ⋙
        (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory ⟶
      (modulePullback f).mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' :=
  Stacks.DerivedFunctor.derivedNatTrans
    (supportedSectionsOnClosedFunctor X Z hZ ⋙ modulePullback (closedSubsetRestriction f Z))
    (modulePullback f ⋙ supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
    (derivedSupportedSectionsOnClosed X Z hZ ⋙
      (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory)
    ((modulePullback f).mapDerivedCategory ⋙
      derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z)) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ))
    (Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))
    (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom

/-- **The factorization that pins `innerDerivedComparison` down**: the unit exhibiting
`R𝓗_Z ⋙ D((f|_{Z'})^*)` as a right derived functor, followed by the comparison, is the
degreewise excision followed by the unit exhibiting `D(f^*) ⋙ R𝓗_{Z'}` as one.  This is
`CategoryTheory.Functor.rightDerivedNatTrans_fac`, and it is the hypothesis `hΨ` of
`Stacks.DerivedFunctor.eq_foldDerived`. -/
theorem innerDerivedComparison_fac :
    Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
          (modulePullback (closedSubsetRestriction f Z))
          (derivedSupportedSectionsOnClosed X Z hZ)
          (derivedSupportedSectionsOnClosedUnit X Z hZ) ≫
        Functor.whiskerLeft DerivedCategory.Qh (innerDerivedComparison f Z hZ hZ') =
      Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans
          (supportedSectionsOnClosedFunctor X Z hZ ⋙
            modulePullback (closedSubsetRestriction f Z))
          (modulePullback f ⋙
            supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom ≫
        Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
          (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') :=
  Functor.rightDerivedNatTrans_fac
    (derivedSupportedSectionsOnClosed X Z hZ ⋙
      (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory)
    ((modulePullback f).mapDerivedCategory ⋙
      derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z)) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ))
    (Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    (Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans
      (supportedSectionsOnClosedFunctor X Z hZ ⋙ modulePullback (closedSubsetRestriction f Z))
      (modulePullback f ⋙ supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom)

/-- **The comparison the definition of
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso` carries is
`innerDerivedComparison`.**  That definition feeds the universal property the whiskered units
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedCompUnit` and its
two-factor counterpart on `X'`, and the source comparison
`Stacks.DerivedFunctor.excisionSourceIso`, rather than the canonical units and
`Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans`; the transport between the two
presentations is `Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso`, whose hypotheses are
`Stacks.DerivedFunctor.postcomposeUnit_whiskerRight`,
`Stacks.DerivedFunctor.precomposeUnit_whisker` and
`Stacks.DerivedFunctor.excisionSourceIso_hom_eq`. -/
theorem rightDerivedNatIso_hom_eq_innerDerivedComparison :
    (Functor.rightDerivedNatIso
        (derivedSupportedSectionsOnClosed X Z hZ ⋙
          (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory)
        ((modulePullback f).mapDerivedCategory ⋙
          derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
        (derivedSupportedSectionsOnClosedCompUnit f Z hZ)
        (Functor.whiskerLeft ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
            (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') ≫
          Functor.whiskerRight (modulePullback f).mapDerivedCategoryFactorsh.inv
            (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ'))
        (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ))
        (Stacks.DerivedFunctor.excisionSourceIso (supportedSectionsOnClosedFunctor X Z hZ)
          (modulePullback (closedSubsetRestriction f Z)) (modulePullback f)
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ'))).hom =
      innerDerivedComparison f Z hZ hZ' :=
  Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    (derivedSupportedSectionsOnClosed X Z hZ ⋙
      (modulePullback (closedSubsetRestriction f Z)).mapDerivedCategory)
    ((modulePullback f).mapDerivedCategory ⋙
      derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z)) (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ))
    (Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))
    (derivedSupportedSectionsOnClosedCompUnit f Z hZ)
    (Functor.whiskerLeft ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
        (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') ≫
      Functor.whiskerRight (modulePullback f).mapDerivedCategoryFactorsh.inv
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ'))
    (Stacks.DerivedFunctor.postcomposeSourceIso (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z))).symm
    (Stacks.DerivedFunctor.precomposeSourceIso (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')).symm
    (Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans
      (supportedSectionsOnClosedFunctor X Z hZ ⋙ modulePullback (closedSubsetRestriction f Z))
      (modulePullback f ⋙ supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom)
    (Stacks.DerivedFunctor.excisionSourceIso (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z)) (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')).hom
    inferInstance inferInstance
    (Stacks.DerivedFunctor.postcomposeUnit_whiskerRight
      (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z))
      (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ))
    (Stacks.DerivedFunctor.precomposeUnit_whisker (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))
    (Stacks.DerivedFunctor.excisionSourceIso_hom_eq (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z)) (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ'))

/-- **The canonical map of [Stacks, Tag 0G78], in three factors.**  At every `K` in `D(𝒪_X)` the
canonical map `L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)` is the identification of the derived
pullback along `f|_{Z'}` with the degreewise one, then `innerDerivedComparison`, then `R𝓗_{Z'}`
applied to that identification for `f` inverted.

`Stacks.Cohomology.SupportedComplexes`
`.supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso` identifies the
canonical map with the comparison of right derived functors, and that comparison is this
three-factor composite by definition; the middle factor is `innerDerivedComparison` by
`rightDerivedNatIso_hom_eq_innerDerivedComparison`. -/
theorem supportedPullbackNatTrans_app_eq_innerDerivedComparison
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    (supportedPullbackNatTrans f Z hZ).app K =
      (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.app
          ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
        (innerDerivedComparison f Z hZ hZ').app K ≫
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
            ((derivedPullbackOpenImmersionIso f).inv.app K) := by
  refine (congrFun (congrArg NatTrans.app
    (supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ))
      K).trans ?_
  exact congrArg (fun σ => (derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.app
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫ NatTrans.app σ K ≫
    (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
      ((derivedPullbackOpenImmersionIso f).inv.app K))
    (rightDerivedNatIso_hom_eq_innerDerivedComparison f Z hZ hZ')

/-! ### The chases -/

/-- Cancelling the inverse of an isomorphism against the leading factor of a composite.  Stated
at an arbitrary category with the objects implicit and the morphisms explicit, so that it
applies by `exact` across the definitionally equal spellings of a composite's derived
functor. -/
private theorem cancel_inv {D : Type*} [Category* D] {a b c : D}
    (qi : a ⟶ b) (qh : b ⟶ a) (n : b ⟶ c) (r : a ⟶ c)
    (hn : n = qh ≫ r) (hq : qi ≫ qh = CategoryStruct.id a) : qi ≫ n = r := by
  rw [hn, ← Category.assoc, hq, Category.id_comp]

/-- Two composable morphisms carried by a functor, against a second factorization of the same
composite.  Stated at arbitrary categories with the objects implicit and the morphisms
explicit. -/
private theorem map_two {E D : Type*} [Category* E] [Category* D] (Φ : E ⥤ D)
    {a b c d : E} (u : a ⟶ b) (v : b ⟶ c) (x : a ⟶ d) (y : d ⟶ c)
    (hh : u ≫ v = x ≫ y) : Φ.map u ≫ Φ.map v = Φ.map x ≫ Φ.map y := by
  rw [← Φ.map_comp, ← Φ.map_comp, hh]

/-- The chase behind `derivedSupportedPushforwardPullbackIso_hom_app_eq_foldDerived`: the first
three of the four factors of excision are the base change read through the derived pullback's
identification (`h123`), the last two factors merge into the derived fold-in's second factor
(`h`), and the fold-in's two factors are `hm`.  Stated at an arbitrary category with the objects
implicit and the morphisms explicit. -/
private theorem fold_push_chase {D : Type*} [Category* D] {x x₁ x₂ x₃ y z v r : D}
    (a₁ : x ⟶ x₁) (a₂ : x₁ ⟶ x₂) (a₃ : x₂ ⟶ x₃) (a₄ : x₃ ⟶ r)
    (p : x ⟶ y) (t : y ⟶ z) (q : z ⟶ x₃) (c : z ⟶ v) (d : v ⟶ r) (m : y ⟶ v)
    (h123 : a₁ ≫ a₂ ≫ a₃ = p ≫ t ≫ q) (h : q ≫ a₄ = c ≫ d) (hm : m = t ≫ c) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ = p ≫ m ≫ d := by
  rw [hm, reassoc_of% h123, h, Category.assoc]

/-! ### Excision is the derived fold-in -/

/-- **Excision for `i_* R𝓗_Z` is the derived fold-in**, read between the two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` it carries.

`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso_hom_app` presents
excision in four factors; the first three are the derived image of the underived base change by
`Stacks.Cohomology.SupportedComplexes.supportedPullbackBaseChangeMap_eq_mapDerivedCategory`,
which is the first factor of `Stacks.DerivedFunctor.foldDerived_app`, and the fourth merges with
the trailing identification of the third into the second factor of the fold-in by
`supportedPullbackNatTrans_app_eq_innerDerivedComparison`. -/
theorem derivedSupportedPushforwardPullbackIso_hom_app_eq_foldDerived
    [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
    [PreservesFiniteColimits
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K =
      (derivedPullbackOpenImmersionIso f).hom.app ((derivedSupportedPushforward X Z hZ).obj K) ≫
        (Stacks.DerivedFunctor.foldDerived (modulePushforward (closedSubsetInclusion X Z))
            (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
            (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
            (CategoryTheory.TwoSquare.mk _ _ _ _
              (closedSubsetPushforwardPullbackNatIso f Z).hom)
            (derivedSupportedSectionsOnClosed X Z hZ)
            (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
            (innerDerivedComparison f Z hZ hZ')).app K ≫
          (derivedSupportedPushforward X' (closedSubsetPreimage f Z) hZ').map
            ((derivedPullbackOpenImmersionIso f).inv.app K) := by
  have h1 : (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K =
      (derivedPullback f).map ((closedPushforwardComparison X Z).hom.app
          ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
        supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
        (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
            ((derivedPullback (closedSubsetRestriction f Z)).obj
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
          (modulePushforward
                (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
            ((supportedPullbackNatTrans f Z hZ).app K) :=
    derivedSupportedPushforwardPullbackIso_hom_app f Z hZ K
  have h123 : (derivedPullback f).map ((closedPushforwardComparison X Z).hom.app
            ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
          supportedPullbackBaseChangeMap f Z ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
          (closedPushforwardComparison X' (closedSubsetPreimage f Z)).inv.app
            ((derivedPullback (closedSubsetRestriction f Z)).obj
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) =
        (derivedPullbackOpenImmersionIso f).hom.app
              ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
                ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
            (CategoryTheory.TwoSquare.mapDerivedCategory (CategoryTheory.TwoSquare.mk _ _ _ _
              (closedSubsetPushforwardPullbackNatIso f Z).hom)).app
                ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
            (modulePushforward
                (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
              ((derivedPullbackOpenImmersionIso
                (closedSubsetRestriction f Z)).inv.app
                  ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) :=
    supportedPullbackBaseChangeMap_eq_mapDerivedCategory f Z hZ hZ'
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K)
  have hcan : (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
          ((derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).inv.app
            ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
        (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
          ((supportedPullbackNatTrans f Z hZ).app K) =
      (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
          ((innerDerivedComparison f Z hZ hZ').app K) ≫
        (derivedSupportedPushforward X' (closedSubsetPreimage f Z) hZ').map
          ((derivedPullbackOpenImmersionIso f).inv.app K) :=
    map_two (modulePushforward
        (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory _ _ _ _
      (cancel_inv _ _ _ _ (supportedPullbackNatTrans_app_eq_innerDerivedComparison f Z hZ hZ' K)
        ((derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).inv_hom_id_app
          ((derivedSupportedSectionsOnClosed X Z hZ).obj K)))
  refine h1.trans (fold_push_chase _ _ _ _ _ _ _ _ _ _ h123 hcan ?_)
  exact Stacks.DerivedFunctor.foldDerived_app
    (modulePushforward (closedSubsetInclusion X Z))
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
    (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
    (CategoryTheory.TwoSquare.mk _ _ _ _ (closedSubsetPushforwardPullbackNatIso f Z).hom)
    (derivedSupportedSectionsOnClosed X Z hZ)
    (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (innerDerivedComparison f Z hZ hZ') K

/-- **The derived excision of the composites is the derived fold-in.**  Both are comparisons
`(i_* R𝓗_Z) ⋙ D(f^*) ⟶ D(f^*) ⋙ (i'_* R𝓗_{Z'})` of right derived functors of
`(H_Z ⋙ i_*) ⋙ f^*` and of `f^* ⋙ (H_{Z'} ⋙ i'_*)`, and they factor the unit the same way:
`Stacks.DerivedIndexing.derivedExcisionNatIso_fac` is the factorization of the first through
`foldZeroIso`, which `Stacks.DerivedIndexing.excisionHomotopyIso_hom` and `foldZeroIso_hom`
rewrite into the shape `Stacks.DerivedFunctor.eq_foldDerived` asks for; the second factors the
unit through `innerDerivedComparison_fac`.  So the uniqueness of right derived functors
identifies them. -/
theorem derivedExcisionNatIso_hom_eq_foldDerived
    [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
    [PreservesFiniteColimits
      (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))] :
    (Stacks.DerivedIndexing.derivedExcisionNatIso
        (supportedSectionsOnClosedFunctor X Z hZ ⋙
          modulePushforward (closedSubsetInclusion X Z))
        (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' ⋙
          modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (modulePullback f) (foldZeroIso f Z hZ hZ')
        (derivedSupportedSectionsOnClosed X Z hZ ⋙
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
          (modulePushforward (closedSubsetInclusion X Z))
          (derivedSupportedSectionsOnClosed X Z hZ)
          (derivedSupportedSectionsOnClosedUnit X Z hZ))
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' ⋙
          (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
          (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))).hom =
      Stacks.DerivedFunctor.foldDerived (modulePushforward (closedSubsetInclusion X Z))
        (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
        (CategoryTheory.TwoSquare.mk _ _ _ _ (closedSubsetPushforwardPullbackNatIso f Z).hom)
        (derivedSupportedSectionsOnClosed X Z hZ)
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
        (innerDerivedComparison f Z hZ hZ') := by
  have hcomb : (Stacks.DerivedIndexing.excisionHomotopyIso
          (supportedSectionsOnClosedFunctor X Z hZ ⋙
            modulePushforward (closedSubsetInclusion X Z))
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' ⋙
            modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
          (modulePullback f) (foldZeroIso f Z hZ hZ')).hom =
      Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans
        ((supportedSectionsOnClosedFunctor X Z hZ ⋙
          modulePushforward (closedSubsetInclusion X Z)) ⋙ modulePullback f)
        (modulePullback f ⋙ (supportedSectionsOnClosedFunctor X'
          (closedSubsetPreimage f Z) hZ' ⋙
            modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))))
        (Stacks.DerivedFunctor.foldZero (supportedSectionsOnClosedFunctor X Z hZ)
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (modulePushforward (closedSubsetInclusion X Z))
          (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
          (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
          (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom
          (CategoryTheory.TwoSquare.mk _ _ _ _
            (closedSubsetPushforwardPullbackNatIso f Z).hom)) :=
    (Stacks.DerivedIndexing.excisionHomotopyIso_hom _ _ _ (foldZeroIso f Z hZ hZ')).trans
      (congrArg (fun σ => Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans _ _ σ)
        (foldZeroIso_hom f Z hZ hZ'))
  exact Stacks.DerivedFunctor.eq_foldDerived (supportedSectionsOnClosedFunctor X Z hZ)
    (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
    (modulePushforward (closedSubsetInclusion X Z))
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
    (modulePullback f) (modulePullback (closedSubsetRestriction f Z))
    (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom
    (CategoryTheory.TwoSquare.mk _ _ _ _ (closedSubsetPushforwardPullbackNatIso f Z).hom)
    (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ)
    (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ')
    (innerDerivedComparison f Z hZ hZ')
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives _
    ((Stacks.DerivedIndexing.derivedExcisionNatIso_fac _ _ _
        (foldZeroIso f Z hZ hZ') _ _ _ _).trans
      (congrArg (fun σ => σ ≫ Stacks.DerivedFunctor.precomposeUnit (modulePullback f)
        (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' ⋙
          modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' ⋙
          (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory)
        (Stacks.DerivedFunctor.postcomposeUnit
          (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
          (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
          (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
          (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))) hcomb))
    (innerDerivedComparison_fac f Z hZ hZ')

/-- **Excision for `i_* R𝓗_Z` along an open immersion is the derived excision that the
uniqueness of right derived functors produces from its degree-zero datum.**  For an open
immersion of ringed spaces `f : X' ⟶ X`, a closed `Z ⊆ X`, `Z' = f^{-1}(Z)` and every `K` in
`D(𝒪_X)`,

`Θ_K = (Lf^* ≅ D(f^*)) ≫ (the derived excision of (H_Z ⋙ i_*) and (H_{Z'} ⋙ i'_*)) ≫
  (i'_* R𝓗_{Z'})(D(f^*) ≅ Lf^*)`,

with `Θ` the isomorphism of
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso`, built from the
canonical map of [Stacks, Tag 0G78], and the middle factor
`Stacks.DerivedIndexing.derivedExcisionNatIso` at the degree-zero excision `foldZeroIso` of the
two endofunctors.  The two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` are there because the
derived excision is built from the *degreewise* pullback, whereas excision is stated for the
derived pullback of [Stacks, Tag 0A3B]'s adjunction.

This is `derivedSupportedPushforwardPullbackIso_hom_app_eq_foldDerived` followed by
`derivedExcisionNatIso_hom_eq_foldDerived`.  It is the companion, at the pushed-forward
spelling, of `Stacks.Cohomology.SupportedComplexes`
`.derivedSupportedSectionsOnClosedPullbackNatIso_eq_classical`. -/
theorem derivedSupportedPushforwardPullbackIso_hom_app_eq_derivedExcision
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
    (derivedSupportedPushforwardPullbackIso f Z hZ).hom.app K =
      (derivedPullbackOpenImmersionIso f).hom.app ((derivedSupportedPushforward X Z hZ).obj K) ≫
        (Stacks.DerivedIndexing.derivedExcisionNatIso
            (supportedSectionsOnClosedFunctor X Z hZ ⋙
              modulePushforward (closedSubsetInclusion X Z))
            (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' ⋙
              modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
            (modulePullback f) (foldZeroIso f Z hZ hZ')
            (derivedSupportedSectionsOnClosed X Z hZ ⋙
              (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory)
            (Stacks.DerivedFunctor.postcomposeUnit (supportedSectionsOnClosedFunctor X Z hZ)
              (modulePushforward (closedSubsetInclusion X Z))
              (derivedSupportedSectionsOnClosed X Z hZ)
              (derivedSupportedSectionsOnClosedUnit X Z hZ))
            (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ' ⋙
              (modulePushforward
                (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory)
            (Stacks.DerivedFunctor.postcomposeUnit
              (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
              (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
              (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
              (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z)
                hZ'))).hom.app K ≫
          (derivedSupportedPushforward X' (closedSubsetPreimage f Z) hZ').map
            ((derivedPullbackOpenImmersionIso f).inv.app K) := by
  let := pushforward_preservesFiniteColimits X Z hZ
  let := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z) hZ'
  rw [derivedSupportedPushforwardPullbackIso_hom_app_eq_foldDerived f Z hZ hZ' K,
    derivedExcisionNatIso_hom_eq_foldDerived f Z hZ hZ']

end Stacks.Perfect.SupportPushExcision

end
