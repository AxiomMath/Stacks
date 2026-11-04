module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportCounitComparison
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CounitGysinEdgeExact
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedCounitForget

/-!
# The counit compatibility of the Gysin edge morphism, at the geometric data

`Stacks.CounitGysinEdge.CounitCompatible` is the one hypothesis of
`Stacks.CounitGysinEdge.mapDerivedCategory_edge`, which says that an exact functor carries the
Gysin edge morphism of [Stacks, Tag 0G8A] to the Gysin edge morphism built from the data on the
other side.  This file instantiates it at the data the square of [Stacks, Tag 0G8B] needs: the
exact functor is the one forgetting the module structure, and the two sets of data are the
module-side and the abelian-side derived supported sections, direct images and counits.

## Main definitions

* `forgetClosed`: forgetting the module structure on the closed subspace, **with its codomain
  spelled as abelian sheaves on `TopCat.of Z`**; the implementation notes say why the spelling is
  named.
* `forgetLocalCohomologyIso`: [Stacks, Tag 0G74] part (2) at the canonical derived functors, as
  an isomorphism `R𝓗_Z(K)_ab ≅ R𝓗^{ab}_Z(K_ab)` of functors.

## Main results

* `counitCompatible`: **`Stacks.CounitGysinEdge.CounitCompatible` holds at the geometric data.**
* `toSheaf_preservesFiniteColimits`: forgetting the module structure on a ringed space preserves
  finite colimits, as a named declaration.

## Implementation notes

Nothing is proved here that the library did not have; the mathematical content is three
identifications composed.  Writing `Φ` for forgetting the module structure on derived categories:

* `Stacks.Perfect.SupportCounitComparison`
  `.derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit` reads the counit of
  [Stacks, Tag 0A3B] as the transition of [Stacks, Tag 0G72], which is the form the next step
  speaks about;
* `Stacks.Cohomology.AbelianSupportedCounitForget.whiskerRight_derivedSupportedSectionsToId`
  carries that transition across `Φ` to the abelian one, with the comparison
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` — that is
  [Stacks, Tag 0G74] part (2) with `i_*` folded in — in between;
* `Stacks.Perfect.SupportedEndoForgetIdentity.endoForgetComparison_eq` rewrites that folded
  comparison as `Stacks.Cohomology.ModulePushforwardComparison`
  `.derivedModulePushforwardCompToSheafIso` followed by the comparison on the closed subset, and
  that composite is literally the right-hand side of `CounitCompatible`:
  `Stacks.CounitGysinEdge.pushCompare` at the two forgetful functors and at
  `Stacks.Cohomology.ModulePushforwardComparison.modulePushforwardCompToSheafIso` **is**
  `derivedModulePushforwardCompToSheafIso`, both being the same `CategoryTheory.Iso.trans` chain,
  so no transport is needed.

**The spelling, which is what the instantiation was actually waiting on.**  Three instances have
to be arranged for the statement to elaborate at all, and none of them is about mathematics.

1. The category of abelian sheaves on the closed subspace has two spellings: the codomain of
   `SheafOfModules.toSheaf (structureSheafRing (closedSubsetRingedSpace X Z))`, which is sheaves
   on `(closedSubsetRingedSpace X Z).carrier`, and the one
   `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed` lands in, which
   is sheaves on `TopCat.of Z`.  They are definitionally equal, but `HasDerivedCategory` is found
   only at the second — the priority-10000 local attribute on `HasDerivedCategory.standard` does
   not rescue the first, because nothing there pins the universe.  So `forgetClosed` ascribes the
   codomain to the `TopCat.of Z` spelling, and the direct image is taken as
   `Stacks.Cohomology.SupportedComplexes.abelianClosedPushforward`, whose source is spelled that
   way too, rather than `abelianPushforward (closedSubsetInclusion X Z)`, whose `Additive`
   instance is then out of reach.
2. At the ascribed spelling, `Additive` and `PreservesFiniteLimits` of `forgetClosed` are no
   longer found by instance search either; they are supplied as local instances, each by
   `inferInstanceAs` at the unascribed spelling.
3. `PreservesFiniteColimits` of the forgetful functor is not found at the spelling
   `structureSheafRing Y` for any ringed space `Y`, closed subspace or not, although
   `Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf` proves it; it is named here as
   `toSheaf_preservesFiniteColimits` and used as a local instance.

**No declaration here carries a `@[stacks ...]` attribute.**  The edge morphism is a construction
of this library and this is a compatibility of its ingredients; the tagged statements those
ingredients realize are [Stacks, Tag 0G74] part (2), [Stacks, Tag 0G72] and [Stacks, Tag 0A3B],
and they carry their attributes where they are proved.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G8B](https://stacks.math.columbia.edu/tag/0G8B)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 20.34.4 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.AbelianSupportedCounitForget
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportCounitComparison
open Stacks.Perfect.SupportedEndoForgetIdentity
open Stacks.Perfect.SupportedQuasicoherent

universe u

namespace Stacks.DeRham.CounitCompatibleGeometric

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Forgetting the module structure on a ringed space preserves finite colimits**, so that it
is exact: this is `Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf` at the site of opens.
It is named because instance search does not find that instance at the spelling
`structureSheafRing Y`, and the exactness hypotheses of
`Stacks.CounitGysinEdge.mapDerivedCategory_edge` ask for it. -/
theorem toSheaf_preservesFiniteColimits (Y : RingedSpace.{u, u}) :
    PreservesFiniteColimits (_root_.SheafOfModules.toSheaf.{u} (structureSheafRing Y)) :=
  Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _

attribute [local instance] toSheaf_preservesFiniteColimits

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **Forgetting the module structure on the closed subspace**, with its codomain spelled as
abelian sheaves on `TopCat.of Z` — the spelling
`Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed` and
`Stacks.Cohomology.SupportedComplexes.abelianClosedPushforward` use.  The implementation notes say
why the ascription is necessary. -/
abbrev forgetClosed :
    _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)) ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf.{u} (structureSheafRing (closedSubsetRingedSpace X Z))

/-- Forgetting the module structure on the closed subspace is additive, at the ascribed
spelling. -/
local instance forgetClosed_additive : (forgetClosed X Z).Additive :=
  inferInstanceAs (_root_.SheafOfModules.toSheaf.{u}
    (structureSheafRing (closedSubsetRingedSpace X Z))).Additive

/-- Forgetting the module structure on the closed subspace preserves finite limits, at the
ascribed spelling. -/
local instance forgetClosed_preservesFiniteLimits :
    PreservesFiniteLimits (forgetClosed X Z) :=
  inferInstanceAs (PreservesFiniteLimits (_root_.SheafOfModules.toSheaf.{u}
    (structureSheafRing (closedSubsetRingedSpace X Z))))

/-- Forgetting the module structure on the closed subspace preserves finite colimits, at the
ascribed spelling. -/
local instance forgetClosed_preservesFiniteColimits :
    PreservesFiniteColimits (forgetClosed X Z) :=
  toSheaf_preservesFiniteColimits (closedSubsetRingedSpace X Z)

/-- **[Stacks, Tag 0G74] part (2), as an isomorphism of functors**, at the canonical derived
functors of supported sections on `Z` of modules and of abelian sheaves: forgetting the module
structure of `R𝓗_Z(K)` gives `R𝓗^{ab}_Z(K_ab)`.  The morphism is
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison` and its invertibility
is `Stacks.Cohomology.SupportedComplexes`
`.isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor`. -/
def forgetLocalCohomologyIso :
    derivedSupportedSectionsOnClosed X Z hZ ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing (closedSubsetRingedSpace X Z))).mapDerivedCategory ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategory ⋙
        derivedAbelianSupportedSectionsOnClosed X Z hZ :=
  letI : IsIso (localCohomologySheafForgetComparison X Z hZ
      (derivedAbelianSupportedSectionsOnClosed X Z hZ)
      (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
      (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedSupportedSectionsOnClosedUnit X Z hZ)) :=
    isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor X Z hZ _ _ _ _
  asIso (localCohomologySheafForgetComparison X Z hZ
    (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
    (derivedSupportedSectionsOnClosed X Z hZ)
    (derivedSupportedSectionsOnClosedUnit X Z hZ))

/-- The underlying morphism of `forgetLocalCohomologyIso` is the comparison of
[Stacks, Tag 0G74] part (2), by definition. -/
theorem forgetLocalCohomologyIso_hom :
    (forgetLocalCohomologyIso X Z hZ).hom =
      localCohomologySheafForgetComparison X Z hZ
        (derivedAbelianSupportedSectionsOnClosed X Z hZ)
        (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
        (derivedSupportedSectionsOnClosed X Z hZ)
        (derivedSupportedSectionsOnClosedUnit X Z hZ) :=
  rfl

/-- The formal rearrangement of `counitCompatible`, at a variable category: `hcF` identifies the
two readings of the counit, carried along the forgetful functor, `hw` is the abelian
compatibility of that counit and `he` rewrites the folded comparison as the two factors of the
right-hand side of `Stacks.CounitGysinEdge.CounitCompatible`.  Stated abstractly and applied with
`exact` because the objects along the composites are definitionally equal in the two spellings
"push forward then forget" and "forget then push forward", which `rw` refuses to identify. -/
private lemma assemble {V : Type*} [Category* V] {x y z w : V}
    (pc : x ⟶ y) (pt : y ⟶ z) (cmp : x ⟶ z) (ep : z ⟶ w) (a b : x ⟶ w)
    (hcF : a = b) (hw : a = cmp ≫ ep) (he : pc ≫ pt = cmp) :
    b = pc ≫ pt ≫ ep := by
  rw [← hcF, hw, ← he, Category.assoc]

/-- **`Stacks.CounitGysinEdge.CounitCompatible` at the geometric data.**  Forgetting the module
structure carries the counit `i_*R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0A3B] to the abelian counit
`i_*R𝓗^{ab}_Z(K_ab) ⟶ K_ab`, across the comparison
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` moving the
direct image past the forgetful functor and the comparison of [Stacks, Tag 0G74] part (2) on the
closed subset.

This is the one hypothesis of `Stacks.CounitGysinEdge.mapDerivedCategory_edge`, so with it that
comparison applies to the Gysin edge morphism of [Stacks, Tag 0G8A].  The three inputs it is
composed of are named in the implementation notes; the only hypothesis is `hZ : IsClosed Z`. -/
theorem counitCompatible :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
    letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
    Stacks.CounitGysinEdge.CounitCompatible
      (modulePushforward (closedSubsetInclusion X Z))
      (_root_.SheafOfModules.toSheaf.{u} (structureSheafRing X))
      (forgetClosed X Z)
      (abelianClosedPushforward Z)
      (modulePushforwardCompToSheafIso (closedSubsetInclusion X Z))
      (derivedSupportedSectionsOnClosed X Z hZ)
      (derivedAbelianSupportedSectionsOnClosed X Z hZ)
      (forgetLocalCohomologyIso X Z hZ)
      (derivedPushforwardAdjunction X Z hZ).counit
      (abelianSupportPushCounit X Z hZ) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  let := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  intro K
  have hc := congr_app
    (derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit X Z hZ) K
  have hw := congr_app (whiskerRight_derivedSupportedSectionsToId X Z
    (derivedAbelianSupportedPushforward X Z hZ)
    (derivedAbelianSupportedPushforwardUnit X Z hZ)
    (derivedSupportedPushforward X Z hZ) (derivedSupportedPushforwardUnit X Z hZ)) K
  have he := congr_app (endoForgetComparison_eq X Z hZ) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hw he
  exact assemble _ _ _ _ _ _
    (congrArg (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategory.map hc)
    hw he

end Stacks.DeRham.CounitCompatibleGeometric

end
