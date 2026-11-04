module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# [Stacks, Tag 08FE] at an open of the target, in the restriction spelling

[Stacks, Tag 08FE] — "forming the total direct image commutes with localization" — is formalized, and
it is formalized at an open of the target of a morphism of schemes:
`AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`,

> `Rf_* ⋙ L(V.ι)^* ≅ L((f ⁻¹ᵁ V).ι)^* ≫ R(f ∣_ V)_*`,

which is `Stacks.Cohomology.derivedPushforwardRestrictIso` at the standard derived functors and at
the cartesian square `AlgebraicGeometry.DerivedChow.isPullback_morphismRestrict`. Nothing about
that comparison is re-proved here, and no `@[stacks 08FE]` attribute is placed: it sits where the
comparison is built and where its scheme form is instantiated.

What this file adds is the **spelling bridge**. The restriction functor in 08FE's formalized forms is
the derived pullback of [Stacks, Tag 079W] along the inclusion of the open subscheme, while the
model crossings of conclusion (c) of [Stacks, Tag 0EX3] — `LerayOpenSubschemeSections.lean` and
`LerayOpenSubschemeDerived.lean` — are written with ordinary restriction
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` and its `mapDerivedCategory`. The two
agree, and that too is proved:
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`. So the bridge is two
whiskerings and no new mathematics.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPushforwardMorphismRestrictIso` —
  **[Stacks, Tag 08FE] at an open `V` of the target of a morphism of schemes `f : X ⟶ S`, with the
  restriction read as `mapDerivedCategory` of ordinary restriction**:

  > `Rf_* ⋙ D((-)|_V) ≅ D((-)|_{f⁻¹V}) ⋙ R(f ∣_ V)_*`.

  No hypothesis on `f` and none on `V`. It is the derived counterpart of the underived
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.modulePushforwardMorphismRestrictIso`, which is
  [Stacks, Tag 01E5] at Mathlib's restricted morphism.

## Implementation notes

*What the bridge is not.* One could instantiate
`Stacks.Cohomology.derivedPushforwardRestrictIso` afresh with the two restriction functors taken
to be `mapDerivedCategory` of `moduleRestriction` and their units transported along
`Stacks.Cohomology.ClosedSupportPerfect.pullbackOpenRestrictionIso`, but the transport does not
elaborate, a `(moduleRestriction X U).Additive` instance being missing. That
transport is **not needed**: 08FE is already instantiated at the standard derived functors, so the
restriction spelling can be changed in the *statement* instead of in the units, by whiskering an
existing isomorphism of functors onto each side. Nothing has to be synthesised at the problematic
spelling and no `IsRightDerivedFunctor` is re-established.

*Where that missing instance came from, for the record.* It is the recorded spelling pair:
`Stacks.Cohomology.HigherDirectImage.moduleRestriction X U` has target the modules on
`…HigherDirectImage.restrictToOpen X U`, while the functors the derived pullback is stated in have
source and target the modules on `X.restrict U.isOpenEmbedding`, and the two are definitionally
equal but not interchangeable for instance synthesis. The crossing is paid once in the tree, in
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`, whose three
exactness arguments are passed explicitly in a term-mode `exact` so that the conversion runs at
default transparency; every use after that is free.

*Why `AlgebraicGeometry.DerivedChow.ofScheme V.ι` needs no transport either.* It is
`V.ι.toLRSHom.toShHom`, which is
`…HigherDirectImage.openSubspaceInclusion S.toRingedSpace V` and hence
`S.toRingedSpace.ofRestrict V.isOpenEmbedding`, by `rfl` — `openSubspaceInclusion` being a
`noncomputable abbrev` for exactly that. The two are *not* interchangeable for instance synthesis
either, which is why the composition below is written at the `ofScheme` spelling 08FE
uses and `derivedPullbackModuleRestrictionIso` is matched against it in term mode.

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage (moduleRestriction)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open Stacks.Cohomology.DerivedOpenImmersion (derivedPullbackModuleRestrictionIso)
open AlgebraicGeometry.DerivedChow (ofScheme derivedPushforwardRestrictOpenIso)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08FE] at an open of the target, with the restriction read as ordinary
restriction.** For a morphism of schemes `f : X ⟶ S` and an open `V ⊆ S`, the derived direct image
along `f` restricted to `V` is the derived direct image along `f ∣_ V` of the restriction to
`f⁻¹V`:

> `Rf_* ⋙ D((-)|_V) ≅ D((-)|_{f⁻¹V}) ⋙ R(f ∣_ V)_*`,

where `D(-)` is `CategoryTheory.Functor.mapDerivedCategory` of
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, restriction being exact. There is no
hypothesis on `f` and none on `V`.

This is the derived counterpart of `modulePushforwardMorphismRestrictIso`, which is
[Stacks, Tag 01E5] at the same restricted morphism, and it is a **spelling bridge only**: the
comparison is `AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`, 08FE at the
standard derived functors of [Stacks, Tag 079W], and the two whiskered isomorphisms are
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`, the identification
of the derived pullback along the inclusion of an open subspace with ordinary restriction. Nothing
is re-proved and no `@[stacks …]` attribute is placed. -/
def derivedPushforwardMorphismRestrictIso {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    derivedPushforward (ofScheme f) ⋙
        (moduleRestriction S.toRingedSpace V).mapDerivedCategory ≅
      (moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)).mapDerivedCategory ⋙
        derivedPushforward (ofScheme (f ∣_ V)) :=
  Functor.isoWhiskerLeft (derivedPushforward (ofScheme f))
      (derivedPullbackModuleRestrictionIso S.toRingedSpace V).symm ≪≫
    derivedPushforwardRestrictOpenIso f V ≪≫
      Functor.isoWhiskerRight
        (derivedPullbackModuleRestrictionIso X.toRingedSpace (f ⁻¹ᵁ V))
        (derivedPushforward (ofScheme (f ∣_ V)))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
