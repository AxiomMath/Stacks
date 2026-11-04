module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# The higher direct images of an associated module along a morphism of representable spaces

Stacks 071N compares the higher direct images of a quasi-coherent module along a morphism of
schemes with the higher direct images of its associated module on the small étale sites:

`Rⁿ a_{small,*}(𝓕ᵃ) ≅ (Rⁿ a_* 𝓕)ᵃ`.

The étale clause is proved on the small étale sites of *schemes*,
`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleObjIso`.  This file carries it
across the identification of the small étale site of a representable algebraic space with the
small étale site of the representing scheme, so that it speaks of the direct image of modules
along a morphism of algebraic spaces (Stacks 03LU,
`AlgebraicGeometry.Space.modulePushforward`) and of the associated module of a Zariski module on
a representable algebraic space (`AlgebraicGeometry.Space.representedAssociatedModule`).

## Main results

* `nonempty_rightDerived_modulePushforward_representedAssociatedModule`: **the étale clause of
  Stacks 071N for a morphism of representable algebraic spaces**, for a quasi-compact and
  quasi-separated morphism of the big fppf site.
* `nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated`: the same
  for a quasi-compact separated morphism, the form its consumers state.

## Implementation notes

The transport to right derived functors is `StacksTag03LR.rightDerivedBaseChangeIso` applied to
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, the comparison of the two
underived direct images.  Its hypotheses are exactly that the two vertical comparisons be exact
and that the left one carry injectives to injectives.  Both comparisons are the functor of an
equivalence of module categories
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`), so all three hold: an
equivalence preserves all limits and colimits and preserves injective objects.

The statements carry `AlgebraicGeometry.Space.hasInjectiveResolutions_modules` and
`AlgebraicGeometry.Space.modulePushforward_additive` in the type through a `have`, as every
statement mentioning a right derived functor of `AlgebraicGeometry.Space.modulePushforward`
must: the modules on the small étale site of an algebraic space have injective resolutions by a
theorem, not by instance search, and additivity of the direct image is found only once that
instance is present.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The identification of the modules on the small étale site of the scheme underlying `U` with
the `𝒪`-modules on the small étale site of the representable algebraic space `yoneda.obj U`,
with its target written as `AlgebraicGeometry.Space.Modules` — the spelling in which the direct
image of modules along a morphism of algebraic spaces is stated.

This is `AlgebraicGeometry.Space.representedModulePushforward`; only the reading of its target
differs, and the two are definitionally equal.  Writing the comparison this way is what lets the
square of direct images be passed to right derived functors: the two readings of the structure
sheaf of rings of a representable algebraic space are definitionally but not reducibly equal, so
a composite that mixes them has `Preadditive` instances no statement of additivity can be found
by. -/
noncomputable abbrev representedModulePushforwardSpace (U : BigFppfOver B S hS) :
    SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U) ⥤
      Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  representedModulePushforward B S hS U

/-- The comparison of modules is additive. -/
instance additive_representedModulePushforwardSpace (U : BigFppfOver B S hS) :
    (representedModulePushforwardSpace B S hS U).Additive :=
  additive_representedModulePushforward B S hS U

/-- The comparison of modules is exact, being the functor of an equivalence: it preserves finite
limits. -/
instance preservesFiniteLimits_representedModulePushforwardSpace (U : BigFppfOver B S hS) :
    Limits.PreservesFiniteLimits (representedModulePushforwardSpace B S hS U) :=
  inferInstanceAs
    (Limits.PreservesFiniteLimits (representedSmallEtaleModuleEquivalence B S hS U).functor)

/-- The comparison of modules is exact, being the functor of an equivalence: it preserves finite
colimits. -/
instance preservesFiniteColimits_representedModulePushforwardSpace (U : BigFppfOver B S hS) :
    Limits.PreservesFiniteColimits (representedModulePushforwardSpace B S hS U) :=
  inferInstanceAs
    (Limits.PreservesFiniteColimits (representedSmallEtaleModuleEquivalence B S hS U).functor)

/-- The comparison of modules carries injective objects to injective objects, being the functor
of an equivalence. -/
instance preservesInjectiveObjects_representedModulePushforwardSpace
    (U : BigFppfOver B S hS) :
    (representedModulePushforwardSpace B S hS U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_isEquivalence
    (F := (representedSmallEtaleModuleEquivalence B S hS U).functor)

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The comparison of the two direct images of modules along a morphism of representable
algebraic spaces passes to the higher right derived functors.**  For a morphism `g : T' ⟶ T` of
the big fppf site over `S`, the identification of the small étale site of a representable
algebraic space with the small étale site of the representing scheme carries the `n`-th higher
direct image of modules along the represented morphism of algebraic spaces to the `n`-th higher
direct image along the morphism of small étale ringed sites of Stacks 070R (2) of the underlying
morphism of schemes.

This is `StacksTag03LR.rightDerivedBaseChangeIso` applied to
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`: the two vertical comparisons
are the functor of an equivalence of module categories, hence exact, and the left one carries
injectives to injectives. -/
noncomputable def representedRightDerivedModulePushforwardSquareIso (n : ℕ) :
    have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
    representedModulePushforwardSpace B S hS T' ⋙
        (modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived n ≅
      (SheafOfModules.pushforward.{u}
          (representedSchemeStructureMapRing B S hS g)).rightDerived n ⋙
        representedModulePushforwardSpace B S hS T := by
  haveI := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
  exact StacksTag03LR.rightDerivedBaseChangeIso
    (representedModulePushforwardSpace B S hS T')
    (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g))
    (modulePushforward B S hS (representedSpaceMap B S hS g))
    (representedModulePushforwardSpace B S hS T)
    (representedModulePushforwardSquareIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g)).symm n

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The étale clause of Stacks 071N for a morphism of representable algebraic spaces.**  Let
`g : T' ⟶ T` be a morphism of the big fppf site over `S` whose underlying morphism of schemes
`φ` is quasi-compact and quasi-separated, and let `𝓕` be a quasi-coherent `𝒪_{T'}`-module.  Then
the `n`-th higher direct image, along the morphism of algebraic spaces represented by `g`, of
the module associated with `𝓕` is the module associated with the Zariski higher direct image
`Rⁿφ_*𝓕`.

The comparison of the two underived direct images passes to the right derived functors by
`representedRightDerivedModulePushforwardSquareIso`, and the resulting higher direct image on
the small étale site of the scheme `T'` is identified with the associated module of `Rⁿφ_*𝓕` by
the étale clause of Stacks 071N on schemes,
`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleObjIso`. -/
theorem nonempty_rightDerived_modulePushforward_representedAssociatedModule
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map g))
    (hqs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map g))
    (F : ((BigFppfOver.toScheme B S hS).obj T').Modules) (hF : F.IsQuasicoherent) (n : ℕ) :
    have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
    Nonempty (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived n).obj
        ((representedAssociatedModule B S hS T'
          (isAlgebraicSpace_yoneda B S hS T')).obj F) ≅
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
        (((Scheme.Modules.pushforward
          ((BigFppfOver.toScheme B S hS).map g)).rightDerived n).obj F)) := by
  have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
  have := hF
  have : QuasiCompact (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) := hqc
  have : QuasiSeparated (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) := hqs
  exact ⟨(representedRightDerivedModulePushforwardSquareIso B S hS g n).app
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj F) ≪≫
    (representedModulePushforward B S hS T).mapIso
      (_root_.AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleObjIso
        (associatedBigEtaleSite B) g.left F n)⟩

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The étale clause of Stacks 071N for a morphism of representable algebraic spaces**, for a
quasi-compact *separated* morphism: a separated morphism of schemes is quasi-separated, so this
is `nonempty_rightDerived_modulePushforward_representedAssociatedModule`. -/
theorem nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map g))
    (hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g))
    (F : ((BigFppfOver.toScheme B S hS).obj T').Modules) (hF : F.IsQuasicoherent) (n : ℕ) :
    have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
    Nonempty (((modulePushforward B S hS (representedSpaceMap B S hS g)).rightDerived n).obj
        ((representedAssociatedModule B S hS T'
          (isAlgebraicSpace_yoneda B S hS T')).obj F) ≅
      (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj
        (((Scheme.Modules.pushforward
          ((BigFppfOver.toScheme B S hS).map g)).rightDerived n).obj F)) := by
  have := hsep
  have := modulePushforward_additive B S hS (representedSpaceMap B S hS g)
  exact nonempty_rightDerived_modulePushforward_representedAssociatedModule B S hS g hqc
    inferInstance F hF n

end AlgebraicGeometry.Space

end
