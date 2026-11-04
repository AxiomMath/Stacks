module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence

/-!
# Internal Hom on an open subscheme, in the open-subscheme model

Let `S` be a scheme and `U ⊆ S` an open subscheme. `𝒪_U`-modules admit two models: sheaves of
modules on the slice site `Opens S / U`, and sheaves of modules on the ringed site of the scheme
`U.toScheme`. `AlgebraicGeometry.Scheme.Modules.overEquiv` is the equivalence between them, and
`Stacks.SheafOfModules.internalHomSchemeOpenIso` transports the internal Hom *sheaf* across it.
This file raises that transport to complexes and to derived categories, by instantiating the
general statements for an equivalence of ringed sites
(`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIsoOfIso` and
`siteEquivDerivedSheafHomIsoOfIso`) at the equivalence of sites
`TopologicalSpace.Opens.overEquivalence` and the structure map
`Stacks.SheafOfModules.schemeOpenPhi`.

With this, the right-hand side of `Stacks.SheafOfModules.derivedSheafHomSchemeRestriction` — the
derived internal Hom of the slice site, carried into the open-subscheme model — becomes the
derived internal Hom of the scheme `U.toScheme`, which is what
`derivedSheafHomSchemeRestrictionIso` below records: [Stacks, Tag 08DL] for the restriction of a
scheme to an open subscheme, with both sides in Mathlib's idiom.

## Main definitions

* `Stacks.SheafOfModules.sheafHomComplexSchemeOpenIso`: the chain-level transport.
* `Stacks.SheafOfModules.derivedSheafHomSchemeOpenIso`: the derived-level transport.
* `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`: the composite with the model
  comparison of `derivedSheafHomSchemeRestriction`.

## Main results

* `Stacks.SheafOfModules.sheafHomComplexSchemeOpenIso_natural`: the chain-level transport is
  natural in both variables.

## Implementation notes

No `@[stacks]` attribute is attached. `derivedSheafHomSchemeRestrictionIso` is Stacks 08DL in a
spelling the tag is not stated in, and the attribute for 08DL sits on
`AlgebraicGeometry.RingedSite.derivedHom_restriction_exists`, where the statement is for
restriction to a slice site; nothing here is a new tag delivery.

The exactness of `𝒪_U`-module pushforward along `schemeOpenPhi` is named rather than
synthesized, as in `Stacks.SheafOfModules.derivedOverFunctorEquiv`: `overEquiv` and the
pushforward along `schemeOpenPhi` are the same functor, but only definitionally, and
`AlgebraicGeometry.Scheme.Modules` being a semireducible `def` keeps synthesis from unfolding
one spelling to the other.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {S : Scheme.{u}} (U : S.Opens)

/-- **The internal Hom complex of the slice-site model, transported to the open-subscheme
model.** For complexes `A`, `B` of `𝒪_U`-modules given on the slice site `Opens S / U`, the
image under `AlgebraicGeometry.Scheme.Modules.overEquiv` of their internal Hom complex there is
the internal Hom complex, on the ringed site of the open subscheme `U`, of their images. -/
def sheafHomComplexSchemeOpenIso
    (A B : CochainComplex (_root_.SheafOfModules.{u} (S.ringCatSheaf.over U)) ℤ) :
    (((Scheme.Modules.overEquiv U).functor).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingedSite.sheafHomComplex ((ringedSite S.sheaf).over U) A B).obj ≅
      (RingedSite.sheafHomComplex (ringedSite U.toScheme.sheaf)
        ((((Scheme.Modules.overEquiv U).functor).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A)
        ((((Scheme.Modules.overEquiv U).functor).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj B)).obj :=
  RingedSite.siteEquivSheafHomComplexIsoOfIso
    (X := (ringedSite S.sheaf).over U) (Y := ringedSite U.toScheme.sheaf)
    U.overEquivalence.symm (schemeOpenPhi U) (hφ := isIso_schemeOpenPhi U) A B

/-- The chain-level transport is natural in both variables: it intertwines the maps
`AlgebraicGeometry.RingedSite.homMap` of internal Hom complexes. -/
theorem sheafHomComplexSchemeOpenIso_natural
    {A A' B B' : CochainComplex (_root_.SheafOfModules.{u} (S.ringCatSheaf.over U)) ℤ}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (((Scheme.Modules.overEquiv U).functor).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (RingedSite.homMap ((ringedSite S.sheaf).over U) f g) ≫
        (sheafHomComplexSchemeOpenIso U A' B').hom =
      (sheafHomComplexSchemeOpenIso U A B).hom ≫
        RingedSite.homMap (ringedSite U.toScheme.sheaf)
          ((((Scheme.Modules.overEquiv U).functor).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)
          ((((Scheme.Modules.overEquiv U).functor).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) :=
  RingedSite.siteEquivSheafHomComplexIsoOfIso_natural
    (X := (ringedSite S.sheaf).over U) (Y := ringedSite U.toScheme.sheaf)
    U.overEquivalence.symm (schemeOpenPhi U) (hφ := isIso_schemeOpenPhi U) f g

/-- **The derived internal Hom of the slice-site model, transported to the open-subscheme
model.** The image under `AlgebraicGeometry.Scheme.Modules.overEquiv` of
`RSheafHom(K, L)` computed on the slice site `Opens S / U` is the derived internal Hom, on the
ringed site of the open subscheme `U`, of the images of `K` and `L`. -/
def derivedSheafHomSchemeOpenIso
    (K L : DerivedCategory (_root_.SheafOfModules.{u} (S.ringCatSheaf.over U))) :
    ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor
          ((ringedSite S.sheaf).over U)).obj (op K)).obj L) ≅
      ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).obj
        (op (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj K))).obj
          (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj L) :=
  RingedSite.siteEquivDerivedSheafHomIsoOfIso
    (X := (ringedSite S.sheaf).over U) (Y := ringedSite U.toScheme.sheaf)
    U.overEquivalence.symm (schemeOpenPhi U) (hφ := isIso_schemeOpenPhi U)
    (hlim := inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.overEquiv U).functor))
    (hcolim := inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.overEquiv U).functor))
    K L

section Restriction

variable [HasSheafify (Opens.grothendieckTopology S) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology S).over U) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (_root_.SheafOfModules.overFunctor.{u} S.ringCatSheaf U)]
  [PreservesFiniteColimits (_root_.SheafOfModules.overFunctor.{u} S.ringCatSheaf U)]

/-- **[Stacks, Tag 08DL] for an open subscheme, in Mathlib's idiom.** For objects `K`, `L` of
`D(𝒪_S)` the derived internal Hom commutes with restriction along the open immersion
`U.ι : U.toScheme ⟶ S`: the restriction of `RSheafHom_{𝒪_S}(K, L)` to the open subscheme `U` is
the derived internal Hom `RSheafHom_{𝒪_U}(K|_U, L|_U)` on the ringed site of `U.toScheme`.

This is `Stacks.SheafOfModules.derivedSheafHomSchemeRestriction` — which lands in the
slice-site model of the derived internal Hom, carried across `overEquiv` — composed with
`derivedSheafHomSchemeOpenIso`, which identifies that with the derived internal Hom of the
scheme `U.toScheme`, and then with the model comparison
`Stacks.SheafOfModules.derivedOverFunctorEquiv` in each of the two variables. -/
def derivedSheafHomSchemeRestrictionIso
    (K L : DerivedCategory (StructureSheafModules S.sheaf)) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite S.sheaf)).obj (op K)).obj L) ≅
      ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).obj
        (op ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K))).obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj L) :=
  derivedSheafHomSchemeRestriction U K L ≪≫
    derivedSheafHomSchemeOpenIso U ((derivedRestrict S.sheaf U).obj K)
      ((derivedRestrict S.sheaf U).obj L) ≪≫
    ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).mapIso
      ((derivedOverFunctorEquiv U).app K).symm.op).app _ ≪≫
    ((RingedSite.derivedSheafHomBifunctor (ringedSite U.toScheme.sheaf)).obj
      (op ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K))).mapIso
        ((derivedOverFunctorEquiv U).app L)

end Restriction

end Stacks.SheafOfModules

end
