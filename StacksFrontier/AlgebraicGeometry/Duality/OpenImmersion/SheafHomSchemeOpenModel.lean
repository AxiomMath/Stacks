module

public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel

/-!
# The sheaf-hom of an open subscheme, in the open-subscheme model of its modules

Let `S` be a scheme and `U ⊆ S` an open subscheme. Modules on `U` have two models: sheaves of
modules on the slice site `Opens S / U` over the restricted sheaf of rings, and sheaves of
modules on the scheme `U.toScheme`. Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv` is the
equivalence between them.

`AlgebraicGeometry.RingedSite.internalHomSheaf` is available on both sides, since both are ringed
sites; this file identifies the two, that is to say it transports the internal Hom sheaf of the
slice-site model into the open-subscheme model:

`overEquiv(Hom_{𝒪_S|_U}(F, G)) ≅ Hom_{𝒪_U}(overEquiv F, overEquiv G)`.

That `overEquiv` is induced by an equivalence of the ringed sites underlying the two models,
with an invertible structure map, is exactly what
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` consumes, so all this file does
is exhibit `overEquiv` in that form and specialize.

## Main definitions

* `Stacks.SheafOfModules.schemeOpenPhi`: the structure map of `overEquiv`, read as the structure
  map of an equivalence of ringed sites.

## Main results

* `Stacks.SheafOfModules.internalHomSchemeOpenIso`: **the transport.** The internal Hom sheaf of
  the slice-site model of `𝒪_U`-modules, carried into the open-subscheme model by `overEquiv`, is
  the internal Hom sheaf of the ringed site of `U.toScheme`.
* `Stacks.SheafOfModules.internalHomSchemeOpenIso_hom_app`: on sections over an open `W` of `U`
  it restricts a local morphism along `TopologicalSpace.Opens.overEquivalence`. This pins the
  isomorphism down, rather than merely asserting that some isomorphism exists.

## Implementation notes

This is the abelian-level input that
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedSheafHomSliceModel.lean` records as
missing: with it, the right-hand side of
`Stacks.SheafOfModules.derivedSheafHomSchemeRestriction` can be rewritten as the derived internal
Hom of the scheme `U.toScheme`, once the chain-level and derived-level analogues of
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` and
`AlgebraicGeometry.RingedSite.derivedHomRestriction` are built on top of it. Those are not here.

The statement is Stacks 0E8H for an equivalence of ringed sites, not for restriction to a
localization, so — as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InternalHomSiteEquivalence.lean` — nothing here
carries a `@[stacks]` attribute.

Five things are renamed with `inferInstanceAs`. Dense-subsiteness and continuity of the two
directions of `TopologicalSpace.Opens.overEquivalence U` are in Mathlib, but stated for
`Opens.grothendieckTopology ↥U` and `(Opens.grothendieckTopology ↥S).over U` and for
`overEquivalence.functor`/`inverse`, whereas the specialization needs them for
`(Stacks.SheafOfModules.ringedSite U.toScheme.sheaf).J` and
`((Stacks.SheafOfModules.ringedSite S.sheaf).over U).J` and for `overEquivalence.symm`; and the
invertibility of the structure map is Mathlib's `Iso.isIso_inv` at the first spelling. Those are
the same by unfolding a scheme's carrier and `Equivalence.symm`, which instance synthesis will
not do.

For the same reason `isIso_schemeOpenPhi` is passed to
`siteEquivInternalHomIsoOfIso` as the named argument `hφ` rather than left to synthesis: the two
statements of `IsIso (schemeOpenPhi U)` differ in which of the two interchangeable `Category`
instances of `CategoryTheory.Sheaf` they carry, and instance resolution does not identify them
even though `exact` does.

The structure map is Mathlib's own, `TopologicalSpace.Opens.overPullbackSheafEquivOver`, which is
what makes `(Scheme.Modules.overEquiv U).functor` and `SheafOfModules.pushforward schemeOpenPhi`
the same functor definitionally; `schemeOpenPhi` is an `abbrev` so that this stays visible.

## References

* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom

namespace Stacks.SheafOfModules

universe u

variable {S : Scheme.{u}} (U : S.Opens)

/-- Passing from an open `W` of `U` to the corresponding object of `Opens S / U` is a dense
subsite inclusion for the localized topologies, in the spelling of the two ringed sites. -/
instance overEquivalenceSymmFunctorIsDenseSubsite :
    U.overEquivalence.symm.functor.IsDenseSubsite
      (ringedSite U.toScheme.sheaf).J ((ringedSite S.sheaf).over U).J :=
  inferInstanceAs (U.overEquivalence.inverse.IsDenseSubsite
    (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology ↥S).over U))

/-- Passing from an object of `Opens S / U` to the corresponding open of `U` is a dense subsite
inclusion for the localized topologies, in the spelling of the two ringed sites. -/
instance overEquivalenceSymmInverseIsDenseSubsite :
    U.overEquivalence.symm.inverse.IsDenseSubsite
      ((ringedSite S.sheaf).over U).J (ringedSite U.toScheme.sheaf).J :=
  inferInstanceAs (U.overEquivalence.functor.IsDenseSubsite
    ((Opens.grothendieckTopology ↥S).over U) (Opens.grothendieckTopology ↥U))

/-- Passing from an open of `U` to the corresponding object of `Opens S / U` is continuous, in
the spelling of the two ringed sites. -/
instance overEquivalenceSymmFunctorIsContinuous :
    U.overEquivalence.symm.functor.IsContinuous
      (ringedSite U.toScheme.sheaf).J ((ringedSite S.sheaf).over U).J :=
  inferInstanceAs (U.overEquivalence.inverse.IsContinuous
    (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology ↥S).over U))

/-- Passing from an object of `Opens S / U` to the corresponding open of `U` is continuous, in
the spelling of the two ringed sites. -/
instance overEquivalenceSymmInverseIsContinuous :
    U.overEquivalence.symm.inverse.IsContinuous
      ((ringedSite S.sheaf).over U).J (ringedSite U.toScheme.sheaf).J :=
  inferInstanceAs (U.overEquivalence.functor.IsContinuous
    ((Opens.grothendieckTopology ↥S).over U) (Opens.grothendieckTopology ↥U))

/-- The structure map of `AlgebraicGeometry.Scheme.Modules.overEquiv`, read as the structure map
of an equivalence of ringed sites: the restriction of `𝒪_S` to `U` as a sheaf of rings on the
space `U` agrees with its restriction to the slice site, reindexed. -/
abbrev schemeOpenPhi :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite U.toScheme.sheaf).O) ⟶
      ((U.overEquivalence.symm.functor).sheafPushforwardContinuous RingCat.{u}
        (ringedSite U.toScheme.sheaf).J ((ringedSite S.sheaf).over U).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite S.sheaf).over U).O) :=
  (U.overPullbackSheafEquivOver.app S.ringCatSheaf).inv

/-- The structure map of `overEquiv` is invertible: it is the inverse of an isomorphism. -/
instance isIso_schemeOpenPhi : IsIso (schemeOpenPhi U) :=
  inferInstanceAs (IsIso (U.overPullbackSheafEquivOver.app S.ringCatSheaf).inv)

/-- **The sheaf-hom of the slice-site model, transported to the open-subscheme model.** For
`𝒪_U`-modules `F` and `G` given on the slice site `Opens S / U`, the image under
`AlgebraicGeometry.Scheme.Modules.overEquiv` of their internal Hom sheaf there is the internal
Hom sheaf, on the ringed site of the open subscheme `U`, of their images.

This is Stacks 0E8H for the equivalence of ringed sites underlying `overEquiv`, obtained from
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso`. -/
def internalHomSchemeOpenIso (F G : _root_.SheafOfModules.{u} (S.ringCatSheaf.over U)) :
    (Scheme.Modules.overEquiv U).functor.obj
        (RingedSite.internalHomSheaf ((ringedSite S.sheaf).over U) F G) ≅
      RingedSite.internalHomSheaf (ringedSite U.toScheme.sheaf)
        ((Scheme.Modules.overEquiv U).functor.obj F)
        ((Scheme.Modules.overEquiv U).functor.obj G) :=
  InternalHom.siteEquivInternalHomIsoOfIso
    (X := (ringedSite S.sheaf).over U) (Y := ringedSite U.toScheme.sheaf)
    U.overEquivalence.symm (schemeOpenPhi U) (hφ := isIso_schemeOpenPhi U) F G

/-- On sections over an open `W` of `U`, the transport restricts a local morphism along
`TopologicalSpace.Opens.overEquivalence`: the morphism attached to a section `α` acts at an
object `T` of `Opens U / W` exactly as `α` acts at the object of `Opens S / U` that `T`
corresponds to. -/
theorem internalHomSchemeOpenIso_hom_app
    (F G : _root_.SheafOfModules.{u} (S.ringCatSheaf.over U))
    (W : (ringedSite U.toScheme.sheaf).Cᵒᵖ)
    (α : ((Scheme.Modules.overEquiv U).functor.obj
      (RingedSite.internalHomSheaf ((ringedSite S.sheaf).over U) F G)).val.obj W)
    (T : (Over W.unop)ᵒᵖ)
    (x : ((restrFun (ringedSite U.toScheme.sheaf).O.obj W.unop).obj
      ((Scheme.Modules.overEquiv U).functor.obj F).val).obj T) :
    ((((internalHomSchemeOpenIso U F G).hom.val.app W).hom α).app T).hom x =
      (α.app ((Over.post U.overEquivalence.symm.functor).op.obj T)).hom x :=
  rfl

end Stacks.SheafOfModules

end
