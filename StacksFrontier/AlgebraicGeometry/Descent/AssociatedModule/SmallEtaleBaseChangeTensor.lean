module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModulesPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral

/-!
# Small étale base change of schemes as a morphism of ringed topoi, and its Stacks 03EL

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site.  The morphism of small étale ringed
sites `ε_a = (a_small, a_small^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Stacks 070R (2) is
`AlgebraicGeometry.smallEtaleRingedSiteHom`, and pullback of sheaves of modules along it is
formed, in the descent development, as Mathlib's two-field pullback
`SheafOfModules.pullback (AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing B a)`
(`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` is stated with it).  The comparison
of Stacks 03EL, `Stacks.SheafOfModules.pullbackTensorIso`, is stated for the pullback of modules
along a *four-field* morphism of ringed topoi.  This file supplies the four-field morphism for
`ε_a`, identifies its pullback of modules with the two-field one, and reads Stacks 03EL across
that identification:

`ε_a^*(𝓕 ⊗_{𝒪_Y} 𝓖) ≅ ε_a^*𝓕 ⊗_{𝒪_X} ε_a^*𝓖`

for arbitrary sheaves of modules `𝓕`, `𝓖` on the small étale site of `Y`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom`: `ε_a` as a morphism of ringed
  topoi in the shape the pullback of modules of Stacks 03D6 and the comparison of Stacks 03EL
  consume.
* `AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso`: **its pullback of modules is
  `SheafOfModules.pullback (smallEtaleStructureMapRing B a)`.**
* `AlgebraicGeometry.SmallEtale.baseChangeTensorIso`: **Stacks 03EL for small étale base change
  of schemes**, read across that identification.

## Implementation notes

The identification is
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` of `ε_a` and nothing
else: the site-presented pullback `RingedToposSiteHom.pullbackToposGeneral` of `ε_a` is
`SheafOfModules.pullback` of its structure map on sheaves of rings, and that structure map *is*
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`, by definition.  So this is the shape of
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` for `ε : S_étale ⟶ S_Zar`, and the
transported comparison is `Stacks.SheafOfModules.pullbackTensorIsoTransport`, as for
`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`.

The statement of the identification is written at the category of functors between sheaves of
modules over `AlgebraicGeometry.SmallEtale.structureSheaf`, given explicitly to `Iso`.  Left to
be inferred from the pullback of modules, that category is spelled with
`AlgebraicGeometry.RingedSite.ringSheaf`-style projections of the small étale ringed site, and
the adjointness instance `SheafOfModules.pullback` asks for is then sought at that spelling, where
`AlgebraicGeometry.SmallEtale.pushforward_smallEtaleStructureMapRing_isRightAdjoint` is not found.

No `@[stacks]` attribute is claimed: Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso`, which proves it for an arbitrary morphism of ringed
topoi, and this instantiates it at one morphism.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The morphism of small étale ringed sites `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Stacks
070R (2), in the shape `Stacks.Sheaves.RingedToposModules.RingedToposHom` that the pullback of
modules of Stacks 03D6 and the comparison of Stacks 03EL consume.

This is `AlgebraicGeometry.smallEtaleRingedSiteHom` pushed through
`AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom` and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`. -/
abbrev baseChangeRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedSite B X.obj X.property).toRingedTopos
      (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos :=
  (smallEtaleRingedSiteHom B a).toRingedToposHom.toRingedToposModulesHom

/-- **The pullback of sheaves of modules along `ε_a`, taken along the morphism of ringed topoi, is
pullback along the structure map `smallEtaleStructureMapRing B a`.**

`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` compares it with the
pullback along the site-presented morphism, which is `SheafOfModules.pullback` of the structure
map of `ε_a` on sheaves of rings, that is, of `smallEtaleStructureMapRing B a`. -/
def pullbackModulesBaseChangeIso :
    @Iso (_root_.SheafOfModules.{u} (structureSheaf B Y.obj Y.property) ⥤
        _root_.SheafOfModules.{u} (structureSheaf B X.obj X.property)) _
      (pullbackModules.{u, u, u, u + 1, u, u + 1} (baseChangeRingedToposModulesHom B a))
      (_root_.SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) :=
  (smallEtaleRingedSiteHom B a).pullbackModulesToposIsoGeneral

/-- **Stacks 03EL for small étale base change of schemes.**  For sheaves of modules `𝓕` and `𝓖`
on the small étale site of `Y`,

`ε_a^*(𝓕 ⊗_{𝒪_Y} 𝓖) ≅ ε_a^*𝓕 ⊗_{𝒪_X} ε_a^*𝓖`,

with no hypothesis on `𝓕` or `𝓖`, where `ε_a^*` is
`SheafOfModules.pullback (smallEtaleStructureMapRing B a)`.

This is `Stacks.SheafOfModules.pullbackTensorIso` at
`AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom`, read across
`AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso` by
`Stacks.SheafOfModules.pullbackTensorIsoTransport`; its naturality in both factors is
`Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality`. -/
def baseChangeTensorIso
    (M N : _root_.SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) :
    (_root_.SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B Y.obj Y.property).toRingedTopos.O).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B X.obj X.property).toRingedTopos.O).obj
        ((_root_.SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj M)).obj
        ((_root_.SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport (baseChangeRingedToposModulesHom B a)
    (pullbackModulesBaseChangeIso B a) M N

end AlgebraicGeometry.SmallEtale

end
