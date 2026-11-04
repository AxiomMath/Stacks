module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange

/-!
# The Zariski restriction of a direct image on the small étale site

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `r` be the underlying
morphism of schemes.  Restriction of an `𝒪`-module on the small étale site to the small Zariski
site, `AlgebraicGeometry.SmallEtale.restrictModule`, commutes with the direct image: for an
`𝒪_{X_étale}`-module `N`,

`(ε_{a*}N)|_{Y_Zar} ≅ r_*(N|_{X_Zar})`,

naturally in `N`, where `ε_a` is the morphism of ringed sites `(X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)`
of Stacks 070R (2).

This is the right-adjoint companion of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, and unlike that one it is a formal
consequence of the square of sites alone.  Both `restrictModule` and the direct image along a
morphism of schemes are `SheafOfModules.pushforward` along a functor of sites, and so is the
direct image along `ε_a`; so each of the two composites above is a pushforward along a composite
functor, and the comparison is `SheafOfModules.pushforwardComp` twice together with the
identification of the two composite functors.  That identification is exactly the square

```
  Y_Zar ---- V ↦ r⁻¹(V) ----> X_Zar
    |                           |
    v                           v
  Y_étale -- base change ----> X_étale
```

which `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleMorphismBaseChange.lean`
already supplies in both halves: `AlgebraicGeometry.SmallEtale.baseChangeOpensIso` geometrically
and `AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso` on structure sheaves.

## Main definitions

* `AlgebraicGeometry.SmallEtale.restrictModulePushforwardIso`: **the Zariski restriction of a
  direct image is the direct image of the Zariski restriction**, as an isomorphism of functors.
* `AlgebraicGeometry.SmallEtale.restrictModuleObjPushforwardIso`: the same at one module, which
  is the form `(ε_{a*}N)|_{Y_Zar} ≅ r_*(N|_{X_Zar})` in which it is used.

## Implementation notes

No `@[stacks]` attribute is carried: the commutation of a restriction of sites with a direct
image is not a statement of the Stacks project, which uses it silently.

The target is written with `SheafOfModules.pushforward` of
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` rather than with
`AlgebraicGeometry.Scheme.Modules.pushforward`; the two are definitionally equal, which
`AlgebraicGeometry.SmallEtale.pushforward_toRingCatSheafHom_eq` records, and the former is the
spelling `SheafOfModules.pushforwardComp` produces.

Both composite functors of the square are continuous, by the two instances
`AlgebraicGeometry.SmallEtale.isContinuous_opensMap_comp_opensToSmallEtale` and
`AlgebraicGeometry.SmallEtale.isContinuous_opensToSmallEtale_comp_baseChange`; nothing further
is needed, and in particular no property of `a` is used anywhere below.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The direct image of `𝒪`-modules along a morphism of schemes, in the spelling
`SheafOfModules.pushforwardComp` produces it: pushforward along the structure-sheaf comparison
of the morphism. -/
public theorem pushforward_toRingCatSheafHom_eq :
    SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom =
      Scheme.Modules.pushforward (schemeHom B a) :=
  rfl

/-- **The Zariski restriction of a direct image is the direct image of the Zariski
restriction.**  Pushing an `𝒪_{X_étale}`-module forward along `ε_a` and then restricting to the
small Zariski site of `Y` is restricting to the small Zariski site of `X` and then pushing
forward along `r`.

Each composite is a pushforward along a composite functor of sites, by
`SheafOfModules.pushforwardComp`, and the two composite functors are identified compatibly with
the two composite structure-sheaf comparisons by
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso` and
`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso`. -/
public def restrictModulePushforwardIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        restrictModule B Y.obj Y.property ≅
      restrictModule B X.obj X.property ⋙
        SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom :=
  SheafOfModules.pushforwardComp.{u} (structureMap B Y.obj Y.property)
      (smallEtaleStructureMapRing B a) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (baseChangeOpensIso B a)
      (structureMap_comp_baseChangeOpensIso B a) ≪≫
    (SheafOfModules.pushforwardComp.{u} (schemeHom B a).toRingCatSheafHom
      (structureMap B X.obj X.property)).symm

/-- **`(ε_{a*}N)|_{Y_Zar} ≅ r_*(N|_{X_Zar})`**, the identification of
`AlgebraicGeometry.SmallEtale.restrictModulePushforwardIso` read at a single
`𝒪_{X_étale}`-module. -/
public def restrictModuleObjPushforwardIso
    (N : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    (restrictModule B Y.obj Y.property).obj
        ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj N) ≅
      (Scheme.Modules.pushforward (schemeHom B a)).obj
        ((restrictModule B X.obj X.property).obj N) :=
  (restrictModulePushforwardIso B a).app N

end AlgebraicGeometry.SmallEtale

end
