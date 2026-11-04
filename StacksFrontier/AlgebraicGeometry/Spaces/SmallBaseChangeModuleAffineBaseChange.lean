module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# Affine base change for the base-change direct image of modules

Let

```
Y' --g'--> Y
|π'         |π
v           v
X' --g-->  X
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site `B`, with `π`
affine and `g` arbitrary.  For every quasi-coherent `𝒪_Y`-module `F` the base change map

`g^*(π_*F) ⟶ π'_*((g')^*F)`

is an isomorphism, naturally in `F`.  This is the base change clause of Stacks 07U8, which the
tree proves for the direct image `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU
(`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineHom`).  This file states it
for the direct image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` along a
representable morphism, whose sections over an étale chart `V` are the sections over the
base-changed chart `V ×_X Y`; that is the direct image in which the ideal direct images of
Stacks 0GV1 are written.  The two direct images are identified by
`AlgebraicGeometry.Space.modulePushforwardChartIso`, and the base change map here is the one of
`AlgebraicGeometry.Space.moduleBaseChangeMap` read through that identification on both sides.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeModuleBaseChangeMap`: the base change map
  `g^* ∘ π_* ⟶ π'_* ∘ (g')^*` of a commutative square, for the base-change direct image.
* `AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso`: its value at a
  quasi-coherent module, as an isomorphism, when the square is cartesian and `π` is affine.
* `AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso`: the same at
  the structure sheaf, `g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallBaseChangeModuleBaseChangeMap_app_of_isAffineHom`: the
  base change map is an isomorphism at every quasi-coherent module.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {π : Y ⟶ X} {g : X' ⟶ X} {π' : Y' ⟶ X'} {g' : Y' ⟶ Y}

/-- **The base change map `g^*(π_*F) ⟶ π'_*((g')^*F)` for the base-change direct image** of a
commutative square with representable vertical morphisms: the base change map
`AlgebraicGeometry.Space.moduleBaseChangeMap` of Stacks 03LU direct images, read on both sides
through the identification `AlgebraicGeometry.Space.modulePushforwardChartIso` of that direct
image with `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`. -/
def smallBaseChangeModuleBaseChangeMap (comm : g' ≫ π = π' ≫ g)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom) :
    smallBaseChangeModulePushforward.{u, u} B S hS π hπ ⋙ modulePullback B S hS g ⟶
      modulePullback B S hS g' ⋙ smallBaseChangeModulePushforward.{u, u} B S hS π' hπ' :=
  Functor.whiskerRight (modulePushforwardChartIso B S hS π hπ).inv (modulePullback B S hS g) ≫
    moduleBaseChangeMap π g π' g' comm ≫
      Functor.whiskerLeft (modulePullback B S hS g') (modulePushforwardChartIso B S hS π' hπ').hom

/-- The base change map of `AlgebraicGeometry.Space.smallBaseChangeModuleBaseChangeMap` at a
module. -/
theorem smallBaseChangeModuleBaseChangeMap_app (comm : g' ≫ π = π' ≫ g)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom)
    (F : Modules.{u, u} B S hS Y.1 Y.2) :
    (smallBaseChangeModuleBaseChangeMap comm hπ hπ').app F =
      (modulePullback B S hS g).map ((modulePushforwardChartIso B S hS π hπ).inv.app F) ≫
        (moduleBaseChangeMap π g π' g' comm).app F ≫
          (modulePushforwardChartIso B S hS π' hπ').hom.app ((modulePullback B S hS g').obj F) :=
  rfl

/-- **Affine base change for the base-change direct image, as an isomorphism** (the base change
clause of Stacks 07U8; Stacks 02KG for schemes): for a cartesian square whose right morphism `π`
is affine and a quasi-coherent `𝒪_Y`-module `F`, `g^*(π_*F) ≅ π'_*((g')^*F)`.  Its forward map
is the base change map `AlgebraicGeometry.Space.smallBaseChangeModuleBaseChangeMap`
(`AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso_hom`); it is assembled from
`AlgebraicGeometry.Space.moduleAffineBaseChangeIso` and the identification
`AlgebraicGeometry.Space.modulePushforwardChartIso` of the two direct images. -/
def smallBaseChangeModuleAffineBaseChangeIso (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    (modulePullback B S hS g).obj ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj F) ≅
      (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        ((modulePullback B S hS g').obj F) :=
  (modulePullback B S hS g).mapIso ((modulePushforwardChartIso B S hS π hπ).app F).symm ≪≫
    moduleAffineBaseChangeIso sq hπa F hF ≪≫
      (modulePushforwardChartIso B S hS π' hπ').app ((modulePullback B S hS g').obj F)

/-- The forward map of `AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso` is the
base change map `AlgebraicGeometry.Space.smallBaseChangeModuleBaseChangeMap`. -/
theorem smallBaseChangeModuleAffineBaseChangeIso_hom (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' F hF).hom =
      (smallBaseChangeModuleBaseChangeMap sq.w hπ hπ').app F := by
  refine Eq.trans ?_ (smallBaseChangeModuleBaseChangeMap_app sq.w hπ hπ' F).symm
  refine congrArg₂ (· ≫ ·) rfl ?_
  exact congrArg₂ (· ≫ ·) (moduleAffineBaseChangeIso_hom sq hπa F hF) rfl

/-- **Affine base change for the base-change direct image** (the base change clause of
Stacks 07U8; Stacks 02KG for schemes).  For a cartesian square of algebraic spaces whose right
morphism `π` is affine, the base change map `g^*(π_*F) ⟶ π'_*((g')^*F)` is an isomorphism at
every quasi-coherent `𝒪_Y`-module `F`.  The bottom morphism `g` is arbitrary. -/
theorem isIso_smallBaseChangeModuleBaseChangeMap_app_of_isAffineHom (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((smallBaseChangeModuleBaseChangeMap sq.w hπ hπ').app F) :=
  smallBaseChangeModuleAffineBaseChangeIso_hom sq hπa hπ hπ' F hF ▸
    Iso.isIso_hom (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' F hF)

/-- **The affine base change isomorphism is natural in the module**: for a morphism `φ : F ⟶ G`
of quasi-coherent `𝒪_Y`-modules, `g^*(π_*φ)` and `π'_*((g')^*φ)` correspond under it. -/
theorem smallBaseChangeModuleAffineBaseChangeIso_hom_naturality (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) {F G : Modules.{u, u} B S hS Y.1 Y.2}
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) (φ : F ⟶ G) :
    (modulePullback B S hS g).map ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).map φ) ≫
        (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' G hG).hom =
      (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' F hF).hom ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
          ((modulePullback B S hS g').map φ) := by
  rw [smallBaseChangeModuleAffineBaseChangeIso_hom, smallBaseChangeModuleAffineBaseChangeIso_hom]
  exact (smallBaseChangeModuleBaseChangeMap sq.w hπ hπ').naturality φ

/-- **Affine base change of the structure sheaf for the base-change direct image.**  For a
cartesian square with `π` affine and `g` arbitrary, `g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}`: the base change
map at `𝒪_Y`, followed by the direct image along `π'` of the identification
`(g')^*𝒪_Y ≅ 𝒪_{Y'}` of Stacks 03LU. -/
def modulePullbackSmallBaseChangeModulePushforwardUnitIso (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) :
    (modulePullback B S hS g).obj ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y))) ≅
      (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y')) :=
  smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' _
      (SheafOfModules.isQuasicoherentOnSite_unit _) ≪≫
    (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').mapIso
      (modulePullbackUnitIso B S hS g')

/-- The forward map of
`AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso` is the affine base
change isomorphism at `𝒪_Y` (whose forward map is the base change map,
`AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso_hom`) followed by the direct
image of `(g')^*𝒪_Y ≅ 𝒪_{Y'}`. -/
theorem modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) :
    (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom =
      (smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ'
          (SheafOfModules.unit (structureRingSheaf B S hS Y))
          (SheafOfModules.isQuasicoherentOnSite_unit _)).hom ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
          (modulePullbackUnitIso B S hS g').hom :=
  Iso.trans_hom _ _

end AlgebraicGeometry.Space

end
