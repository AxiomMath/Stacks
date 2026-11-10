module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelShiftedHom

/-!
# `Ext¹` out of the naive cotangent complex at the two models of the derived category

The group `Ext¹_{𝒪_X}(NL_{X/Y}, 𝒢)` of a morphism `f : X ⟶ Y` of ringed spaces is written twice
in this development:

* `AlgebraicGeometry.RingedSpaceThickening.extOneNaiveCotangent f 𝒢`, the group acting on the
  solutions of the lifting problems of **Stacks 08UC** and compared in **Stacks 0GQ3**, computed
  in the standard model `HasDerivedCategory.standard` of the derived category of
  `SheafOfModules (structureSheafRing X)`;
* `AlgebraicGeometry.RingedSpace.naiveCotangentExt f 𝒢 1`, the group of the second display of
  **Stacks 0DY9** and of the `Ext⁰` identification of
  `StacksFrontier/AlgebraicGeometry/Scheme/NaiveCotangentExtZero.lean`, computed in the locally
  small model of Tag 079Q, the global instance `SheafOfModules.hasDerivedCategory`.

The complex is the same term (`AlgebraicGeometry.RingedSpace.naiveCotangentComplex f`), the
category of coefficients is the same up to `rfl`, and the objects of the two derived categories are
the same; only the morphism types differ. This file identifies the two groups by the general
comparison `Stacks.Injectives.grothendieckModelShiftedHomAddEquiv` of
`StacksFrontier/Homology/DerivedCategory/GrothendieckModelShiftedHom.lean`, in degree `1`, and
records its compatibility with changing the complex along a map of complexes and with changing the
coefficients.

## Main definitions

* `AlgebraicGeometry.RingedSpace.extOneNaiveCotangentAddEquiv`: **the identification of the two
  `Ext¹_{𝒪_X}(NL_{X/Y}, 𝒢)`** for a morphism of ringed spaces.
* `AlgebraicGeometry.Scheme.extOneNaiveCotangentAddEquiv`: the same for a morphism of schemes.

## Main results

* `AlgebraicGeometry.RingedSpace.extOneNaiveCotangentAddEquiv_Q_map_comp`: compatibility with
  precomposition by a map of naive cotangent complexes.
* `AlgebraicGeometry.RingedSpace.extOneNaiveCotangentAddEquiv_comp_singleFunctor_map`:
  compatibility with a map of coefficient modules.

## Implementation notes

No `@[stacks]` attribute is attached: the two groups are the same mathematical object, and the
identification is the artefact of the two chosen models explained in
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **`Ext¹_{𝒪_X}(NL_{X/Y}, 𝒢)` at the two models of the derived category.** The group
`RingedSpaceThickening.extOneNaiveCotangent f 𝒢` of the standard model is identified with the
group `RingedSpace.naiveCotangentExt f 𝒢 1` of the model of Tag 079Q by the comparison of the two
models, which is the identity on objects. -/
def extOneNaiveCotangentAddEquiv {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    RingedSpaceThickening.extOneNaiveCotangent f G ≃+ naiveCotangentExt f G 1 :=
  Stacks.Injectives.grothendieckModelShiftedHomAddEquiv
    (SheafOfModules.{u} (structureSheafRing X)) _ _ 1

/-- The identification is the general comparison of shifted homomorphisms of the two models. -/
theorem extOneNaiveCotangentAddEquiv_apply {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : SheafOfModules.{u} (structureSheafRing X))
    (x : RingedSpaceThickening.extOneNaiveCotangent f G) :
    extOneNaiveCotangentAddEquiv f G x =
      Stacks.Injectives.grothendieckModelShiftedHomAddEquiv
        (SheafOfModules.{u} (structureSheafRing X)) _ _ 1 x := rfl

/-- **Compatibility with a map of coefficients**: pushing a class along `g : 𝒢 ⟶ 𝒢'` at the
standard model corresponds to pushing it along `g` at the model of Tag 079Q. -/
theorem extOneNaiveCotangentAddEquiv_comp_singleFunctor_map {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) {G G' : SheafOfModules.{u} (structureSheafRing X)} (g : G ⟶ G')
    (x : RingedSpaceThickening.extOneNaiveCotangent f G) :
    extOneNaiveCotangentAddEquiv f G'
        (x ≫ ((@DerivedCategory.singleFunctor _ _ _
          (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))) 0).map g)
            ⟦(1 : ℤ)⟧') =
      extOneNaiveCotangentAddEquiv f G x ≫
        ((DerivedCategory.singleFunctor (siteModules X) 0).map g)⟦(1 : ℤ)⟧' :=
  Stacks.Injectives.grothendieckModelShiftedHomAddEquiv_comp_singleFunctor_map x g

/-- **Compatibility with a map of naive cotangent complexes**: for morphisms `f : X ⟶ Y` and
`f' : X ⟶ Y'` with the same source and a map of complexes `φ : NL_{X/Y'} ⟶ NL_{X/Y}`, pulling a
class back along `Q.map φ` at the standard model corresponds to pulling it back along `Q.map φ` at
the model of Tag 079Q. -/
theorem extOneNaiveCotangentAddEquiv_Q_map_comp {X Y Y' : RingedSpace.{u, u}} (f : X ⟶ Y)
    (f' : X ⟶ Y') (G : SheafOfModules.{u} (structureSheafRing X))
    (φ : (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
        AlgebraicGeometry.RingedSpace.naiveCotangentComplex f') ⟶
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
        AlgebraicGeometry.RingedSpace.naiveCotangentComplex f))
    (x : RingedSpaceThickening.extOneNaiveCotangent f G) :
    extOneNaiveCotangentAddEquiv f' G
        ((@DerivedCategory.Q _ _ _
          (HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X)))).map φ ≫ x) =
      (DerivedCategory.Q (C := siteModules X)).map φ ≫ extOneNaiveCotangentAddEquiv f G x :=
  Stacks.Injectives.grothendieckModelShiftedHomAddEquiv_Q_map_comp φ x

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme

/-- **`Ext¹_{𝒪_X}(NL_{X/Y}, 𝒢)` at the two models of the derived category, for a morphism of
schemes**: the instance of `AlgebraicGeometry.RingedSpace.extOneNaiveCotangentAddEquiv` along the
underlying morphism of ringed spaces, which is how `AlgebraicGeometry.Scheme.naiveCotangentExt` is
defined. -/
def extOneNaiveCotangentAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules) :
    RingedSpaceThickening.extOneNaiveCotangent f.toLRSHom.toShHom G ≃+
      naiveCotangentExt f G 1 :=
  RingedSpace.extOneNaiveCotangentAddEquiv f.toLRSHom.toShHom G

end AlgebraicGeometry.Scheme

end
