module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChangeStalk
public import StacksFrontier.RingTheory.NaiveCotangent.FlatAlgebraLocalizedTarget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials

/-!
# Base change for the naive cotangent complex of a flat morphism, at a point of a cartesian square

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a *cartesian* square of schemes with `f` flat, and let `x'` be a point of `X'`. The stalk at
`x'` of the canonical comparison `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` is a quasi-isomorphism. The
analogous statement with `g` flat in place of `f` is
`Stacks.NaiveCotangentFlatBaseChangeStalk.quasiIso_stalkFunctor_map_baseChangeMapOfComparison`.

Writing `R`, `A`, `B`, `C` for the stalks at `x'` of `(g')^{-1}f^{-1}𝒪_Y`, `(g')^{-1}𝒪_X`,
`(f')^{-1}𝒪_{Y'}` and `𝒪_{X'}`, the canonical map `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` is a
quasi-isomorphism, since `A` is flat over `R` and `C` is a localization of `B ⊗_R A`. The
`R`-algebra structure on `A` is the stalk of the first map of the tower, which is the stalk map of
`f` conjugated by two isomorphisms of stalks, hence flat.

## Main results

In the namespace `Stacks.NaiveCotangentFlatAlgebraBaseChangeStalk`:

* `stalkFunctor_map_inverseImageFirstRingMap_eq`: the stalk of the first map of the tower is the
  stalk map of `f` conjugated by the two stalk identifications.
* `flat_stalkInverseImageMiddle`: that composite is flat when `f` is.
* `isQuasiIso_of_localization_data`: the ring-level base change for a flat algebra `A₀` over `R₀`
  and a localization `C₀` of `B₀ ⊗[R₀] A₀`.
* `isQuasiIso_nlExtensionBaseChangeMap_stalk`: the map `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` is a
  quasi-isomorphism at every point of a cartesian square with `f` flat.
* `quasiIso_stalkFunctor_map_baseChangeComposite`: the stalk of the three-factor composite
  defining the canonical base change map is a quasi-isomorphism.
* `quasiIso_stalkFunctor_map_baseChangeMapOfComparison`: the stalk of the canonical base change
  map is a quasi-isomorphism.

## Implementation notes

The `R`-algebra structure on `A` is the stalk of the first map of the tower, which is the
structure the complexes are built from. The `R`-algebra structure on `B` is transported along
`Stacks.NaiveCotangentFlatBaseChangeStalk.exists_isLocalization_tensor_congr`, which substitutes
an equality of the two ring maps defining the algebra structure on the left tensor factor.

The two scalar towers are introduced with an explicit type ascription and passed by name:
`Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase` states its conclusion under a chain of
`letI`s, so instance search does not see through the type of the hypothesis it produces.

`Algebra.TensorProduct.rightAlgebra` is a local instance: it is the `A`-algebra structure on
`B ⊗_R A` that makes the latter a target for base change of `NL_{A/R}`.

## References

* [Stacks Project, Tag 0FK0](https://stacks.math.columbia.edu/tag/0FK0), base change for the naive
  cotangent complex of a morphism of schemes.
* [Stacks Project, Tag 0FJU](https://stacks.math.columbia.edu/tag/0FJU), the ring-level base
  change along a cocartesian square with one flat side.
* [Stacks Project, Tag 01JR](https://stacks.math.columbia.edu/tag/01JR), fibre products of
  schemes, whose local rings the localization statement describes.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of the
  naive cotangent complex, the first factor of the comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf)
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.BaseChangeStalk

universe u

noncomputable section

namespace Stacks.NaiveCotangentFlatAlgebraBaseChangeStalk

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {X Y X' Y' : Scheme.{u}}

/-- **The stalk of the first map `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X` of the tower**, written as
the stalk map of `f` conjugated by the two stalk identifications. -/
theorem stalkFunctor_map_inverseImageFirstRingMap_eq (f : X ⟶ Y) (g' : X' ⟶ X)
    (x' : X'.carrier) :
    (stalkInverseImageBaseRingIso f g' x').hom ≫ f.stalkMap (g'.base x') ≫
          (stalkInverseImageMiddleRingIso g' x').inv =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
        (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom :=
  (Category.assoc _ _ _).symm.trans <| (Iso.comp_inv_eq _).mpr
    (stalkInverseImageBaseRingIso_hom_comp_stalkMap f g' x').symm

/-- For a flat `f`, the `𝒪_{Y,y}`-algebra structure that the stalk of the first map of the tower
puts on the stalk of `(g')^{-1}𝒪_X` is flat. -/
theorem flat_stalkInverseImageMiddle (f : X ⟶ Y) (g' : X' ⟶ X)
    [AlgebraicGeometry.Flat f] (x' : X'.carrier) :
    RingHom.Flat ((stalkInverseImageBaseRingIso f g' x').hom ≫ f.stalkMap (g'.base x') ≫
      (stalkInverseImageMiddleRingIso g' x').inv).hom :=
  RingHom.Flat.comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
      (stalkInverseImageBaseRingIso f g' x').hom))
    (RingHom.Flat.comp (AlgebraicGeometry.Flat.stalkMap f (g'.base x'))
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
        (stalkInverseImageMiddleRingIso g' x').inv)))

open Stacks.Sites.Conormal (stalkIsScalarTowerSquareBase stalkIsScalarTowerSquareTarget)

/-- Let `A₀` be a flat `R₀`-algebra, and let `C₀` be an `A₀`- and `B₀`-algebra which, through a
ring map `ψ : B₀ ⊗[R₀] A₀ →+* C₀` compatible with both, is a localization of `B₀ ⊗[R₀] A₀`. Then
the base change map `NL_{A₀/R₀} ⊗_{A₀} C₀ ⟶ NL_{C₀/B₀}` along `h` is a quasi-isomorphism. -/
theorem isQuasiIso_of_localization_data {R₀ A₀ B₀ C₀ : Type u} [CommRing R₀] [CommRing A₀]
    [CommRing B₀] [CommRing C₀] [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra A₀ C₀] [Algebra B₀ C₀]
    [Algebra R₀ C₀] [IsScalarTower R₀ A₀ C₀] [IsScalarTower R₀ B₀ C₀] [Module.Flat R₀ A₀]
    (ψ : TensorProduct R₀ B₀ A₀ →+* C₀)
    (hL : ψ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap B₀ C₀)
    (hR : ψ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap A₀ C₀)
    (M : Submonoid (TensorProduct R₀ B₀ A₀))
    (hM : letI := ψ.toAlgebra; IsLocalization M C₀)
    (h : (Algebra.Generators.self R₀ A₀).toExtension.Hom
      (Algebra.Generators.self B₀ C₀).toExtension) :
    NaiveCotangent.IsQuasiIso
      (NaiveCotangent.nlExtensionBaseChangeMap (T := C₀) h) := by
  let := ψ.toAlgebra
  have := hM
  have : IsScalarTower B₀ (TensorProduct R₀ B₀ A₀) C₀ := IsScalarTower.of_algebraMap_eq' hL.symm
  have : IsScalarTower A₀ (TensorProduct R₀ B₀ A₀) C₀ := IsScalarTower.of_algebraMap_eq' hR.symm
  exact NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_algebra M h

section Point

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- At a point `x'` of a cartesian square whose right vertical morphism `f` is flat, the base
change map `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` of the stalks at `x'` of `(g')^{-1}f^{-1}𝒪_Y`,
`(g')^{-1}𝒪_X`, `(f')^{-1}𝒪_{Y'}` and `𝒪_{X'}` is a quasi-isomorphism. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_stalk [AlgebraicGeometry.Flat f]
    (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    letI := algebraStalk
      (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom x'
    letI := algebraStalk ((inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom) ≫
      ringedSpaceStructureMap g'.toLRSHom.toShHom).hom x'
    letI := algebraStalk (ringedSpaceStructureMap g'.toLRSHom.toShHom).hom x'
    letI := algebraStalk (baseRingComparison f f' g' g hsq.w).hom x'
    letI := algebraStalk (ringedSpaceStructureMap f'.toLRSHom.toShHom).hom x'
    letI : IsScalarTower
      (ToType (TopCat.Presheaf.stalk
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')) :=
      stalkIsScalarTowerSquareBase
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (inverseImageSheaf f'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
      (ringedSpaceStructureMap f'.toLRSHom.toShHom)
      ((inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom) ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom)
      (baseRingComparison f f' g' g hsq.w) x'
      (baseRingComparison_comp f f' g' g hsq.w).symm
    letI : IsScalarTower
      (ToType (TopCat.Presheaf.stalk
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')) :=
      stalkIsScalarTowerSquareTarget
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
      (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      ((inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom) ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom)
      (ringedSpaceStructureMap g'.toLRSHom.toShHom) x' rfl
    ∀ h : (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk
              (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
            (ToType (TopCat.Presheaf.stalk
              (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x'))).toExtension.Hom
          (Algebra.Generators.self
            (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x'))
            (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x'))).toExtension,
        NaiveCotangent.IsQuasiIso
          (NaiveCotangent.nlExtensionBaseChangeMap
            (T := ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')) h) := by
  let := algebraStalk (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom x'
  let := algebraStalk ((inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom) ≫
    ringedSpaceStructureMap g'.toLRSHom.toShHom).hom x'
  let := algebraStalk (ringedSpaceStructureMap g'.toLRSHom.toShHom).hom x'
  let := algebraStalk (baseRingComparison f f' g' g hsq.w).hom x'
  let := algebraStalk (ringedSpaceStructureMap f'.toLRSHom.toShHom).hom x'
  have towB : IsScalarTower
      (ToType (TopCat.Presheaf.stalk
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')) :=
    stalkIsScalarTowerSquareBase
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (inverseImageSheaf f'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
      (ringedSpaceStructureMap f'.toLRSHom.toShHom)
      ((inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom) ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom)
      (baseRingComparison f f' g' g hsq.w) x'
      (baseRingComparison_comp f f' g' g hsq.w).symm
  have towA : IsScalarTower
      (ToType (TopCat.Presheaf.stalk
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')) :=
    stalkIsScalarTowerSquareTarget
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
      (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      ((inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom) ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom)
      (ringedSpaceStructureMap g'.toLRSHom.toShHom) x' rfl
  have hflat : RingHom.Flat (CommRingCat.Hom.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
        (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom)) :=
    (congrArg (fun φ : CommRingCat.Hom
        ((inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).presheaf.stalk x')
        ((inverseImageMiddleRing g'.toLRSHom.toShHom).presheaf.stalk x') =>
      RingHom.Flat (CommRingCat.Hom.hom φ))
      (stalkFunctor_map_inverseImageFirstRingMap_eq f g' x')) ▸
      flat_stalkInverseImageMiddle f g' x'
  have : Module.Flat
      (ToType (TopCat.Presheaf.stalk
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x')) :=
    hflat
  obtain ⟨ψ, hL, hR, M, hM⟩ :=
    Stacks.NaiveCotangentFlatBaseChangeStalk.exists_isLocalization_tensor_congr
    (R₀ := (ToType (TopCat.Presheaf.stalk
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x')))
    (A₀ := (ToType (TopCat.Presheaf.stalk (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x')))
    (B₀ := (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x')))
    (C₀ := (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')))
    (congrArg CommRingCat.Hom.hom
      (Stacks.NaiveCotangentFlatBaseChangeStalk.stalkFunctor_map_baseRingComparison_eq
        f g f' g' hsq.w x'))
    (stalk_isLocalization_of_isPullback_inverseImage_comm f g g' f' hsq x')
  exact @isQuasiIso_of_localization_data _ _ _ _ _ _ _ _ _ _ _ _ _ towA towB _ ψ hL hR M hM

/-- **The stalk of the canonical base change map of a cartesian square whose right vertical
morphism is flat is a quasi-isomorphism**, for the map written as the composite of the
identification of `(g')^*NL_{X/Y}` with a base change, the base-change map of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and the relative map of the tower through
`(f')^{-1}𝒪_{Y'}`. -/
theorem quasiIso_stalkFunctor_map_baseChangeComposite [AlgebraicGeometry.Flat f]
    (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    QuasiIso ((((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map
      ((Stacks.SheafOfModules.pulledNaiveCotangentComparison g'.toLRSHom.toShHom
          f.toLRSHom.toShHom).hom ≫
        Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap
            (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
            (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
            (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
            (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫
          eqToHom (congrArg
            (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
              (Opens.grothendieckTopology X'.toRingedSpace.carrier)
              (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
              X'.toRingedSpace.sheaf) (baseRingComparison_comp f f' g' g hsq.w)) ≫
            Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap
              (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
              (inverseImageSheaf f'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
              (baseRingComparison f f' g' g hsq.w)
              (ringedSpaceStructureMap f'.toLRSHom.toShHom))) := by
  have habs := Stacks.SheafOfModules.eqToHom_comp_spaceRelativeNaiveCotangentComplexMap
    (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (inverseImageMiddleRing g'.toLRSHom.toShHom) (inverseImageSheaf f'.toLRSHom.toShHom)
    X'.toRingedSpace.sheaf (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (ringedSpaceStructureMap g'.toLRSHom.toShHom) (baseRingComparison f f' g' g hsq.w)
    (ringedSpaceStructureMap f'.toLRSHom.toShHom) (baseRingComparison_comp f f' g' g hsq.w)
  refine Eq.mpr (congrArg (fun φ => QuasiIso
    ((((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
        X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map φ))
    (congrArg (fun t => (Stacks.SheafOfModules.pulledNaiveCotangentComparison
        g'.toLRSHom.toShHom f.toLRSHom.toShHom).hom ≫ t)
      (congrArg (fun t => Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap
          (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (inverseImageMiddleRing g'.toLRSHom.toShHom) X'.toRingedSpace.sheaf
          (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
          (ringedSpaceStructureMap g'.toLRSHom.toShHom) ≫ t) habs))) ?_
  rw [CategoryTheory.Functor.map_comp]
  have := Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite
    (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (inverseImageMiddleRing g'.toLRSHom.toShHom) (inverseImageSheaf f'.toLRSHom.toShHom)
    X'.toRingedSpace.sheaf (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (ringedSpaceStructureMap g'.toLRSHom.toShHom) (baseRingComparison f f' g' g hsq.w)
    (ringedSpaceStructureMap f'.toLRSHom.toShHom) x'
    (baseRingComparison_comp f f' g' g hsq.w)
    (isQuasiIso_nlExtensionBaseChangeMap_stalk f g f' g' hsq x')
  infer_instance

/-- **The stalk of the canonical base change map of a cartesian square whose right vertical
morphism is flat is a quasi-isomorphism**, stated for the map
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` itself rather than for the
three-factor composite it is defined to be. -/
theorem quasiIso_stalkFunctor_map_baseChangeMapOfComparison [AlgebraicGeometry.Flat f]
    (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    QuasiIso ((((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map
      (Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison f f' g'
        (baseRingComparison f f' g' g hsq.w)
        (baseRingComparison_comp f f' g' g hsq.w))) := by
  refine Eq.mpr (congrArg (fun χ => QuasiIso χ)
      (congrArg (fun χ => (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map χ) ?_))
    (quasiIso_stalkFunctor_map_baseChangeComposite f g f' g' hsq x')
  rfl

end Point

end Stacks.NaiveCotangentFlatAlgebraBaseChangeStalk

end

end
