module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerStalkBaseChangeHomology
public import StacksFrontier.RingTheory.NaiveCotangent.BaseChangeLocalizedTarget

/-!
# Base change for the naive cotangent complex of a cartesian square of schemes

Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' ---g--> Y
```
be a cartesian square of schemes, with **no** flatness assumed anywhere.  Stacks 0FV5 says that
the canonical map

`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`

induces an isomorphism on `H^0` and a surjection on `H^{-1}`.  Both conclusions are proved here
for that map, which is `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` taken
against the canonical base-ring comparison
`AlgebraicGeometry.BaseChangeStalk.baseRingComparison` of the square -- the same map the two
flat-base-change statements `Stacks.NaiveCotangentFlatBaseChange`
`.quasiIso_baseChangeMapOfComparison_of_flat_base` and
`.quasiIso_baseChangeMapOfComparison_of_flat_algebra` are about, where it is moreover a
quasi-isomorphism.  With no flatness the degree-`-1` half is a surjection and no more, which is
exactly what the source asserts.

## Main results

* `Stacks.NaiveCotangentBaseChange.isH₀IsoH₁Surj_of_localization_data`: the ring-level input of
  Stacks 0FV5, in the shape a cartesian square supplies its data: `C₀` is a localization of
  `B₀ ⊗_{R₀} A₀`.
* `Stacks.NaiveCotangentBaseChange.isH₀IsoH₁Surj_nlExtensionBaseChangeMap_stalk`: that
  ring-level input, discharged at every point of a cartesian square.
* `Stacks.NaiveCotangentBaseChange`
  `.isBijectiveOnCokernel_stalkFunctor_map_baseChangeMapOfComparison` and
  `.isSurjectiveOnKernel_stalkFunctor_map_baseChangeMapOfComparison`: the stalk of the canonical
  base change map is bijective on the cokernel of its differential and surjective on its
  kernel.
* `Stacks.NaiveCotangentBaseChange.isIso_homologyMap_zero_baseChangeMapOfComparison`:
  **Stacks 0FV5**, the degree-zero isomorphism.
* `Stacks.NaiveCotangentBaseChange.epi_homologyMap_negOne_baseChangeMapOfComparison`:
  **Stacks 0FV5**, the degree-minus-one surjection.

## Implementation notes

Every step is the corresponding step of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChangeStalk` with flatness
removed and the conclusion weakened in degree `-1`, and the two files share all of their
geometric input: the identification of `𝒪_{X',x'}` as a localization of
`𝒪_{Y',f'(x')} ⊗_{𝒪_{Y,y}} 𝒪_{X,g'(x')}`
(`AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage_comm`, which
is where cartesianness is used), the stalk of the canonical base-ring comparison
(`Stacks.NaiveCotangentFlatBaseChangeStalk.stalkFunctor_map_baseRingComparison_eq`) and the
transport of the localization data along it
(`Stacks.NaiveCotangentFlatBaseChangeStalk.exists_isLocalization_tensor_congr`).  What is
dropped is the flatness of that stalk, which is the only use flat base change makes of `[Flat g]`
and the only thing that would make the comparison a quasi-isomorphism.

The two scalar towers are introduced with an explicit type ascription and passed by name, for
the reason recorded in the flat companion: `Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase`
states its conclusion under a chain of `letI`s, so instance search does not see through the type
of the hypothesis it produces.

The passage from the two elementwise conditions on the stalks to `H^0` and `H^{-1}` is
`CochainComplex.isIso_homologyMap_zero_of_isBijectiveOnCokernel` and
`CochainComplex.epi_homologyMap_negOne_of_isSurjectiveOnKernel`, which need the two complexes to
vanish outside degrees `-1` and `0`; that is
`Stacks.NaiveCotangentFlatBaseChange.isZero_pulledComplex_X` and
`AlgebraicGeometry.Scheme.naiveCotangentComplex_isZero_X` carried through the stalk functor,
which is additive.

`Algebra.TensorProduct.rightAlgebra` is a local instance here as it is in the flat companion: it
is the `A`-algebra structure on `B ⊗_R A` that makes the latter a target for base change of
`NL_{A/R}`.

## References

* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5), base change for the
  naive cotangent complex of a morphism of schemes.
* [Stacks Project, Tag 0FUZ](https://stacks.math.columbia.edu/tag/0FUZ), the ring-level
  arbitrary base change, which the stalkwise input rests on.
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), the comparison of
  `NL_{X/Y}` with the ring-level naive cotangent complex over an affine open; the stalkwise
  reduction used here is its stalk-level counterpart, [Stacks, Tag 0D09].
* [Stacks Project, Tag 01JR](https://stacks.math.columbia.edu/tag/01JR), fibre products of
  schemes, whose local rings the localization statement describes.
* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for
  the naive cotangent complex, the companion statement this one drops the flatness from.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf)
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.BaseChangeStalk
open Stacks.NaiveCotangentFlatBaseChange (baseChangeMapOfComparison isZero_pulledComplex_X)
open Stacks.NaiveCotangentFlatBaseChangeStalk (stalkFunctor_map_baseRingComparison_eq
  exists_isLocalization_tensor_congr)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareBase stalkIsScalarTowerSquareTarget)

universe u

noncomputable section

namespace Stacks.NaiveCotangentBaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {X Y X' Y' : Scheme.{u}}

/-! ### The ring-level input -/

/-- **The ring-level input of Stacks 0FV5, from the localization data in the shape a cartesian
square of schemes supplies it.**  This is
`Stacks.NaiveCotangentFlatBaseChangeStalk.isQuasiIso_of_localization_data` with the flatness of
`R₀ → B₀` dropped and the conclusion correspondingly weakened in degree `1`. -/
theorem isH₀IsoH₁Surj_of_localization_data {R₀ A₀ B₀ C₀ : Type u} [CommRing R₀] [CommRing A₀]
    [CommRing B₀] [CommRing C₀] [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra A₀ C₀] [Algebra B₀ C₀]
    [Algebra R₀ C₀] [IsScalarTower R₀ A₀ C₀] [IsScalarTower R₀ B₀ C₀]
    (ψ : TensorProduct R₀ B₀ A₀ →+* C₀)
    (hL : ψ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap B₀ C₀)
    (hR : ψ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap A₀ C₀)
    (M : Submonoid (TensorProduct R₀ B₀ A₀))
    (hM : letI := ψ.toAlgebra; IsLocalization M C₀)
    (h : (Algebra.Generators.self R₀ A₀).toExtension.Hom
      (Algebra.Generators.self B₀ C₀).toExtension) :
    NaiveCotangent.IsH₀IsoH₁Surj
      (NaiveCotangent.nlExtensionBaseChangeMap (T := C₀) h) := by
  let := ψ.toAlgebra
  have := hM
  have : IsScalarTower B₀ (TensorProduct R₀ B₀ A₀) C₀ := IsScalarTower.of_algebraMap_eq' hL.symm
  have : IsScalarTower A₀ (TensorProduct R₀ B₀ A₀) C₀ := IsScalarTower.of_algebraMap_eq' hR.symm
  exact NaiveCotangent.isH₀IsoH₁Surj_nlExtensionBaseChangeMap_of_isLocalization_tensor M h

/-! ### The ring-level input at a point of a cartesian square -/

section Point

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The ring-level input of Stacks 0FV5, at a point of a cartesian square.**  This is
`Stacks.NaiveCotangentFlatBaseChangeStalk.isQuasiIso_nlExtensionBaseChangeMap_stalk` with the
flatness of `g` dropped: the localization of `𝒪_{X',x'}` is the one piece of data a cartesian
square supplies on its own, and it is all that is used. -/
theorem isH₀IsoH₁Surj_nlExtensionBaseChangeMap_stalk (hsq : IsPullback g' f' f g)
    (x' : X'.carrier) :
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
        NaiveCotangent.IsH₀IsoH₁Surj
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
  obtain ⟨ψ, hL, hR, M, hM⟩ := exists_isLocalization_tensor_congr
    (R₀ := (ToType (TopCat.Presheaf.stalk
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x')))
    (A₀ := (ToType (TopCat.Presheaf.stalk (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x')))
    (B₀ := (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x')))
    (C₀ := (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')))
    (congrArg CommRingCat.Hom.hom (stalkFunctor_map_baseRingComparison_eq f g f' g' hsq.w x'))
    (stalk_isLocalization_of_isPullback_inverseImage_comm f g g' f' hsq x')
  exact fun h => @isH₀IsoH₁Surj_of_localization_data _ _ _ _ _ _ _ _ _ _ _ _ _ towA towB
    ψ hL hR M hM h

/-! ### The stalk of the canonical base change map -/

/-- **The stalk of the canonical base change map of a cartesian square is bijective on the
cokernel of its differential.**  The map is the composite of the [Stacks, Tag 08TM]
identification of `(g')^*NL_{X/Y}` with a base change, the base-change map of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and the relative map of the tower through
`(f')^{-1}𝒪_{Y'}`; the first factor is an isomorphism, and the stalk of the other two is
bijective on the cokernel by
`Stacks.NaiveCotangentTowerStalk.isBijectiveOnCokernel_stalkFunctor_map_towerComposite` fed with
the ring-level arbitrary base change. -/
theorem isBijectiveOnCokernel_stalkFunctor_map_baseChangeComposite (hsq : IsPullback g' f' f g)
    (x' : X'.carrier) :
    CochainComplex.IsBijectiveOnCokernel
      ((((stalkFunctor
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
  refine Eq.mpr (congrArg (fun φ => CochainComplex.IsBijectiveOnCokernel
    ((((stalkFunctor
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
  exact (CochainComplex.isBijectiveOnCokernel_of_isIso _).comp
    (Stacks.NaiveCotangentTowerStalk.isBijectiveOnCokernel_stalkFunctor_map_towerComposite
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (inverseImageMiddleRing g'.toLRSHom.toShHom) (inverseImageSheaf f'.toLRSHom.toShHom)
      X'.toRingedSpace.sheaf (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (ringedSpaceStructureMap g'.toLRSHom.toShHom) (baseRingComparison f f' g' g hsq.w)
      (ringedSpaceStructureMap f'.toLRSHom.toShHom) x'
      (baseRingComparison_comp f f' g' g hsq.w)
      (isH₀IsoH₁Surj_nlExtensionBaseChangeMap_stalk f g f' g' hsq x'))

/-- **The stalk of the canonical base change map of a cartesian square is surjective on the
kernel of its differential.**  The three factors are the ones of
`isBijectiveOnCokernel_stalkFunctor_map_baseChangeComposite`, and nothing is claimed about
injectivity on that kernel. -/
theorem isSurjectiveOnKernel_stalkFunctor_map_baseChangeComposite (hsq : IsPullback g' f' f g)
    (x' : X'.carrier) :
    CochainComplex.IsSurjectiveOnKernel
      ((((stalkFunctor
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
  refine Eq.mpr (congrArg (fun φ => CochainComplex.IsSurjectiveOnKernel
    ((((stalkFunctor
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
  exact (CochainComplex.isSurjectiveOnKernel_of_isIso _).comp
    (Stacks.NaiveCotangentTowerStalk.isSurjectiveOnKernel_stalkFunctor_map_towerComposite
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (inverseImageMiddleRing g'.toLRSHom.toShHom) (inverseImageSheaf f'.toLRSHom.toShHom)
      X'.toRingedSpace.sheaf (inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (ringedSpaceStructureMap g'.toLRSHom.toShHom) (baseRingComparison f f' g' g hsq.w)
      (ringedSpaceStructureMap f'.toLRSHom.toShHom) x'
      (baseRingComparison_comp f f' g' g hsq.w)
      (isH₀IsoH₁Surj_nlExtensionBaseChangeMap_stalk f g f' g' hsq x'))

/-- **The stalk of the canonical base change map is bijective on the cokernel of its
differential**, stated for the map
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` itself rather than for the
three-factor composite it is defined to be.  The folding is done by rewriting rather than by
conversion, for the reason recorded on
`Stacks.NaiveCotangentFlatBaseChangeStalk.quasiIso_stalkFunctor_map_baseChangeMapOfComparison`:
underneath the stalk functor, two morphisms that differ by so much as one unfolding are compared
by descending through the mapped complex in every degree. -/
theorem isBijectiveOnCokernel_stalkFunctor_map_baseChangeMapOfComparison
    (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    CochainComplex.IsBijectiveOnCokernel
      ((((stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map
        (baseChangeMapOfComparison f f' g' (baseRingComparison f f' g' g hsq.w)
          (baseRingComparison_comp f f' g' g hsq.w))) := by
  refine Eq.mpr (congrArg (fun χ => CochainComplex.IsBijectiveOnCokernel χ)
      (congrArg (fun χ => (((stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map χ) ?_))
    (isBijectiveOnCokernel_stalkFunctor_map_baseChangeComposite f g f' g' hsq x')
  rfl

/-- **The stalk of the canonical base change map is surjective on the kernel of its
differential**, stated for the map
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` itself. -/
theorem isSurjectiveOnKernel_stalkFunctor_map_baseChangeMapOfComparison
    (hsq : IsPullback g' f' f g) (x' : X'.carrier) :
    CochainComplex.IsSurjectiveOnKernel
      ((((stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map
        (baseChangeMapOfComparison f f' g' (baseRingComparison f f' g' g hsq.w)
          (baseRingComparison_comp f f' g' g hsq.w))) := by
  refine Eq.mpr (congrArg (fun χ => CochainComplex.IsSurjectiveOnKernel χ)
      (congrArg (fun χ => (((stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
            X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).map χ) ?_))
    (isSurjectiveOnKernel_stalkFunctor_map_baseChangeComposite f g f' g' hsq x')
  rfl

end Point

/-! ### The vanishing of the two complexes outside degrees `-1` and `0`, on stalks -/

/-- The complex of stalks at a point of `(g')^*NL_{X/Y}` has no terms outside degrees `-1` and
`0`: the stalk functor is additive, so it carries the zero object to the zero object. -/
theorem isZero_stalkFunctor_pulledComplex_X (f : X ⟶ Y) (g' : X' ⟶ X) (x' : X'.carrier)
    (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero (((((stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
        X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).obj
      (Stacks.NaiveCotangentFlatBaseChange.pulledComplex f g')).X i) :=
  AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x' _
    (isZero_pulledComplex_X f g' i hneg hzero)

/-- The complex of stalks at a point of `NL_{X'/Y'}` has no terms outside degrees `-1` and
`0`. -/
theorem isZero_stalkFunctor_naiveCotangentComplex_X (f' : X' ⟶ Y') (x' : X'.carrier) (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero (((((stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (J := Opens.grothendieckTopology X'.toRingedSpace.carrier)
        X'.toRingedSpace.sheaf) x').mapHomologicalComplex (ComplexShape.up ℤ))).obj
      (AlgebraicGeometry.Scheme.naiveCotangentComplex f')).X i) :=
  AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj _ x' _
    (AlgebraicGeometry.Scheme.naiveCotangentComplex_isZero_X f' i hneg hzero)

/-! ### Stacks 0FV5 -/

/-- **Stacks 0FV5, the degree-zero isomorphism.**  For a cartesian square of schemes the
canonical map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` induces an isomorphism on degree-zero cohomology.

No flatness is assumed anywhere, and the canonical map is constructed and not assumed: it is
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` taken against the canonical
base-ring comparison `AlgebraicGeometry.BaseChangeStalk.baseRingComparison` of the square. -/
@[stacks 0FV5 "the degree-zero ISOMORPHISM, for a CARTESIAN square \
(`hsq : IsPullback g' f' f g`) and NO other hypothesis -- in particular no flatness.  The \
canonical map is CONSTRUCTED, not assumed: \
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` is the source's own composite \
of the [Stacks, Tag 08TM] identification of `(g')^*NL_{X/Y}` with a base change \
(`Stacks.SheafOfModules.pulledNaiveCotangentComparison`), the base-change map \
`NL_{B/A} (x)_B C -> NL_{C/A}` of [Stacks, Tag 0E1Y] \
(`Stacks.SheafOfModules.spaceBaseChangeNaiveCotangentMap`) for the tower \
`(g')^-1 f^-1 O_Y -> (g')^-1 O_X -> O_{X'}`, and the relative map `NL_{C/A} -> NL_{C/B}` \
(`Stacks.SheafOfModules.spaceRelativeNaiveCotangentComplexMap`) for the tower through \
`(f')^-1 O_{Y'}`.  The base-ring comparison it is taken against is the CANONICAL one of the \
square, `AlgebraicGeometry.BaseChangeStalk.baseRingComparison`, with its compatibility \
`AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp`; it is built from the square and is \
not a `Classical.choose` of a non-unique existence statement.  It is the same map the flat \
statements [Stacks, Tag 0FJZ] and [Stacks, Tag 0FK0] are about.  PROVED: the reduction to the \
stalks ([Stacks, Tag 08TL], through \
`AlgebraicGeometry.SheafOfModules.isIso_homologyMap_iff_forall_stalk`); the degreewise \
vanishing outside degrees -1 and 0; and the stalkwise statement \
`isBijectiveOnCokernel_stalkFunctor_map_baseChangeMapOfComparison`, which is \
`Stacks.NaiveCotangentTowerStalk.isBijectiveOnCokernel_stalkFunctor_map_towerComposite` read \
through the stalk identification of the naive cotangent complex ([Stacks, Tag 0D09], the \
stalk-level form of [Stacks, Tag 0D0I]) and fed with the ring-level ARBITRARY base change \
[Stacks, Tag 0FUZ] `NaiveCotangent.naiveCotangentComplex_baseChange_homology`, composed with \
localization of the target [Stacks, Tag 00S7] in \
`NaiveCotangent.isH₀IsoH₁Surj_nlExtensionBaseChangeMap_of_isLocalization_tensor`.  The one \
geometric input is the identification of `O_{X',x'}` as a localization of \
`O_{Y',f'(x')} (x)_{O_{Y,y}} O_{X,g'(x')}`, \
`AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage_comm` \
([Stacks, Tag 01JR]), and that is the one place cartesianness is used.  The companion clause, \
the `H^{-1}` surjection, is \
`Stacks.NaiveCotangentBaseChange.epi_homologyMap_negOne_baseChangeMapOfComparison`"]
theorem isIso_homologyMap_zero_baseChangeMapOfComparison (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) :
    IsIso (HomologicalComplex.homologyMap
      (baseChangeMapOfComparison f f' g' (baseRingComparison f f' g' g hsq.w)
        (baseRingComparison_comp f f' g' g hsq.w)) 0) :=
  (AlgebraicGeometry.SheafOfModules.isIso_homologyMap_iff_forall_stalk
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (J := Opens.grothendieckTopology X'.toRingedSpace.carrier) X'.toRingedSpace.sheaf)
    (baseChangeMapOfComparison f f' g' (baseRingComparison f f' g' g hsq.w)
      (baseRingComparison_comp f f' g' g hsq.w)) 0).2 fun x' =>
    CochainComplex.isIso_homologyMap_zero_of_isBijectiveOnCokernel _
      (isZero_stalkFunctor_pulledComplex_X f g' x')
      (isZero_stalkFunctor_naiveCotangentComplex_X f' x')
      (isBijectiveOnCokernel_stalkFunctor_map_baseChangeMapOfComparison f g f' g' hsq x')

/-- **Stacks 0FV5, the degree-minus-one surjection.**  For a cartesian square of schemes the
canonical map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` induces a surjection on degree-minus-one
cohomology.

No flatness is assumed anywhere, and nothing is claimed about injectivity in degree `-1`: the
source's `H^{-1}` assertion is a surjection and not an isomorphism, and that is exactly what the
ring-level statement provides. -/
@[stacks 0FV5 "the degree-minus-one SURJECTION, for a CARTESIAN square \
(`hsq : IsPullback g' f' f g`) and NO other hypothesis -- in particular no flatness.  The \
canonical map is the one described on \
`Stacks.NaiveCotangentBaseChange.isIso_homologyMap_zero_baseChangeMapOfComparison`, the same \
constructed map `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` taken against \
the canonical base-ring comparison of the square.  PROVED: the reduction of EPIMORPHY to the \
stalks (`AlgebraicGeometry.SheafOfModules.epi_homologyMap_iff_forall_stalk`, the epimorphy \
counterpart of [Stacks, Tag 08TL]); the degreewise vanishing outside degrees -1 and 0; and the \
stalkwise statement `isSurjectiveOnKernel_stalkFunctor_map_baseChangeMapOfComparison`, which is \
`Stacks.NaiveCotangentTowerStalk.isSurjectiveOnKernel_stalkFunctor_map_towerComposite` fed with \
the ring-level ARBITRARY base change [Stacks, Tag 0FUZ].  Only SURJECTIVITY on the degree -1 \
cycles is assumed and only a surjection is concluded, which is what the source asserts and all \
that [Stacks, Tag 0FUZ] supplies: injectivity there is the half flatness would buy, and is the \
content of the stronger [Stacks, Tag 0FJZ] / [Stacks, Tag 0FK0].  The companion clause, the \
`H^0` isomorphism, is \
`Stacks.NaiveCotangentBaseChange.isIso_homologyMap_zero_baseChangeMapOfComparison`"]
theorem epi_homologyMap_negOne_baseChangeMapOfComparison (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) :
    Epi (HomologicalComplex.homologyMap
      (baseChangeMapOfComparison f f' g' (baseRingComparison f f' g' g hsq.w)
        (baseRingComparison_comp f f' g' g hsq.w)) (-1)) :=
  (AlgebraicGeometry.SheafOfModules.epi_homologyMap_iff_forall_stalk
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (J := Opens.grothendieckTopology X'.toRingedSpace.carrier) X'.toRingedSpace.sheaf)
    (baseChangeMapOfComparison f f' g' (baseRingComparison f f' g' g hsq.w)
      (baseRingComparison_comp f f' g' g hsq.w)) (-1)).2 fun x' =>
    CochainComplex.epi_homologyMap_negOne_of_isSurjectiveOnKernel _
      (isZero_stalkFunctor_pulledComplex_X f g' x')
      (isZero_stalkFunctor_naiveCotangentComplex_X f' x')
      (isSurjectiveOnKernel_stalkFunctor_map_baseChangeMapOfComparison f g f' g' hsq x')

end Stacks.NaiveCotangentBaseChange

end

end
