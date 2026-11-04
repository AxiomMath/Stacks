module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeComparisonMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SquareBaseRingComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentTowerStalkQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat base change for the naive cotangent complex, at a point of a cartesian square

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a *cartesian* square of schemes with `g` flat, and let `x'` be a point of `X'`.  This file
proves that the stalk at `x'` of the canonical comparison `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` is a
quasi-isomorphism, which is the stalkwise statement Stacks 0FJZ reduces to.

The canonical comparison is the composite of the Stacks 08TM identification of `(g')^*NL_{X/Y}`
with the base change to `𝒪_{X'}` of `NL_{(g')^{-1}𝒪_X/(g')^{-1}f^{-1}𝒪_Y}`, the base-change map
of the tower `(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}`, and the relative map of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` — the comparison of base rings being the
canonical one, `AlgebraicGeometry.BaseChangeStalk.baseRingComparison`.  The first factor is an
isomorphism, so everything rests on the stalk of the last two, which is
`Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite`; what this file
supplies is that theorem's ring-level hypothesis.

Writing `R`, `A`, `B`, `C` for the stalks at `x'` of `(g')^{-1}f^{-1}𝒪_Y`, `(g')^{-1}𝒪_X`,
`(f')^{-1}𝒪_{Y'}` and `𝒪_{X'}`, the ring-level hypothesis is that the canonical map
`NL_{A/R} ⊗_A C ⟶ NL_{C/B}` is a quasi-isomorphism.  That is
`NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base`, whose two inputs are:

* `B` is flat over `R`.  The `R`-algebra structure on `B` is the stalk of the canonical base-ring
  comparison, which `AlgebraicGeometry.BaseChangeStalk.stalkFunctor_map_baseRingComparison`
  identifies with the stalk map of `g` conjugated by the three stalk identifications; so it is a
  composite of three isomorphisms of rings with a flat map, and `AlgebraicGeometry.Flat.stalkMap`
  provides the flatness of the latter.
* `C` is a localization of `B ⊗_R A`.  This is
  `AlgebraicGeometry.BaseChangeStalk.stalk_isLocalization_of_isPullback_inverseImage_comm`, the
  only place cartesianness of the square is used.

## Main results

* `Stacks.NaiveCotangentFlatBaseChangeStalk.stalkFunctor_map_baseRingComparison_eq` and
  `algebraStalk_baseRingComparison`: the stalk of the canonical base-ring comparison, as a
  morphism of rings and as an algebra structure.
* `Stacks.NaiveCotangentFlatBaseChangeStalk.flat_stalkInverseImage`: that algebra structure is
  flat when `g` is.
* `Stacks.NaiveCotangentFlatBaseChangeStalk.isQuasiIso_of_localization_data` and
  `exists_isLocalization_tensor_congr`: the ring-level flat base change in the shape the square
  supplies its data, and the transport of that data along an equality of the ring map defining
  the algebra structure on the flat factor.
* `Stacks.NaiveCotangentFlatBaseChangeStalk.isQuasiIso_nlExtensionBaseChangeMap_stalk`: **the
  ring-level hypothesis**, discharged at every point of a cartesian square with flat base.
* `Stacks.NaiveCotangentFlatBaseChangeStalk.quasiIso_stalkFunctor_map_baseChangeComposite`:
  **the stalk of the canonical base change map is a quasi-isomorphism.**

## Implementation notes

**The algebra structure on the flat factor, and why it has to be transported.**
`stalk_isLocalization_of_isPullback_inverseImage_comm` states the localization against the
*transported* `R`-algebra structure on `B`, namely the stalk map of `g` read through
`stalkInverseImageBaseRingIso` and `stalkInverseImageSheafIso`; nothing there chooses a comparison
of sheaves of rings, because a commutative square does not determine one.  The complexes whose
stalk is being computed, on the other hand, are built from the canonical comparison, so the
algebra structure they produce is the stalk of that comparison.  The two agree — that is exactly
`stalkFunctor_map_baseRingComparison` — but the tensor product `B ⊗_R A`, the flatness of `B` and
the localization statement all depend on the structure, so the agreement has to be transported
through them.  `exists_isLocalization_tensor_congr` does that by substituting an equality of the
two defining ring maps; stating it for the ring maps rather than for the algebra structures is
what makes `subst` applicable.

**The scalar towers.**  `Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase` states its
conclusion under a chain of `letI`s, so the hypothesis it produces has a `let`-expression as its
type and instance search does not see through it; the two towers are therefore introduced with an
explicit type ascription, and passed to `isQuasiIso_of_localization_data` by name rather than left
to instance search.

**`Algebra.TensorProduct.rightAlgebra`** is a local instance here as it is in
`StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget`: it is the `A`-algebra structure
on `B ⊗_R A` that makes the latter a target for base change of `NL_{A/R}`, and it is the one the
ring-level theorem is stated against.

## References

* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for the
  naive cotangent complex.
* [Stacks Project, Tag 00S4](https://stacks.math.columbia.edu/tag/00S4), the ring-level flat base
  change.
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

namespace Stacks.NaiveCotangentFlatBaseChangeStalk

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {X Y X' Y' : Scheme.{u}}

/-- **The stalk of the canonical base-ring comparison**, written as the composite of the three
stalk identifications with the stalk map of `g`.  This is
`AlgebraicGeometry.BaseChangeStalk.stalkFunctor_map_baseRingComparison` with the identification of
the stalk of `(f')^{-1}𝒪_{Y'}` moved to the other side. -/
theorem stalkFunctor_map_baseRingComparison_eq (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) (x' : X'.carrier) :
    (stalkInverseImageBaseRingIso f g' x').hom ≫
          eqToHom (congrArg Y.presheaf.stalk
            (congrArg (fun k : X' ⟶ Y => k.base x') w)) ≫
          g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
        (baseRingComparison f f' g' g w).hom := by
  refine Eq.trans (congrArg (fun t => (stalkInverseImageBaseRingIso f g' x').hom ≫ t)
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact (Iso.comp_inv_eq _).mpr
    ((Category.assoc _ _ _).trans
      (stalkFunctor_map_baseRingComparison f f' g' g w x').symm)

/-- The stalk at `x'` of the canonical base-ring comparison of a commutative square defines, up
to the four stalk identifications, the same `𝒪_{Y,y}`-algebra structure on `𝒪_{Y',y'}` as the
stalk map of `g`.  This is `stalkFunctor_map_baseRingComparison` read as an equality of algebra
structures. -/
theorem algebraStalk_baseRingComparison (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (x' : X'.carrier) :
    ((stalkInverseImageBaseRingIso f g' x').hom ≫
          eqToHom (congrArg Y.presheaf.stalk
            (congrArg (fun k : X' ⟶ Y => k.base x') w)) ≫
          g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv).hom.toAlgebra =
      algebraStalk (baseRingComparison f f' g' g w).hom x' :=
  congrArg (fun φ : CommRingCat.Hom
      ((inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).presheaf.stalk x')
      ((inverseImageSheaf f'.toLRSHom.toShHom).presheaf.stalk x') =>
    RingHom.toAlgebra (CommRingCat.Hom.hom φ))
    (stalkFunctor_map_baseRingComparison_eq f g f' g' w x')

/-- For a flat `g`, the `𝒪_{Y,y}`-algebra structure that the stalk of the canonical base-ring
comparison puts on the stalk of `(f')^{-1}𝒪_{Y'}` is flat: it is a composite of three
isomorphisms of rings with the stalk map of `g`, which is flat by Mathlib's
`AlgebraicGeometry.Flat.stalkMap`. -/
theorem flat_stalkInverseImage (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [AlgebraicGeometry.Flat g] (w : g' ≫ f = f' ≫ g) (x' : X'.carrier) :
    RingHom.Flat ((stalkInverseImageBaseRingIso f g' x').hom ≫
      eqToHom (congrArg Y.presheaf.stalk (congrArg (fun k : X' ⟶ Y => k.base x') w)) ≫
      g.stalkMap (f'.base x') ≫ (stalkInverseImageSheafIso f' x').inv).hom :=
  have iso : ∀ {P Q : CommRingCat.{u}} (e : P ⟶ Q) [IsIso e], RingHom.Flat e.hom := fun e =>
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e)
  (iso _).comp ((iso _).comp ((AlgebraicGeometry.Flat.stalkMap g (f'.base x')).comp (iso _)))

open Stacks.Sites.Conormal (stalkIsScalarTowerSquareBase stalkIsScalarTowerSquareTarget)

/-- **The ring-level flat base change, from the localization data in the shape a cartesian square
of schemes supplies it.** -/
theorem isQuasiIso_of_localization_data {R₀ A₀ B₀ C₀ : Type u} [CommRing R₀] [CommRing A₀]
    [CommRing B₀] [CommRing C₀] [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra A₀ C₀] [Algebra B₀ C₀]
    [Algebra R₀ C₀] [IsScalarTower R₀ A₀ C₀] [IsScalarTower R₀ B₀ C₀] [Module.Flat R₀ B₀]
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
  exact NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base M h

/-- **The localization data of a tensor product, transported along an equality of the ring map
that defines the algebra structure on the left factor.**  Both the tensor product and the
statement about it depend on that algebra structure, so the transport is a substitution. -/
theorem exists_isLocalization_tensor_congr {R₀ A₀ B₀ C₀ : Type u} [CommRing R₀] [CommRing A₀]
    [CommRing B₀] [CommRing C₀] [Algebra R₀ A₀] [Algebra A₀ C₀] [Algebra B₀ C₀]
    {φ₁ φ₂ : R₀ →+* B₀} (hφ : φ₁ = φ₂)
    (h : letI := φ₁.toAlgebra
      ∃ ψ : TensorProduct R₀ B₀ A₀ →+* C₀,
        ψ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap B₀ C₀ ∧
        ψ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap A₀ C₀ ∧
        ∃ M : Submonoid (TensorProduct R₀ B₀ A₀), letI := ψ.toAlgebra; IsLocalization M C₀) :
    letI := φ₂.toAlgebra
    ∃ ψ : TensorProduct R₀ B₀ A₀ →+* C₀,
      ψ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap B₀ C₀ ∧
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap A₀ C₀ ∧
      ∃ M : Submonoid (TensorProduct R₀ B₀ A₀), letI := ψ.toAlgebra; IsLocalization M C₀ := by
  subst hφ
  exact h

section Point

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The ring-level input of flat base change, at a point of a cartesian square with flat
base.** -/
theorem isQuasiIso_nlExtensionBaseChangeMap_stalk [AlgebraicGeometry.Flat g]
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
      (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')) := stalkIsScalarTowerSquareBase
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
        (baseRingComparison f f' g' g hsq.w).hom)) :=
    by rw [← stalkFunctor_map_baseRingComparison_eq f g f' g' hsq.w x']
       exact flat_stalkInverseImage f g f' g' hsq.w x'
  have : Module.Flat
      (ToType (TopCat.Presheaf.stalk
        (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x'))
      (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x')) := hflat
  obtain ⟨ψ, hL, hR, M, hM⟩ := exists_isLocalization_tensor_congr
    (R₀ := (ToType (TopCat.Presheaf.stalk
      (inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom).obj x')))
    (A₀ := (ToType (TopCat.Presheaf.stalk (inverseImageMiddleRing g'.toLRSHom.toShHom).obj x')))
    (B₀ := (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f'.toLRSHom.toShHom).obj x')))
    (C₀ := (ToType (TopCat.Presheaf.stalk X'.toRingedSpace.sheaf.obj x')))
    (congrArg CommRingCat.Hom.hom (stalkFunctor_map_baseRingComparison_eq f g f' g' hsq.w x'))
    (stalk_isLocalization_of_isPullback_inverseImage_comm f g g' f' hsq x')
  exact fun h => @isQuasiIso_of_localization_data _ _ _ _ _ _ _ _ _ _ _ _ _ towA towB _
    ψ hL hR M hM h

/-- **The stalk of the canonical base change map of a cartesian square with flat base is a
quasi-isomorphism.**  The map is the composite of the [Stacks, Tag 08TM] identification of
`(g')^*NL_{X/Y}` with a base change, the base-change map of the tower
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and the relative map of the tower through
`(f')^{-1}𝒪_{Y'}`; the first factor is an isomorphism, and the stalk of the other two is a
quasi-isomorphism by `Stacks.NaiveCotangentTowerStalk.quasiIso_stalkFunctor_map_towerComposite`
fed with the ring-level flat base change. -/
theorem quasiIso_stalkFunctor_map_baseChangeComposite [AlgebraicGeometry.Flat g]
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

/-- **The stalk of the canonical base change map of a cartesian square with flat base is a
quasi-isomorphism**, stated for the map
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison` itself rather than for the
three-factor composite it is defined to be.

This is `quasiIso_stalkFunctor_map_baseChangeComposite` with the composite folded back up.  The
folding is done by rewriting rather than by conversion, and the morphism the rewrite starts from
is left to be read off `quasiIso_stalkFunctor_map_baseChangeComposite` rather than written out
again: underneath the stalk functor and `QuasiIso`, two morphisms that differ by so much as one
unfolding are compared by descending through the mapped complex in every degree, which for a
composite this wide does not terminate.  What is left is the equality of the two morphisms
themselves, which is the definition of the map and holds by `rfl`. -/
theorem quasiIso_stalkFunctor_map_baseChangeMapOfComparison [AlgebraicGeometry.Flat g]
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

end Stacks.NaiveCotangentFlatBaseChangeStalk

end

end
