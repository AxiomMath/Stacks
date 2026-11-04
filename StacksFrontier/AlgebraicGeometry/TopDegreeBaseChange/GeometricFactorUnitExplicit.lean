module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineUnitTensorCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorUnitorSpellings

/-!
# The Eilenberg-Watts module of (b) and its unit, written out

The functor `Φ : M ↦ H^d(X', F ⊗ (f')^* M~)` of [Stacks, Tag 0EX3] (b) over an affine base, and
the identification `Φ(R) ≅ H^d(X', F)` of its Eilenberg-Watts module, are built from four named
factors. **This file writes both out in the explicit spelling** — the tensor product sheaf of
[Stacks, Tag 01CA], the pullback of module sheaves, and Mathlib's `AlgebraicGeometry.tilde` — in
which the geometric half of conclusion (c) is stated.

Both statements are about a *variable* scheme over a *variable* affine base. That is the point: a
consumer instantiates them at the situation restricted to an affine open of its base, and the one
identification of that restricted situation's structure morphism with `f' ∣_ V` is then performed
once, at the instantiation, rather than inside a composite large enough that the unifier does not
finish.

## Main results

* `…TopDegreeBaseChange.affineTopDegreeFunctor_map_eq`: the functor of conclusion (b) on
  morphisms, written out.
* `…TopDegreeBaseChange.geometricFactorFormulaObjSelfIso_inv_eq` and
  `…TopDegreeBaseChange.geometricFactorFormulaObjSelfIso_inv_eq'`: the identification of the value
  of the geometric factor at the base ring with the coefficient sheaf, inverted and written out —
  at the named factors and at the explicit spelling.
* `…TopDegreeBaseChange.affineTopDegreeFunctorObjSelfIso_inv_eq`: the identification of the
  Eilenberg-Watts module of conclusion (b) with `H^d(X', F)`, inverted, as the cohomological tail
  applied to the unit of the geometric factor.

## Implementation notes

The third is definitional; the second is definitional up to the one place where this directory
uses two spellings of the right unitor of [Stacks, Tag 01CA], and there
`…TopDegreeBaseChange.tensorFactorObjUnitIso_hom_eq` identifies them. The first, and the two
factors of the second, cost one further step: the named tensor factor is the fixed-factor
`Stacks.SheafOfModules.Tensor.sheafTensor` and the explicit spelling is its uncurried form, and
the identity in the other variable is cancelled by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`.

*No `@[stacks 0EX3]` attribute is placed.* These are restatements of the definitions of the
functor of conclusion (b) and of its unit, not conclusions of the tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable (R : Type u) [CommRing R] (Z : Over (Spec (CommRingCat.of R)))

/-- The tensor factor on a morphism is the uncurried tensor product sheaf at the identity in the
first variable. -/
private theorem tensorFactor_map_eq_uncurry_map
    (F : _root_.SheafOfModules.{u} Z.left.ringCatSheaf) {A B : Z.left.Modules} (g : A ⟶ B) :
    (tensorFactor R Z F).map g =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩)).map (𝟙 F ×ₘ g) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩ (𝟙 F) g).symm

/-- **The functor `Φ` of [Stacks, Tag 0EX3] (b) on morphisms, written out.** It carries a map `g`
of modules over the base ring to the degree-`d` cohomology of `𝟙_F` tensored with the pullback
along the structure morphism of the tilde of `g`. -/
theorem affineTopDegreeFunctor_map_eq (d : ℕ)
    (F : (_root_.SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).FullSubcategory)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (affineTopDegreeFunctor R Z d (geometricFactor R Z F)).map g =
      (ModuleCat.restrictScalars (algebraMap R Γ(Z.left, ⊤))).map
        (((moduleGlobalSections Z.left).rightDerived d).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩)).map
            (𝟙 F.obj ×ₘ (Scheme.Modules.pullback Z.hom).map
              ((AlgebraicGeometry.tilde.functor (CommRingCat.of R)).map g)))) :=
  congrArg (fun z => (ModuleCat.restrictScalars (algebraMap R Γ(Z.left, ⊤))).map
      (((moduleGlobalSections Z.left).rightDerived d).map z))
    (tensorFactor_map_eq_uncurry_map R Z F.obj _)

/-- **The unit of the geometric factor of [Stacks, Tag 0EX3] (b), inverted and written out.** The
identification `F ⊗ (f')^* R~ ≅ F` of the value of the geometric factor at the base ring with the
coefficient sheaf is, inverted, the inverse of the right unitor of [Stacks, Tag 01CA] followed by
tensoring in the inverse of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` and then the
pullback of the inverse of `AlgebraicGeometry.tildeSelf`. -/
theorem geometricFactorFormulaObjSelfIso_inv_eq
    (F : _root_.SheafOfModules.{u} Z.left.ringCatSheaf) :
    (geometricFactorFormulaObjSelfIso R Z F).inv =
      (tensorSheafUnitRightIso Z.left.toRingedSpace F).inv ≫
        (tensorFactor R Z F).map (pullbackFactorObjUnitIso R Z).inv ≫
        (tensorFactor R Z F).map ((pullbackFactor R Z).map (tildeFactorObjSelfIso R).inv) := by
  have hdef : (geometricFactorFormulaObjSelfIso R Z F).inv =
      ((tensorFactorObjUnitIso R Z F).inv ≫
          (tensorFactor R Z F).map (pullbackFactorObjUnitIso R Z).inv) ≫
        (tensorFactor R Z F).map ((pullbackFactor R Z).map (tildeFactorObjSelfIso R).inv) := rfl
  rw [← congrArg Iso.inv (Iso.ext (tensorFactorObjUnitIso_hom_eq R Z F))]
  exact hdef.trans (Category.assoc _ _ _)

/-- **The two factors of the unit of the geometric factor, at the explicit spelling.** The
pullback factor is the pullback along the structure morphism, and the tensor factor is the
uncurried tensor product sheaf of [Stacks, Tag 01CA] at the identity in the first variable. The
pullback factor is definitional; the tensor factor is
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`. -/
theorem tensorFactor_map_pullbackFactorObjUnitIso_inv_eq
    (F : _root_.SheafOfModules.{u} Z.left.ringCatSheaf) :
    (tensorFactor R Z F).map (pullbackFactorObjUnitIso R Z).inv =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩)).map
        (𝟙 F ×ₘ (Scheme.Modules.pullbackUnitIso Z.hom).inv) :=
  tensorFactor_map_eq_uncurry_map R Z F _

/-- **The outer factor of the unit of the geometric factor, at the explicit spelling.** -/
theorem tensorFactor_map_pullbackFactor_map_tildeFactorObjSelfIso_inv_eq
    (F : _root_.SheafOfModules.{u} Z.left.ringCatSheaf) :
    (tensorFactor R Z F).map ((pullbackFactor R Z).map (tildeFactorObjSelfIso R).inv) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩)).map
        (𝟙 F ×ₘ (Scheme.Modules.pullback Z.hom).map
          (AlgebraicGeometry.tildeSelf (R := CommRingCat.of R)).inv) :=
  tensorFactor_map_eq_uncurry_map R Z F _

/-- **The unit of the geometric factor of [Stacks, Tag 0EX3] (b), inverted, at the explicit
spelling**: the inverse of the right unitor of [Stacks, Tag 01CA], then tensoring in the inverse
of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, then the pullback of the inverse of
`AlgebraicGeometry.tildeSelf`. This is the shape the geometric half of conclusion (c) is stated
at. -/
theorem geometricFactorFormulaObjSelfIso_inv_eq'
    (F : _root_.SheafOfModules.{u} Z.left.ringCatSheaf) :
    (geometricFactorFormulaObjSelfIso R Z F).inv =
      (tensorSheafUnitRightIso Z.left.toRingedSpace F).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩)).map
          (𝟙 F ×ₘ (Scheme.Modules.pullbackUnitIso Z.hom).inv) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Z.left.toRingedSpace.presheaf, Z.left.toRingedSpace.IsSheaf⟩)).map
          (𝟙 F ×ₘ (Scheme.Modules.pullback Z.hom).map
            (AlgebraicGeometry.tildeSelf (R := CommRingCat.of R)).inv) :=
  (geometricFactorFormulaObjSelfIso_inv_eq R Z F).trans
    (congrArg (fun z => (tensorSheafUnitRightIso Z.left.toRingedSpace F).inv ≫ z)
      (congrArg₂ (fun x y => x ≫ y)
        (tensorFactor_map_pullbackFactorObjUnitIso_inv_eq R Z F)
        (tensorFactor_map_pullbackFactor_map_tildeFactorObjSelfIso_inv_eq R Z F)))

/-- **The Eilenberg-Watts module of [Stacks, Tag 0EX3] (b) is `H^d(X', F)`, with the
identification inverted and written out**: the cohomological tail of the functor of conclusion (b)
applied to the inverse of the unit of its geometric factor. -/
theorem affineTopDegreeFunctorObjSelfIso_inv_eq (d : ℕ)
    (F : (_root_.SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).FullSubcategory) :
    (affineTopDegreeFunctorObjSelfIso R Z d F).inv =
      (ModuleCat.restrictScalars (algebraMap R Γ(Z.left, ⊤))).map
        (((moduleGlobalSections Z.left).rightDerived d).map
          (geometricFactorFormulaObjSelfIso R Z F.obj).inv) := rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
