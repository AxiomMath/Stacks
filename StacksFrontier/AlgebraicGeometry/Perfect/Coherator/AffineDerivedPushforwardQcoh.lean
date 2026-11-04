module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffinePushforwardExact
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage

/-!
# Derived pushforward along an affine morphism on the quasi-coherent derived category

Let `f : X ⟶ Y` be an affine morphism of schemes. The unbounded derived direct image carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`, so it restricts to a functor between the two subcategories of
complexes with quasi-coherent cohomology.

The statement is made for an arbitrary model `(RF, α)` of the right derived functor of
degreewise pushforward rather than for one fixed construction: any two models are canonically
isomorphic by `CategoryTheory.Functor.rightDerivedUnique`, and the condition on cohomology
sheaves is invariant under isomorphism because quasi-coherent modules form a weak Serre
subcategory.

## Main definitions

* `AlgebraicGeometry.affineRightDerivedPushforward`: the restriction of a model of the derived
  direct image to the complexes with quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.affineRightDerivedPushforward_mem`: the derived direct image of a complex
  with quasi-coherent cohomology has quasi-coherent cohomology.

## References

* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 08D7.** The derived direct image along an affine morphism of schemes
takes a complex of `𝒪_X`-modules with quasi-coherent cohomology to a complex of `𝒪_Y`-modules
with quasi-coherent cohomology. -/
@[stacks 08D7 "quasi-coherent cohomology of derived pushforward"]
public theorem affineRightDerivedPushforward_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (E : QuasicoherentDerivedCategory X) :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) (RF.obj E.obj) := by
  have : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Y)
  let RF₀ : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
    RingedSpace.derivedPushforward f.toLRSHom.toShHom
  let β : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF₀ :=
    RingedSpace.derivedPushforwardUnit f.toLRSHom.toShHom
  have hRD : RF₀.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    RingedSpace.derivedPushforward_isRightDerivedFunctor f.toLRSHom.toShHom
  exact (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).prop_of_iso
      ((Functor.rightDerivedUnique RF RF₀ α β
        (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))).symm.app E.obj)
      (isQuasicoherent_derivedPushforward f E)

/-- The restriction of a model of the derived direct image along an affine morphism to the
complexes with quasi-coherent cohomology, as a functor
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. -/
public noncomputable def affineRightDerivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    QuasicoherentDerivedCategory X ⥤ QuasicoherentDerivedCategory Y :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).lift
    ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RF)
    (affineRightDerivedPushforward_mem f RF α)

end AlgebraicGeometry

end
