module

public import StacksFrontier.Deformation.ToposThickening.DerivedIdealTensorComparison
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorExtensionOfScalars

/-!
# The ideal part of a derived base change is the derived tensor product with the ideal

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site and let `I₀` be a
sheaf of `O₀`-modules, with `I = I₀|_O` its restriction. This file identifies

`((- ⊗^L_O O₀) ⊗^L_{O₀} I₀)|_O ≅ - ⊗^L_O I`

as functors on the derived category of `O`-modules. This is the second of the two comparisons a
`Deformation.ComplexLift.DerivedReduction` needs: it identifies the first vertex of the
reduction triangle with the ideal part of a derived base change.

Unlike the first comparison
(`Deformation.ComplexLift.derivedRestrictExtensionIso`), this one is not uniqueness of left
derived functors applied to an isomorphism of the functors being derived: the left-hand side
derives `K ↦ ((O₀ ⊗_O K) ⊗^L_{O₀} I₀)|_O`, with the *derived* tensor product with `I₀` inside,
and that functor is isomorphic to the degreewise `K ↦ K ⊗_O I` only on the `P`-cellular
complexes. So the comparison is exhibited as a left derived functor by the converse criterion
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions` at the
`P`-cellular objects, `P` being the flat sheaves of modules.

## Main definitions

* `Deformation.ComplexLift.idealTensorCounitHomotopy`: the comparison of the composite with the
  degreewise tensor product with `I`, a three-step composite.
* `Deformation.ComplexLift.derivedIdealTensorIso`: **the identification**, for the derived base
  change constructed by Stacks 0794.
* `Deformation.ComplexLift.derivedIdealTensorIsoOf`: the same for an arbitrary derived base
  change along `f`, which is the form a `Deformation.ComplexLift.DerivedReduction` consumes.

## Main results

* `Deformation.ComplexLift.isIso_derivedExtensionOfScalarsCounitHomotopy_app`: the comparison of
  derived base change with degreewise extension of scalars is invertible on the `P`-cellular
  objects.
* `Deformation.ComplexLift.isIso_idealTensorCounitHomotopy_app`: so is the three-step
  comparison, which is where
  `Deformation.ComplexLift.isIso_derivedTensorRightCounitHomotopy_app_extensionOfScalars`
  enters.
* `Deformation.ComplexLift.isLeftDerivedFunctor_idealTensorCounitHomotopy`: hence the composite
  is the total left derived functor of the degreewise tensor product with `I`.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory
open StacksDraft.UnboundedLeftDerivedFunctor

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-! ### The comparison of derived base change is invertible on the cellular objects -/

/-- **Extension of scalars inverts a quasi-isomorphism between `P`-cellular objects of
`K(Mod(O))`**, `P` being the flat sheaves of modules: Stacks 0794 for
`Deformation.ComplexLift.extensionOfScalars`. -/
theorem isIso_map_extensionOfScalarsHomotopy_of_cellular
    {A B : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)}
    (s : A ⟶ B)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) s)
    (hA : cellular (flatObjects O) A) (hB : cellular (flatObjects O) B) :
    IsIso ((extensionOfScalarsHomotopy.{d₀} f).map s) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  have hder := derives_cellularLocalizerMorphism (extensionOfScalars f) (flatObjects O)
    (flatObjects_biprod O) (flatObjects_cover O) (acyclic_map_extensionOfScalars f)
  exact hder (ObjectProperty.homMk (P := cellular (flatObjects O))
    (X := ⟨_, hA⟩) (Y := ⟨_, hB⟩) s) hs

/-- **The comparison of derived base change with degreewise extension of scalars is invertible
on the `P`-cellular objects**: the `P`-cellular objects resolve `K(Mod(O))` and extension of
scalars inverts the quasi-isomorphisms between them. -/
theorem isIso_derivedExtensionOfScalarsCounitHomotopy_app
    (X : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ))
    (hX : cellular (flatObjects O) X) :
    IsIso ((derivedExtensionOfScalarsCounitHomotopy.{d, d₀} f).app X) :=
  CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))
    (cellular (flatObjects O)) (exists_cellular_quasiIso O) (extensionOfScalarsHomotopy.{d₀} f)
    (fun s hs hA hB ↦ isIso_map_extensionOfScalarsHomotopy_of_cellular f s hs hA hB)
    DerivedCategory.Qh (derivedExtensionOfScalars.{d, d₀} f)
    (derivedExtensionOfScalarsCounitHomotopy f) X hX

/-! ### The three-step comparison -/

variable (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-- **The comparison of the ideal part of a derived base change with the degreewise tensor
product with `I`.** It is the composite of three steps: the comparison of derived base change
with degreewise extension of scalars, the comparison of the derived tensor product with `I₀`
with the degreewise one, and the projection formula
`Deformation.ComplexLift.idealTensorComplexLeg`. -/
def idealTensorCounitHomotopy :
    DerivedCategory.Qh ⋙ (derivedExtensionOfScalars.{d, d₀} f ⋙
        derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) ⟶
      tensorRightHomotopy.{d} (restrictIdeal f I₀) :=
  ((Functor.associator DerivedCategory.Qh (derivedExtensionOfScalars.{d, d₀} f)
        (derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f)).inv ≫
      Functor.whiskerRight (derivedExtensionOfScalarsCounitHomotopy f)
        (derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f)) ≫
    Functor.whiskerLeft ((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.whiskerRight (derivedTensorRightCounitHomotopy.{d₀} I₀)
        (restrictionOnDerived.{d, d₀} f)) ≫
    (idealTensorComplexLeg.{d, d₀} f I₀).hom

/-- **The three-step comparison is invertible on the `P`-cellular objects.** The first step is
invertible there because derived base change is derived by flat resolutions; the second is
`Deformation.ComplexLift.isIso_derivedTensorRightCounitHomotopy_app_extensionOfScalars`, the
extension of scalars of a `P`-cellular object being a complex at which the degreewise tensor
product with `I₀` computes the derived one; the third is an isomorphism everywhere. -/
theorem isIso_idealTensorCounitHomotopy_app
    (X : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ))
    (hX : cellular (flatObjects O) X) :
    IsIso ((idealTensorCounitHomotopy.{d, d₀} f I₀).app X) := by
  have h₁ : IsIso ((derivedExtensionOfScalarsCounitHomotopy.{d, d₀} f).app X) :=
    isIso_derivedExtensionOfScalarsCounitHomotopy_app f X hX
  have h₂ : IsIso ((derivedTensorRightCounitHomotopy.{d₀} I₀).app
      (((extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
    isIso_derivedTensorRightCounitHomotopy_app_extensionOfScalars f I₀ X hX
  dsimp only [idealTensorCounitHomotopy, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app]
  infer_instance

/-- **The ideal part of a derived base change is the total left derived functor of the
degreewise tensor product with `I`.** The degreewise tensor product with `I` inverts the
quasi-isomorphisms between `P`-cellular objects of `K(Mod(O))` and those resolve every object,
so the converse criterion applies to the three-step comparison. -/
instance isLeftDerivedFunctor_idealTensorCounitHomotopy :
    (derivedExtensionOfScalars.{d, d₀} f ⋙ derivedTensorRight.{d₀} I₀ ⋙
        restrictionOnDerived.{d, d₀} f).IsLeftDerivedFunctor
      (idealTensorCounitHomotopy.{d, d₀} f I₀)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) :=
  CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))
    (cellular (flatObjects O)) (exists_cellular_quasiIso O)
    (tensorRightHomotopy.{d} (restrictIdeal f I₀))
    (fun s hs hA hB ↦
      isIso_map_tensorRightHomotopy_of_cellular O (restrictIdeal f I₀) s hs hA hB)
    DerivedCategory.Qh _ (idealTensorCounitHomotopy.{d, d₀} f I₀)
    (fun X hX ↦ isIso_idealTensorCounitHomotopy_app f I₀ X hX)

/-! ### The identification -/

/-- **The ideal part of a derived base change is the derived tensor product with the ideal.**
The isomorphism of functors `D(O) ⥤ D(O)`

`((- ⊗^L_O O₀) ⊗^L_{O₀} I₀)|_O ≅ - ⊗^L_O I`

for the derived base change constructed by Stacks 0794. Both sides are total left derived
functors of the degreewise tensor product with `I` along `Qh`, so this is uniqueness of left
derived functors. -/
def derivedIdealTensorIso :
    derivedExtensionOfScalars.{d, d₀} f ⋙ derivedTensorRight.{d₀} I₀ ⋙
        restrictionOnDerived.{d, d₀} f ≅
      derivedTensorRight.{d} (restrictIdeal f I₀) :=
  Functor.leftDerivedUnique _ _ (idealTensorCounitHomotopy.{d, d₀} f I₀)
    (derivedTensorRightCounitHomotopy.{d} (restrictIdeal f I₀))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- **The same identification for an arbitrary derived base change along `f`.** Any two derived
base changes along `f` are canonically isomorphic, so the identification above transports to the
one chosen in the statements of Tags 0DIY and 0DIZ. -/
def derivedIdealTensorIsoOf (T : DerivedExtensionOfScalars.{d, d₀} f) :
    T.baseChange ⋙ derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f ≅
      derivedTensorRight.{d} (restrictIdeal f I₀) :=
  Functor.isoWhiskerRight
      (DerivedExtensionOfScalars.baseChangeIso T (derivedExtensionOfScalarsData.{d, d₀} f))
      (derivedTensorRight.{d₀} I₀ ⋙ restrictionOnDerived.{d, d₀} f) ≪≫
    derivedIdealTensorIso.{d, d₀} f I₀

end Deformation.ComplexLift

end
