module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral

/-!
# Naturality of the derived tensor-hom adjunction in the source

For a ringed space with structure sheaf `Rc`, the equivalence `derivedSheafHomTensorEquiv Rc A B Z`
between morphisms `A ⟶ RHom(B, Z)` and morphisms `A ⊗ᴸ B ⟶ Z` in the derived category is natural
in `A`.

## Main results

* `derivedSheafHomTensorEquiv_naturality_source`: precomposing with `u : A' ⟶ A` on the source
  corresponds to precomposing with `u ⊗ᴸ B`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

section Abstract

variable {C : Type*} [Category C] (F : C ⥤ C ⥤ C)

end Abstract

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The equivalence `derivedSheafHomTensorEquiv` is natural in the source: for `u : A' ⟶ A`, it
sends `u ≫ h` to `(u ⊗ᴸ B) ≫ derivedSheafHomTensorEquiv Rc A B Z h`. -/
theorem derivedSheafHomTensorEquiv_naturality_source
    {A A' : DerivedCategory (StructureSheafModules Rc)}
    (B Z : DerivedCategory (StructureSheafModules Rc))
    (u : A' ⟶ A) (h : A ⟶ ((derivedSheafHom Rc).obj (op B)).obj Z) :
    derivedSheafHomTensorEquiv Rc A' B Z (u ≫ h) =
      ((derivedTensor Rc).map u).app B ≫ derivedSheafHomTensorEquiv Rc A B Z h := by
  rw [derivedSheafHomTensorEquiv_eq Rc A' B Z, derivedSheafHomTensorEquiv_eq Rc A B Z,
    RingedSite.derivedCurryHomEquiv_naturality_source (ringedSite Rc) u h]

end Stacks.SheafOfModules

end
