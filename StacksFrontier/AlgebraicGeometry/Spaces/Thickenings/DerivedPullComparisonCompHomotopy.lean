module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso

/-!
# The composition comparison of derived pullbacks against the comparisons with degreewise pullback

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the composition comparison
`L(Y ⟶ Z)^* ⋙ L(X ⟶ Y)^* ⟶ L(X ⟶ Z)^*` of the derived pullback datum
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, followed by the comparison of the derived
pullback along the composite with degreewise pullback, is computed on the homotopy category, in the
spelling of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_inv_app_comp_α`: the composition
  comparison followed by the comparison along the composite, on the homotopy category.
* `AlgebraicGeometry.Space.derivedPullComparison_app`: the comparison of the derived pullback with
  degreewise pullback at a complex, written out.
* `AlgebraicGeometry.Space.comp_chain_triangle`: the abstract shape of the computation.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

namespace AlgebraicGeometry.Space

/-- The abstract shape of the computation of the composition comparison of derived pullbacks
on complexes: given the three commuting relations `n₁`, `h₁`, `h₃` and `b₃ ≫ b₄ = 𝟙 G₂`, the
composite `t₀ ≫ a₁ ≫ a₂ ≫ a₃` is `F.map (b₁ ≫ b₂ ≫ b₃) ≫ (F.map b₄ ≫ b₅ ≫ b₆) ≫ b₇`. -/
theorem comp_chain_triangle {D D' : Type*} [Category D] [Category D'] (F : D' ⥤ D)
    {A₁ A₂ A₃ A₄ C₅ C₆ : D} {G₀ G₁ G₂ G₃ : D'}
    (t₀ : F.obj G₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃) (a₃ : A₃ ⟶ A₄)
    (b₁ : G₀ ⟶ G₁) (b₂ : G₁ ⟶ G₂) (b₃ : G₂ ⟶ G₃) (b₄ : G₃ ⟶ G₂)
    (b₅ : F.obj G₂ ⟶ C₅) (b₆ : C₅ ⟶ C₆) (b₇ : C₆ ⟶ A₄) (t₁ : F.obj G₁ ⟶ A₂) (e : C₅ ⟶ A₃)
    (n₁ : F.map b₁ ≫ t₁ = t₀ ≫ a₁) (h₁ : t₁ ≫ a₂ = F.map b₂ ≫ b₅ ≫ e)
    (h₃₄ : b₃ ≫ b₄ = 𝟙 G₂) (h₃ : e ≫ a₃ = b₆ ≫ b₇) :
    t₀ ≫ a₁ ≫ a₂ ≫ a₃ = F.map (b₁ ≫ b₂ ≫ b₃) ≫ (F.map b₄ ≫ b₅ ≫ b₆) ≫ b₇ := by
  rw [← reassoc_of% n₁, reassoc_of% h₁]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc b₃ b₄, h₃₄, CategoryTheory.Functor.map_id, Category.id_comp, h₃]

section DerivedPull

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The comparison of the derived pullback with degreewise pullback, at a complex, written out. -/
theorem derivedPullComparison_app (h : X ⟶ Y)
    (M : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    (derivedPullComparison B S hS h).app M =
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) h).map
          ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS Y.1 Y.2)).inv.app M) ≫
        ((derivedModulePullbackLeftDerived B S hS).α h).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ≫
        (quotientCompModulePullbackIso B S hS h).hom.app M :=
  rfl

/-- The comparison of the derived pullback datum at a composite, on the homotopy category, in
the spelling of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`. -/
theorem smallEtaleDerivedPullbackData_compIso_inv_app_comp_α (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : HomotopyCategory (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app
          (((derivedModulePullbackLeftDerived B S hS).Q Z).obj M) ≫
        ((derivedModulePullbackLeftDerived B S hS).α (f ≫ g)).app M =
      ((derivedModulePullbackLeftDerived B S hS).L f).map
          (((derivedModulePullbackLeftDerived B S hS).α g).app M) ≫
        ((derivedModulePullbackLeftDerived B S hS).α f).app
          (((modulePullbackDataTopos B S hS).mapHomotopyCategory.pull g).obj M) ≫
        ((derivedModulePullbackLeftDerived B S hS).Q X).map
          ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
            (ComplexShape.up ℤ)).hom.app M) := by
  rw [smallEtaleDerivedPullbackData_compIso_eq, Iso.symm_inv]
  exact smallEtaleDerivedModulePullbackCompIso_hom_app_comp_comparison B S hS f g M

end DerivedPull

end AlgebraicGeometry.Space

end
