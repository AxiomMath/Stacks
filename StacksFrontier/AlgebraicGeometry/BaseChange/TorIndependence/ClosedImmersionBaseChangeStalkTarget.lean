module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkDiagram
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedStalkPushforwardLocalRing

/-!
# The target chain of the stalk diagram, below `DerivedCategory.Q`

For a morphism of schemes `g : Z' ⟶ Z`, a closed immersion `i' : Z' ⟶ X'` and a point `w` of `Z'`,
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkTargetIso` identifies the derived stalk
at `i' w` of `Ri'_*(Lg^* -)` with `(-)_{g w} ⊗ᴸ_{𝒪_{Z, g w}} 𝒪_{Z', w}` with scalars restricted
along the germ map of `i'`. This file computes its components at an arbitrary object, and at
`DerivedCategory.Q.obj P` composed with the comparison tail of Stacks 0661 for `g` at `w`.

## Main results

* `StacksDraft.DerivedStalkTargetChase.comp_id_comp₂` and
  `StacksDraft.DerivedStalkTargetChase.targetComponentChase`: two identities of composites in
  arbitrary categories.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkTargetIso_hom_app`: the component of
  the target chain at an object, as the composite of the components of its two nontrivial factors.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkTargetIso_hom_app_Q_comp_comparison`:
  the component of the target chain at a complex, followed by the comparison tail of Stacks 0661.

## Implementation notes

The equation of `derivedStalkTargetIso_hom_app_Q_comp_comparison` mixes
`AlgebraicGeometry.Scheme.Modules Z'` with
`CategoryTheory.SheafOfModules (structureSheafRing Z'.toRingedSpace)`, whose `Category` instances
are definitionally but not reducibly equal, so it is not type-correct at the transparency at which
`rw`, `simp` and `conv` check their motives. It is therefore obtained by `exact` from the abstract
identity `StacksDraft.DerivedStalkTargetChase.targetComponentChase`.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

namespace StacksDraft.DerivedStalkTargetChase

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- `f ≫ 𝟙 ≫ g ≫ 𝟙 = f ≫ g`. -/
theorem comp_id_comp₂ {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    f ≫ CategoryStruct.id b ≫ g ≫ CategoryStruct.id c = f ≫ g := by
  simp

/-- If `ψ = u ≫ F.map A`, `A ≫ B ≫ G = H ≫ E` and `u ≫ F.map H = x ≫ y`, then
`ψ ≫ F.map B ≫ F.map G = x ≫ y ≫ F.map E`. -/
theorem targetComponentChase (F : C ⥤ D) {m n₁ n₂ n₃ p : C}
    (A : m ⟶ n₁) (B : n₁ ⟶ n₂) (G : n₂ ⟶ n₃) (H : m ⟶ p) (E : p ⟶ n₃)
    {O₀ N : D} (ψ : O₀ ⟶ F.obj n₁) (u : O₀ ⟶ F.obj m) (x : O₀ ⟶ N) (y : N ⟶ F.obj p)
    (h₀ : ψ = u ≫ F.map A) (hc : A ≫ B ≫ G = H ≫ E) (hnat : u ≫ F.map H = x ≫ y) :
    ψ ≫ F.map B ≫ F.map G = x ≫ y ≫ F.map E := by
  rw [h₀, Category.assoc, ← F.map_comp, ← F.map_comp, hc, F.map_comp, ← Category.assoc, hnat,
    Category.assoc]

end StacksDraft.DerivedStalkTargetChase

universe u

namespace Stacks.Cohomology.ClosedImmersionBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {Z' X' Z : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z}
  [AlgebraicGeometry.IsClosedImmersion i']

/-- The component of `derivedStalkTargetIso` at an object, as the composite of the components
of its two nontrivial factors: the derived stalk of `Ri'_*` on the image, taken at the derived
pullback of the object, and restriction of scalars along the germ map of `i'` applied to the
derived stalk comparison for `g`. -/
theorem derivedStalkTargetIso_hom_app (w : Z')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    (derivedStalkTargetIso (i' := i') (g := g) w).hom.app K =
      (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i' w).hom.app
          ((derivedPullback g.toLRSHom.toShHom).obj K) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedPullbackStalkIso g w).hom.app K) :=
  (rfl : (derivedStalkTargetIso (i' := i') (g := g) w).hom.app K =
      _ ≫ CategoryStruct.id _ ≫ _ ≫ CategoryStruct.id _).trans
    (StacksDraft.DerivedStalkTargetChase.comp_id_comp₂ _ _)

/-- For a cochain complex `P` of `𝒪_Z`-modules, the component of `derivedStalkTargetIso` at
`DerivedCategory.Q.obj P` followed by the tail `Lh(−)_{g w}`-of-the-factorization and the
comparison `alphaH`, restricted along the germ map of `i'`, is the derived stalk at `i' w` of
`Ri'_*` of the canonical map `AlgebraicGeometry.pullbackComparisonOnComplex` from the derived
pullback of `P` to its degreewise pullback, followed by the derived stalk of `Ri'_*` on the image
at that degreewise pullback, followed by the factorization of the stalk functor at `w` and
`DerivedCategory.Q` of the degreewise stalk formula `Stacks.ModuleSkyscraper.pullbackStalkIso` for
the underived pullback. -/
theorem derivedStalkTargetIso_hom_app_Q_comp_comparison (w : Z')
    (P : CochainComplex Z.Modules ℤ) :
    (derivedStalkTargetIso (i' := i') (g := g) w).hom.app (DerivedCategory.Q.obj P) ≫
        (Lh (g := g) w ⋙ (ModuleCat.restrictScalars.{u, u, u}
            (i'.stalkMap w).hom).mapDerivedCategory).map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
            (g w)).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory.map
          ((alphaH (g := g) w).app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (derivedPushforward i'.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (AlgebraicGeometry.pullbackComparisonOnComplex g P) ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i' w).hom.app
          (DerivedCategory.Q.obj (((Scheme.Modules.pullback g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z'
                w).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso g w).symm
              (ComplexShape.up ℤ)).hom.app P)) := by
  have h₀ := derivedStalkTargetIso_hom_app (i' := i') (g := g) w (DerivedCategory.Q.obj P)
  have hc : (AlgebraicGeometry.derivedPullbackStalkIso g w).hom.app (DerivedCategory.Q.obj P) ≫
        (Lh (g := g) w).map ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
          (g w)).mapDerivedCategoryFactors.hom.app P) ≫
        (alphaH (g := g) w).app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
            (g w)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (AlgebraicGeometry.derivedStalkFunctor w).map
          (AlgebraicGeometry.pullbackComparisonOnComplex g P) ≫
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z'
              w).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (Stacks.ModuleSkyscraper.pullbackStalkIso g w).symm
            (ComplexShape.up ℤ)).hom.app P)) :=
    AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison g w P
  have hnat : (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing
          i' w).hom.app ((derivedPullback g.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P)) ≫
        (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.derivedStalkFunctor w).map
            (AlgebraicGeometry.pullbackComparisonOnComplex g P)) =
      (derivedPushforward i'.toLRSHom.toShHom ⋙
            AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (AlgebraicGeometry.pullbackComparisonOnComplex g P) ≫
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i' w).hom.app
          (DerivedCategory.Q.obj (((Scheme.Modules.pullback g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) :=
    ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i' w).hom.naturality
      (AlgebraicGeometry.pullbackComparisonOnComplex g P)).symm
  exact StacksDraft.DerivedStalkTargetChase.targetComponentChase
    (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory
    _ _ _ _ _ _ _ _ _ h₀ hc hnat

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
