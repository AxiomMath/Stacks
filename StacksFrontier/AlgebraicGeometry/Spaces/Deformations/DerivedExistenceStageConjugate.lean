module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceStageCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleUnderivedPullbackCompMates

/-!
# The two composition isomorphisms of the tower of Situation 0DIK are conjugate

In Situation [Stacks, Tag 0DIK], the composition isomorphism `Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` of derived
pullbacks (Stacks 0D6D) is conjugate, along `Ljₙ^* ⊣ Rjₙ,*` and the composite adjunction
`Ljₙ₊₁^* ⋙ Liₙ^* ⊣ Riₙ,* ⋙ Rjₙ₊₁,*`, to the composition isomorphism `Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*` of
the exact direct images from which the tower `Rjₙ,* Kₙ` of [Stacks, Tag 0DIL] is built. This file
develops inputs of that comparison: the unit property of the composition isomorphism of exact
direct images, and the counit compatibility of the exact adjunctions `Liₙ^* ⊣ Riₙ,*`.

## Main results

* `AlgebraicGeometry.Space.compUnit_comp_mapDerivedCategoryCompNatIso_hom_app_sheafOfModules`:
  the unit property of `RingTheory.TorIndependence.mapDerivedCategoryCompNatIso` for categories
  of sheaves of modules, with the preadditive structure that instance synthesis finds.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.transitionAdjunction_counit_fac`: the
  counit of
  `Liₙ^* ⊣ Riₙ,*` is induced by the degreewise counit.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u w

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

section ExactComposition

/-- `compUnit_comp_mapDerivedCategoryCompNatIso_hom_app` for categories of sheaves of modules,
stated with their own preadditive structure on the homotopy categories (the one instance
synthesis finds) rather than the one carried by the abelian structure. At concrete sites the two
are identified once, here, at abstract ones. -/
theorem compUnit_comp_mapDerivedCategoryCompNatIso_hom_app_sheafOfModules
    {C₁ : Type*} [Category* C₁] {J₁ : GrothendieckTopology C₁} {R₁ : Sheaf J₁ RingCat.{w}}
    [HasSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {C₂ : Type*} [Category* C₂] {J₂ : GrothendieckTopology C₂} {R₂ : Sheaf J₂ RingCat.{w}}
    [HasSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {C₃ : Type*} [Category* C₃] {J₃ : GrothendieckTopology C₃} {R₃ : Sheaf J₃ RingCat.{w}}
    [HasSheafify J₃ AddCommGrpCat.{w}] [J₃.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory (SheafOfModules.{w} R₁)] [HasDerivedCategory (SheafOfModules.{w} R₂)]
    [HasDerivedCategory (SheafOfModules.{w} R₃)]
    {F : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂}
    {G : SheafOfModules.{w} R₂ ⥤ SheafOfModules.{w} R₃}
    {H : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₃}
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H)
    (K : HomotopyCategory (SheafOfModules.{w} R₁) (ComplexShape.up ℤ)) :
    (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app K) ≫
        G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app K)) ≫
      (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom.app
        (DerivedCategory.Qh.obj K) =
      H.mapDerivedCategoryFactorsh.inv.app K :=
  compUnit_comp_mapDerivedCategoryCompNatIso_hom_app e K

end ExactComposition


namespace SeparatedDerivedExistenceSystem

open Stacks.Cohomology.DerivedPushforward (pullbackMapHomotopy pushforwardMapHomotopy
  pullbackAdjPushforwardMapHomotopy)

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- The counit of `Liₙ^* ⊣ Riₙ,*` (exact form) is induced by the degreewise counit. -/
theorem transitionAdjunction_counit_fac (n : ℕ)
    (K : HomotopyCategory (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) :
    (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
        ((D.transitionPushforwardFactorsh n).inv.app K) ≫
      (D.transitionAdjunction n).counit.app ((D.stageQh n).obj K) =
      (smallEtaleDerivedModulePullbackComparison D.B (limitBase D.system) D.containsLimitBase
          (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).app
          ((pushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom D.B
            (limitBase D.system) D.containsLimitBase
            (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))).obj K) ≫
        (D.stageQh n).map ((pullbackAdjPushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
            (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))).counit.app
              K) :=
  counit_ofNatIsoRight_fac _
    (transitionToposDerivedAdjunction D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.transitionToposDerivedPushforwardIso n)
    (rightDerivedIsoOfFactors_hom_app (D.stageQh n)
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) _ _
      (D.transitionToposUnit n) (D.transitionPushforwardFactorsh n))
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_counit_fac.{u, u + 1, u, u,
        u + 1, u}
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))) K

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
