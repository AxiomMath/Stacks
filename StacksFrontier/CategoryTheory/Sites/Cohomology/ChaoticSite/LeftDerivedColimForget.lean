module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules

/-!
# Derived colimits with linear coefficients, read on underlying abelian groups

Let `C` be a small category carrying the chaotic topology, let `B` be a ring and let `U_•` be a
cosimplicial object of `C` which is a point resolution, so that both `L_n colim` on diagrams of
`B`-modules over `Cᵒᵖ` and `L_n colim` on abelian presheaves are computed by the homology of the
Moore complex of `ℱ(U_•)` — the module half of Tag 08Q9, and Tag 08Q9 itself. The forgetful
functor `Mod(B) ⥤ Ab` is additive and preserves homology, so it carries the one Moore complex to
the other and commutes with taking homology. Therefore

`L_n colim` at module coefficients, followed by the forgetful functor, *is* `L_n colim` at
abelian-group coefficients applied to the underlying diagram of abelian groups.

Since the forgetful functor is moreover faithful, a morphism of diagrams of `B`-modules which
induces the zero map on `L_n colim` of the underlying abelian presheaves already induces the
zero map on `L_n colim` of the diagrams of `B`-modules. This is the form in which the comparison
is used: vanishing of a map on derived colimits is checked at abelian coefficients.

## Main definitions

* `Stacks.ChaoticSite.mooreComplexForgetNatIso`: the Moore complex of `ℱ(U_•)` read in abelian
  groups is the Moore complex of the underlying abelian presheaf, naturally in `ℱ`.
* `Stacks.ChaoticSite.forgetModulesHomologyFunctorIso`: the forgetful functor `Mod(B) ⥤ Ab`
  commutes with the degree-`n` homology of a chain complex.
* `Stacks.ChaoticSite.leftDerivedColimForgetIso`: **`L_n colim` at module coefficients, forgotten
  to abelian groups, is `L_n colim` at abelian-group coefficients.**

## Main results

* `Stacks.ChaoticSite.leftDerivedColim_map_eq_zero_of_forget`: a morphism of diagrams of
  `B`-modules induces the zero map on `L_n colim` as soon as it does so on underlying abelian
  groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.ChaoticSite

universe u

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)

/-- **The Moore complex of `ℱ(U_•)` commutes with the forgetful functor `Mod(B) ⥤ Ab`**, both
read as functors of the diagram of `B`-modules `ℱ`: applying the forgetful functor degreewise to
the Moore complex of `ℱ(U_•)` gives the Moore complex of the underlying abelian presheaf
evaluated on `U_•`. The forgetful functor is additive, so it commutes with forming the
alternating sum of the faces. -/
def mooreComplexForgetNatIso :
    ModuleValued.moduleCosimplicialMooreComplex U ⋙
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.down ℕ) ≅
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj
          (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) ⋙ cosimplicialMooreComplex U :=
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat.{u} B)).obj U.op)
    (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}))

/-- **The forgetful functor `Mod(B) ⥤ Ab` commutes with homology**: it is additive and preserves
homology, so the degree-`n` homology of the complex of underlying abelian groups is the
underlying abelian group of the degree-`n` homology. -/
def forgetModulesHomologyFunctorIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n ⋙
        forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n)
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}))

/-- **`L_n colim` at module coefficients, forgotten to abelian groups, is `L_n colim` at
abelian-group coefficients.** Both sides are the degree-`n` homology of the Moore complex of
`ℱ(U_•)` — the module half of Tag 08Q9 and Tag 08Q9 — and the forgetful functor `Mod(B) ⥤ Ab`
carries the one Moore complex to the other and commutes with homology. -/
def leftDerivedColimForgetIso (hU : IsPointResolution U) (n : ℕ) :
    (colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived n ⋙
        forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ≅
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj
          (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) ⋙
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n :=
  Functor.isoWhiskerRight (ModuleValued.moduleLeftDerivedColimitNatIso U hU n)
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) ≪≫
    Functor.isoWhiskerLeft (ModuleValued.moduleCosimplicialMooreComplex U)
      (forgetModulesHomologyFunctorIso (B := B) n).symm ≪≫
    Functor.isoWhiskerRight (mooreComplexForgetNatIso U)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n) ≪≫
    Functor.isoWhiskerLeft
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}))
      (leftDerivedColimitNatIso U hU n).symm

/-- **Vanishing on `L_n colim` at module coefficients is detected on underlying abelian groups.**
The forgetful functor `Mod(B) ⥤ Ab` is faithful and additive, so a morphism of `B`-modules is
zero as soon as the underlying map of abelian groups is; and under
`Stacks.ChaoticSite.leftDerivedColimForgetIso` that underlying map is the map induced on
`L_n colim` by the morphism of underlying abelian presheaves. -/
theorem leftDerivedColim_map_eq_zero_of_forget (hU : IsPointResolution U) (n : ℕ)
    {F G : Cᵒᵖ ⥤ ModuleCat.{u} B} (a : F ⟶ G)
    (h : ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map
        (Functor.whiskerRight a (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})) = 0) :
    ((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived n).map a = 0 := by
  refine (Functor.map_eq_zero_iff (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).mp ?_
  rw [← cancel_mono ((leftDerivedColimForgetIso U hU n).hom.app G), zero_comp]
  refine ((leftDerivedColimForgetIso U hU n).hom.naturality a).trans ?_
  simp only [Functor.comp_map, Functor.whiskeringRight_obj_map, h, comp_zero]

end Stacks.ChaoticSite

end
