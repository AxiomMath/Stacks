module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopSingleProjection
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOfTopCohomology

/-!
# Compatibilities of the cohomology comparison of an exact functor

For an exact functor `F` the comparison `F.mapDerivedCategoryHomologyIso n` identifies
`Hⁿ(F(K))` with `F(Hⁿ(K))`. This file records how these comparisons behave under a natural
transformation `τ : F ⟶ G ⋙ H` of exact functors: on the image of a complex in the derived
category, the comparison of `F` followed by `τ` is the map induced by `τ` followed by the
comparisons of `H` and of `G`.

## Main results

* `Stacks.ModulesOnACategory.TopCohomology.mapDerivedCategoryHomologyIso_hom_app_Q`: the comparison
  on the image of a complex.
* `Stacks.ModulesOnACategory.TopCohomology.compat_Q`: the compatibility of the comparison on the
  image of a complex with a natural transformation `τ : F ⟶ G ⋙ H`.
* `Stacks.MapDerivedHomologyCompat.homology_map_mapDerivedCategorySingleFunctor_hom_app`: on a
  complex `P[0]` concentrated in degree zero, the comparison is compatible with the
  identifications `H⁰(P[0]) ≅ P` and `F(P)[0] ≅ F(P[0])`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.MapDerivedHomologyCompat

open Stacks.ModulesOnACategory.TopCohomology

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

section Single

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The projection from the cycles of `X[0]` to its degree zero homology, followed by the
identification with `X`, is the inclusion of the cycles followed by `X[0]₀ ≅ X`. -/
private lemma homologyπ_single_hom_self {C : Type*} [Category C] [Abelian C] (X : C) :
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).homologyπ 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom =
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom := by
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom]

open HomologicalComplex in
/-- On a complex `P[0]` concentrated in degree zero, the cohomology comparison of `F` on complexes
is compatible with the identifications `H⁰(P[0]) ≅ P` and `F(P)[0] ≅ F(P[0])`. -/
lemma homologyMap_mapCochainComplexSingleFunctor_hom_app (P : A) :
    HomologicalComplex.homologyMap ((F.mapCochainComplexSingleFunctor 0).hom.app P) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj P)).hom =
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) 0).hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P) ≫
        F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 P).hom := by
  refine (cancel_epi (((CochainComplex.singleFunctor A 0 ⋙
    F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homologyπ 0)).1 ?_
  have h2 : ((F.mapCochainComplexSingleFunctor 0).hom.app P).f 0 =
      F.map (singleObjXSelf (ComplexShape.up ℤ) 0 P).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj P)).inv :=
    singleMapHomologicalComplex_hom_app_self F (ComplexShape.up ℤ) 0 P
  have L : ((CochainComplex.singleFunctor A 0 ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homologyπ 0 ≫
      homologyMap ((F.mapCochainComplexSingleFunctor 0).hom.app P) 0 ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj P)).hom =
      ((CochainComplex.singleFunctor A 0 ⋙
        F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).iCycles 0 ≫
        F.map (singleObjXSelf (ComplexShape.up ℤ) 0 P).hom := by
    rw [homologyπ_naturality_assoc]
    refine (congrArg (_ ≫ ·) (homologyπ_single_hom_self (F.obj P))).trans ?_
    refine (cyclesMap_i_assoc ((F.mapCochainComplexSingleFunctor 0).hom.app P) 0 _).trans ?_
    rw [h2, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have R : ((((single A (ComplexShape.up ℤ) 0).obj P).sc 0).map F).homologyπ ≫
      (((((single A (ComplexShape.up ℤ) 0).obj P).sc 0).mapHomologyIso F).hom ≫
        F.map (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 P).hom) =
      ((((single A (ComplexShape.up ℤ) 0).obj P).sc 0).map F).iCycles ≫
        F.map (singleObjXSelf (ComplexShape.up ℤ) 0 P).hom := by
    rw [ShortComplex.homologyπ_comp_mapHomologyIso_hom_assoc]
    exact (congrArg (_ ≫ ·) ((F.map_comp _ _).symm.trans
      ((congrArg F.map (homologyπ_single_hom_self P)).trans
        (F.map_comp _ _)))).trans (ShortComplex.mapCyclesIso_hom_iCycles_assoc _ _ _)
  exact L.trans R.symm

omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private lemma single_chase {E : Type*} [Category E] {a b c d e f g t : E}
    (fa : a ⟶ b) (q : b ⟶ c) (h₂ : c ⟶ d) (s₂ : d ⟶ t) (h₂' : b ⟶ e) (m : e ⟶ f)
    (x : f ⟶ g) (y : g ⟶ t) (z : f ⟶ t) (hc : x ≫ y = z)
    (h : q ≫ h₂ ≫ s₂ = h₂' ≫ m ≫ z) :
    (fa ≫ q) ≫ h₂ ≫ s₂ = (fa ≫ h₂' ≫ m ≫ x) ≫ y := by
  simp only [Category.assoc, hc, h]

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

/-- On `P[0]`, the cohomology comparison `H⁰(F(P[0])) ≅ F(H⁰(P[0]))` of an exact functor is
compatible with `F(P)[0] ≅ F(P[0])` and the identifications `H⁰(Q[0]) ≅ Q`. -/
lemma homology_map_mapDerivedCategorySingleFunctor_hom_app (P : A) :
    (DerivedCategory.homologyFunctor B 0).map ((F.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (F.obj P) =
      (F.mapDerivedCategoryHomologyIso 0).hom.app ((DerivedCategory.singleFunctor A 0).obj P) ≫
        F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).hom.app P) := by
  have h5 := homologyMap_mapCochainComplexSingleFunctor_hom_app F P
  have h6 := DerivedCategory.homologyFunctorFactors_hom_naturality
    ((F.mapCochainComplexSingleFunctor 0).hom.app P) 0
  have hκ : (F.mapDerivedCategorySingleFunctor 0).hom.app P =
      F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app P) := by
    rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app P,
      Iso.hom_inv_id_app_assoc]
  rw [hκ, Stacks.TopSingleProjection.singleFunctorCompHomologyFunctorIso_hom_app (F.obj P) 0,
    Stacks.TopSingleProjection.singleFunctorCompHomologyFunctorIso_hom_app P 0]
  change _ = (F.mapDerivedCategoryHomologyIso 0).hom.app (DerivedCategory.Q.obj
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P)) ≫
    F.map ((DerivedCategory.homologyFunctorFactors A 0).hom.app
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P) ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 P).hom)
  rw [mapDerivedCategoryHomologyIso_hom_app_Q F 0
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P)]
  have hc : F.map ((DerivedCategory.homologyFunctorFactors A 0).inv.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P)) ≫
      F.map ((DerivedCategory.homologyFunctorFactors A 0).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj P) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 P).hom) =
      F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 P).hom :=
    (F.map_comp _ _).symm.trans (congrArg F.map (Iso.inv_hom_id_app_assoc _ _ _))
  rw [(DerivedCategory.homologyFunctor B 0).map_comp]
  exact single_chase _ _ _ _ _ _ _ _ _ hc (((reassoc_of% h6)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj P)).hom).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h5)))

end Single

end Stacks.MapDerivedHomologyCompat
