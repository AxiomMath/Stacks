module

public import StacksFrontier.Algebra.Homology.RightDerivedEdge
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CocycleFormula

/-!
# The edge morphism of an exact functor is the inverse of the comparison of Stacks 03FD

Let `F : B ⥤ A` be an exact functor between abelian categories which preserves injective
objects, and let `G : A ⥤ Ab` be a left exact functor corepresented by `X`. Two morphisms
relate `Rⁿ(F ⋙ G)` and `F ⋙ RⁿG`:

* the edge morphism `Stacks.Cohomology.RightDerivedEdge.edge F G n : F ⋙ RⁿG ⟶ Rⁿ(F ⋙ G)`,
  built from a comparison of injective resolutions; and
* the comparison `ModuleSheafCohomology.comparisonIso` of Stacks 03FD,
  `Rⁿ(F ⋙ G) ≅ F ⋙ RⁿG`, characterized as the unique isomorphism of `δ`-functors normalized
  in degree zero, where the `δ`-structures come from `Ext`.

They are inverse to each other (`edge_eq_comparisonIso_inv`). In positive degree both are read
on the chosen resolutions (`ModuleComparison.comparisonIso_hom_app_succ_eq` and
`RightDerivedEdge.edge_app_eq`), and the composite of the two comparisons of resolutions is an
endomorphism of `F` applied to an injective resolution, which is again an injective resolution
because `F` is exact and preserves injectives; it extends the identity, hence induces the identity
on cohomology. In degree zero both are normalized by the canonical maps to `R⁰`
(`toRightDerivedZero_comp_edge_zero`).

Through `ModuleComparison.comparisonIso_hom_eq_extMapComp` this gives the edge morphism an
`Ext`-level formula, which is how the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) compares the canonical geometric Frobenius
on `Hⁱ_c(X_k̄, K)` with its action on `Ext`.

## Main results

* `Stacks.Cohomology.RightDerivedEdge.toRightDerivedZero_comp_edge_zero`: in degree zero the edge
  morphism intertwines the two canonical maps to `R⁰`, for any `F` preserving injectives.
* `Stacks.Cohomology.RightDerivedEdge.edge_eq_comparisonIso_inv`: **the edge morphism of an exact
  functor preserving injectives is the inverse of the comparison of Stacks 03FD**, in every
  degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian ModuleSheafCohomology

namespace Stacks.Cohomology.RightDerivedEdge

open Stacks.Cohomology.CompositeRightDerived

/-- Cancelling an isomorphism in the middle of a composite, abstract in the objects so that it
applies across definitionally but not syntactically equal spellings. -/
private theorem cancel_iso_mid {C : Type*} [Category* C] {W X Y Z V : C} (a : W ⟶ X)
    (b : X ⟶ Y) (e : Z ≅ Y) (r : Y ⟶ V) : (a ≫ b ≫ e.inv) ≫ e.hom ≫ r = a ≫ b ≫ r := by
  simp

section DegreeZero

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects] (Q : B ⥤ D) [Q.Additive]

/-- **In degree zero the edge morphism intertwines the canonical maps to `R⁰`.** The canonical
map `Q (P X) ⟶ R⁰Q (P X)` followed by the edge morphism is the canonical map
`(P ⋙ Q) X ⟶ R⁰(P ⋙ Q) X`. -/
theorem toRightDerivedZero_comp_edge_zero (X : A) :
    Q.toRightDerivedZero.app (P.obj X) ≫ (edge P Q 0).app X =
      (P ⋙ Q).toRightDerivedZero.app X := by
  have hcyc : (injectiveResolution (P.obj X)).toRightDerivedZero' Q ≫
      HomologicalComplex.cyclesMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison P X)) 0 =
      (injectiveResolution X).toRightDerivedZero' (P ⋙ Q) := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0), Category.assoc,
      HomologicalComplex.cyclesMap_i, InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    refine Eq.trans ?_
      (InjectiveResolution.toRightDerivedZero'_comp_iCycles (injectiveResolution X) (P ⋙ Q)).symm
    exact (Q.map_comp _ _).symm.trans (congrArg Q.map (ι_f_zero_comp_resolutionComparison P X))
  have key : (injectiveResolution (P.obj X)).toRightDerivedZero' Q ≫
      HomologicalComplex.homologyπ _ 0 ≫
      HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison P X)) 0 ≫
      (isoRightDerivedObjComp P Q (injectiveResolution X) 0).inv =
    (injectiveResolution X).toRightDerivedZero' (P ⋙ Q) ≫ HomologicalComplex.homologyπ _ 0 ≫
      ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) 0).inv := by
    have h1 := congrArg (fun t => (injectiveResolution (P.obj X)).toRightDerivedZero' Q ≫ t)
      ((reassoc_of% HomologicalComplex.homologyπ_naturality
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison P X)) 0)
        (isoRightDerivedObjComp P Q (injectiveResolution X) 0).inv)
    have h2 := congrArg (fun t => t ≫ HomologicalComplex.homologyπ _ 0 ≫
      ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) 0).inv) hcyc
    exact h1.trans ((Category.assoc _ _ _).symm.trans h2)
  refine Eq.trans ?_
    (key.trans (InjectiveResolution.toRightDerivedZero_eq (injectiveResolution X) (P ⋙ Q)).symm)
  rw [InjectiveResolution.toRightDerivedZero_eq (injectiveResolution (P.obj X)) Q]
  change ((injectiveResolution (P.obj X)).toRightDerivedZero' Q ≫
      HomologicalComplex.homologyπ _ 0 ≫
      ((injectiveResolution (P.obj X)).isoRightDerivedObj Q 0).inv) ≫
      ((injectiveResolution (P.obj X)).isoRightDerivedObj Q 0).hom ≫
      HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison P X)) 0 ≫
      (isoRightDerivedObjComp P Q (injectiveResolution X) 0).inv = _
  exact cancel_iso_mid _ _ _ _

end DegreeZero

/-- Cancelling a pair of mutually inverse factors flanked by an isomorphism and its inverse,
abstract in the objects. -/
private theorem conj_cancel {C : Type*} [Category* C] {W X Y Z : C} (a : W ≅ X) (x : X ⟶ Y)
    (e : Z ≅ Y) (y : Y ⟶ X) (hxy : x ≫ y = 𝟙 X) :
    (a.hom ≫ x ≫ e.inv) ≫ e.hom ≫ y ≫ a.inv = 𝟙 W := by
  simp [reassoc_of% hxy]

section ComparisonIso

universe v uA uB

variable {A : Type uA} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]
  [EnoughInjectives A] {B : Type uB} [Category.{v} B] [Abelian B] [HasExt.{v} B]
  [HasInjectiveResolutions B] [EnoughInjectives B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects]
  (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G] (X : A)
  (α : G ≅ preadditiveCoyoneda.obj (op X)) (Y : B)
  (β : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))
  (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext.{v} X (F.obj I) (n + 1)), e = 0)

/-- In positive degree the comparison of Stacks 03FD followed by the edge morphism is the
identity: both are read on the chosen resolutions, and the composite of the two comparisons of
resolutions is an endomorphism of `F` applied to the chosen resolution of `M` — itself an injective
resolution of `F M` — extending the identity. -/
theorem comparisonIso_hom_comp_edge_succ (n : ℕ) :
    (comparisonIso F G X α Y β h (n + 1)).hom ≫ edge F G (n + 1) = 𝟙 _ := by
  refine NatTrans.ext (funext fun M => ?_)
  obtain ⟨φ, hφ⟩ := ModuleComparison.exists_mapResolutionComparison F (injectiveResolution M)
    (injectiveResolution (F.obj M))
  rw [NatTrans.comp_app, ModuleComparison.comparisonIso_hom_app_succ_eq F G X α Y β h n M φ hφ,
    edge_app_eq F G (n + 1) (injectiveResolution M) (injectiveResolution (F.obj M))
      (resolutionComparison F M) (ι_f_zero_comp_resolutionComparison F M)]
  have hid : HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1) ≫
      HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison F M)) (n + 1) =
      𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have haug : (mapInjRes F (injectiveResolution M)).ι.f 0 ≫
        (φ ≫ resolutionComparison F M).f 0 =
        (mapInjRes F (injectiveResolution M)).ι.f 0 ≫
          HomologicalComplex.Hom.f (𝟙 (mapInjRes F (injectiveResolution M)).cocomplex) 0 :=
      ((congrArg (fun t => t ≫ (φ ≫ resolutionComparison F M).f 0)
        (Stacks.DerivedIndexing.mapInjRes_ι_f_zero F (injectiveResolution M))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ (resolutionComparison F M).f 0) hφ).trans
            ((ι_f_zero_comp_resolutionComparison F M).trans
              (Stacks.DerivedIndexing.mapInjRes_ι_f_zero F (injectiveResolution M)).symm)))).trans
        (Category.comp_id _).symm
    exact (homologyMap_map_eq_of_aug G (mapInjRes F (injectiveResolution M))
      (mapInjRes F (injectiveResolution M)).injective _ _ haug (n + 1)).trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f (n + 1))
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map_id _)).trans
        (HomologicalComplex.homologyMap_id _ _))
  exact conj_cancel _ _ _ _ hid

/-- **The edge morphism of an exact functor preserving injectives is the inverse of the
comparison of Stacks 03FD**, in every degree. In degree zero both are normalized by the canonical
maps to `R⁰`; in positive degree this is `comparisonIso_hom_comp_edge_succ`. -/
theorem edge_eq_comparisonIso_inv (n : ℕ) :
    edge F G n = (comparisonIso F G X α Y β h n).inv := by
  cases n with
  | zero =>
    rw [comparisonIso_zero]
    refine NatTrans.ext (funext fun M => ?_)
    rw [← cancel_epi (G.toRightDerivedZero.app (F.obj M)), toRightDerivedZero_comp_edge_zero]
    simp [degreeZeroIso]
  | succ n => exact (Iso.inv_ext (comparisonIso_hom_comp_edge_succ F G X α Y β h n)).symm

end ComparisonIso

end Stacks.Cohomology.RightDerivedEdge

end
