module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

/-!
# Pushing forward and forgetting, read over the homotopy category

`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` is the
comparison `f_*^D ⋙ Φ_Y^D ≅ Φ_X^D ⋙ f_*^{ab,D}` on unbounded derived categories, and
`derivedModulePushforwardCompToSheafIso_fac` pins it down at the image of a **cochain complex**,
through `CategoryTheory.Functor.mapDerivedCategoryFactors`.

A right derived functor on an unbounded derived category is characterised by a factorization
stated over `DerivedCategory.Qh`, at the image of an object of the **homotopy** category, through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`.  A proof that meets the comparison there
cannot use `derivedModulePushforwardCompToSheafIso_fac`: the two live over different localization
functors.

This file supplies the missing form, `derivedModulePushforwardCompToSheafIso_fach`.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompIso_inv_app_Q`: the inverse of the composition
  comparison of `CategoryTheory.Functor.mapDerivedCategoryCompIso` at the image of a cochain
  complex; the companion of `CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q`.
* `Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_fach`:
  **what pins the derived comparison down over `DerivedCategory.Qh`.**  At the image of an object
  of the homotopy category it intertwines the four `mapDerivedCategoryFactorsh`, exactly as
  `derivedModulePushforwardCompToSheafIso_fac` intertwines the four `mapDerivedCategoryFactors`.

## Implementation notes

The route is not to redo the conjugation by `DerivedCategory.quotientCompQhIso` — that is already
done once and for all in
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory`, for
`CategoryTheory.Functor.mapDerivedCategoryCompIso`.  Instead the comparison is rebuilt out of that
isomorphism, as

`f_*^D ⋙ Φ_Y^D ≅ (f_* ⋙ Φ_Y)^D ≅ Φ_X^D ⋙ f_*^{ab,D}`,

whose two halves are `mapDerivedCategoryCompIso` applied to `Iso.refl` and to
`Stacks.Cohomology.ModulePushforwardComparison.modulePushforwardCompToSheafIso`; the rebuilt
isomorphism has both evaluations, over `DerivedCategory.Q` and over `DerivedCategory.Qh`, and
`compIsoBuild_eq` identifies it with the original by `CategoryTheory.Localization.natTrans_ext`
from the two evaluations over `DerivedCategory.Q`.

**Two devices against the two spellings.**  `f_* ⋙ Φ_Y` and `Φ_X ⋙ f_*^{ab}` are definitionally
equal functors with different spellings, so a composite that passes from one to the other is well
typed and yet opaque to `rw`.  `chain_cancel` is stated at a variable category, with the two
spellings as *distinct* object variables joined by one hypothesis, and `comp_map_comp_id` likewise;
both are applied with `exact`, which checks up to definitional equality.  The passage between the
spellings is isolated in `reflCompSym` and `reflCompSymComplex`, each proved by `rfl`, so the
expensive definitional check happens once per declaration rather than once per cancellation step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace CategoryTheory.Functor

section General

universe w₁ w₂ w₃

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The inverse of the composition comparison attached to `e : F ⋙ G ≅ H` at the image of a
cochain complex: the inverse of the composite of
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q`, factor by factor in the opposite
order.  This is the companion over `DerivedCategory.Q` of
`CategoryTheory.Functor.mapDerivedCategoryCompIso_inv_app_Qh`. -/
theorem mapDerivedCategoryCompIso_inv_app_Q (e : F ⋙ G ≅ H) (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryCompIso e).inv.app (DerivedCategory.Q.obj K) =
      H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app K) ≫
          G.mapDerivedCategoryFactors.inv.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  have hiso : (Functor.mapDerivedCategoryCompIso e).app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
        G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
          DerivedCategory.Q.mapIso
              ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).app K) ≪≫
            (H.mapDerivedCategoryFactors.app K).symm :=
    Iso.ext (Functor.mapDerivedCategoryCompIso_hom_app_Q e K)
  refine (congrArg Iso.inv hiso).trans ?_
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end General

end CategoryTheory.Functor

namespace Stacks.Cohomology.ModulePushforwardComparison

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### Two formal cancellations at a variable category -/

/-- Cancelling a composable pair whose composite is the identity inside the argument of a functor,
at an abstract category.  Stated with the source and the target of the pair written as the same
object variable, so that instantiating it identifies the two spellings once, at default
transparency. -/
private lemma comp_map_comp_id {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : C₀ ⥤ D₀)
    {A B : C₀} (a : A ⟶ B) (b : B ⟶ A) (hab : a ≫ b = 𝟙 A) {V : D₀} (r : V ⟶ W.obj A) :
    r ≫ W.map a ≫ W.map b = r := by
  rw [← W.map_comp, hab, W.map_id, Category.comp_id]

/-- Collapsing the ten-morphism chain the comparison unfolds to, at an abstract category: two
composable pairs are inverse to each other, and the two morphisms that cross between the two
spellings of the composite functor are absorbed into the leading pair by the hypothesis `hs`. -/
private lemma chain_cancel {C₀ : Type*} [Category* C₀] {W V A A₁ A₂ A' B B₁ : C₀}
    (p : W ⟶ V) (r : V ⟶ A)
    (q₁ : A ⟶ A₁) (u₁ : A₁ ⟶ A₂) (u₂ : A₂ ⟶ A₁) (h₁ : u₁ ≫ u₂ = 𝟙 A₁)
    (q₂ : A₁ ⟶ A')
    (v₁ : A' ⟶ B) (w₁ : B ⟶ B₁) (w₂ : B₁ ⟶ B) (hw : w₁ ≫ w₂ = 𝟙 B) (v₂ : B ⟶ A')
    (hv : v₁ ≫ v₂ = 𝟙 A') (s : V ⟶ A') (hs : r ≫ q₁ ≫ q₂ = s) :
    p ≫ r ≫ q₁ ≫ u₁ ≫ u₂ ≫ q₂ ≫ v₁ ≫ w₁ ≫ w₂ ≫ v₂ = p ≫ s := by
  rw [← hs]
  simp [hv, reassoc_of% h₁, reassoc_of% hw]

/-! ### The comparison rebuilt from the composition isomorphism -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [PreservesFiniteLimits (modulePushforward f)]
  [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (abelianPushforward f)]

/-- The comparison `f_*^D ⋙ Φ_Y^D ≅ Φ_X^D ⋙ f_*^{ab,D}` assembled from
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, which has evaluations over both
`DerivedCategory.Q` and `DerivedCategory.Qh`.  `compIsoBuild_eq` identifies it with
`derivedModulePushforwardCompToSheafIso`. -/
private def compIsoBuild :
    (modulePushforward f).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategory ⋙
        (abelianPushforward f).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso
      (Iso.refl (modulePushforward f ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing Y))) ≪≫
    (Functor.mapDerivedCategoryCompIso (modulePushforwardCompToSheafIso f).symm).symm

omit [PreservesFiniteLimits (modulePushforward f)] [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (abelianPushforward f)] in
/-- The two comparisons of homotopy categories crossing between the two spellings of
`f_* ⋙ Φ_Y` compose to the identity: both are quotients of identity maps of complexes. -/
private lemma reflCompSym
    (J : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (modulePushforward f ⋙
            _root_.SheafOfModules.toSheaf (structureSheafRing Y)))
          (ComplexShape.up ℤ)).hom.app J ≫
        (Functor.mapHomotopyCategoryCompIso (modulePushforwardCompToSheafIso f).symm
          (ComplexShape.up ℤ)).inv.app J =
      𝟙 _ := rfl

omit [PreservesFiniteLimits (modulePushforward f)] [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (abelianPushforward f)] in
/-- The complexes-level counterpart of `reflCompSym`. -/
private lemma reflCompSymComplex
    (P : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (Functor.mapHomologicalComplexCompIso
          (Iso.refl (modulePushforward f ⋙
            _root_.SheafOfModules.toSheaf (structureSheafRing Y)))
          (ComplexShape.up ℤ)).hom.app P ≫
        (Functor.mapHomologicalComplexCompIso (modulePushforwardCompToSheafIso f).symm
          (ComplexShape.up ℤ)).inv.app P =
      𝟙 _ := rfl

/-- The rebuilt comparison at the image of a cochain complex: it satisfies the factorization of
`derivedModulePushforwardCompToSheafIso_fac` verbatim. -/
private lemma compIsoBuild_fac
    (P : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (compIsoBuild f).hom.app (DerivedCategory.Q.obj P) ≫
        (abelianPushforward f).mapDerivedCategory.map
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategoryFactors.hom.app P) ≫
        (abelianPushforward f).mapDerivedCategoryFactors.hom.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (show ((modulePushforward f).mapDerivedCategory ⋙
              (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory).obj
                (DerivedCategory.Q.obj P) ⟶
            DerivedCategory.Q.obj
              (((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) from
        (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.map
            ((modulePushforward f).mapDerivedCategoryFactors.hom.app P) ≫
          (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategoryFactors.hom.app
            (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  simp only [compIsoBuild, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_Q, Functor.mapDerivedCategoryCompIso_inv_app_Q]
  refine chain_cancel _ _ _ _ _ ?_ _ _ _ _ ?_ _ ?_ _ ?_
  · exact Iso.inv_hom_id_app _ _
  · exact ((abelianPushforward f).mapDerivedCategory.mapIso
      ((_root_.SheafOfModules.toSheaf
        (structureSheafRing X)).mapDerivedCategoryFactors.app P)).inv_hom_id
  · exact Iso.inv_hom_id_app _ _
  · exact comp_map_comp_id DerivedCategory.Q _ _ (reflCompSymComplex f P) _

/-- The rebuilt comparison is `derivedModulePushforwardCompToSheafIso`: both are natural
transformations between functors on the derived category, both satisfy the factorization of
`derivedModulePushforwardCompToSheafIso_fac` at the image of every cochain complex, and that
factorization determines a transformation there, the remaining factors being isomorphisms. -/
private lemma compIsoBuild_eq : compIsoBuild f = derivedModulePushforwardCompToSheafIso f := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) fun P => ?_)
  exact (cancel_mono _).mp
    ((compIsoBuild_fac f P).trans (derivedModulePushforwardCompToSheafIso_fac f P).symm)

/-- The rebuilt comparison over `DerivedCategory.Qh`: it intertwines the four
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, by the evaluation of
`CategoryTheory.Functor.mapDerivedCategoryCompIso` at the image of an object of the homotopy
category. -/
private lemma compIsoBuild_fach
    (J : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (compIsoBuild f).hom.app (DerivedCategory.Qh.obj J) ≫
        (abelianPushforward f).mapDerivedCategory.map
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app J) ≫
        (abelianPushforward f).mapDerivedCategoryFactorsh.hom.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.map
          ((modulePushforward f).mapDerivedCategoryFactorsh.hom.app J) ≫
        (show (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj
                (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ⟶
            DerivedCategory.Qh.obj
              (((abelianPushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
                (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj J)) from
          (_root_.SheafOfModules.toSheaf
            (structureSheafRing Y)).mapDerivedCategoryFactorsh.hom.app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) := by
  simp only [compIsoBuild, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_Qh,
    Functor.mapDerivedCategoryCompIso_inv_app_Qh]
  refine chain_cancel _ _ _ _ _ ?_ _ _ _ _ ?_ _ ?_ _ ?_
  · exact Iso.inv_hom_id_app _ _
  · exact ((abelianPushforward f).mapDerivedCategory.mapIso
      ((_root_.SheafOfModules.toSheaf
        (structureSheafRing X)).mapDerivedCategoryFactorsh.app J)).inv_hom_id
  · exact Iso.inv_hom_id_app _ _
  · exact comp_map_comp_id DerivedCategory.Qh _ _ (reflCompSym f J) _

/-- **What pins the derived comparison down over `DerivedCategory.Qh`.**  At the image of an
object of the homotopy category of cochain complexes it intertwines the canonical factorizations
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the four functors involved: going down the
right-hand side of the square and then forgetting degreewise is going down the left-hand side and
then pushing forward degreewise.  No inverse occurs, so the identity can be used in either
direction.

This is `derivedModulePushforwardCompToSheafIso_fac` over `DerivedCategory.Qh`, which is the
localization functor the universal property of a right derived functor is stated over. -/
theorem derivedModulePushforwardCompToSheafIso_fach
    (J : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    (derivedModulePushforwardCompToSheafIso f).hom.app (DerivedCategory.Qh.obj J) ≫
        (abelianPushforward f).mapDerivedCategory.map
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app J) ≫
        (abelianPushforward f).mapDerivedCategoryFactorsh.hom.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.map
          ((modulePushforward f).mapDerivedCategoryFactorsh.hom.app J) ≫
        (show (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj
                (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ⟶
            DerivedCategory.Qh.obj
              (((abelianPushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
                (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj J)) from
          (_root_.SheafOfModules.toSheaf
            (structureSheafRing Y)).mapDerivedCategoryFactorsh.hom.app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) := by
  rw [← compIsoBuild_eq f]
  exact compIsoBuild_fach f J

end Stacks.Cohomology.ModulePushforwardComparison

end
