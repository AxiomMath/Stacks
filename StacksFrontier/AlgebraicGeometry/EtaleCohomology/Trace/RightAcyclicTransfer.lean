module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowComparisonDevissage

/-!
# Transporting acyclic objects along exact functors

Let `G' : 𝒜' ⥤ ℳ'` and `G : 𝒜 ⥤ ℳ` be additive functors, `r_A : 𝒜' ⥤ 𝒜` and `r_M : ℳ' ⥤ ℳ`
exact functors with `G' ⋙ r_M ≅ r_A ⋙ G`, and suppose that `r_A` carries injectives to
`G`-acyclic objects. Then `RG' ⋙ r_M ≅ r_A ⋙ RG`
(`CategoryTheory.Functor.rightDerivedRestrictionIso`), compatibly with the units. This file
reads off that compatibility at a complex concentrated in degree zero:

* `r_A` carries `G'`-acyclic objects to `G`-acyclic objects;
* if `r_M` reflects isomorphisms, an object whose image under `r_A` is `G`-acyclic is
  `G'`-acyclic.

## Main results

* `CategoryTheory.Functor.rightAcyclic_obj_of_rightAcyclic`: `r_A` carries `G'`-acyclic objects
  to `G`-acyclic objects.
* `CategoryTheory.Functor.rightAcyclic_of_rightAcyclic_obj`: if `r_M` reflects isomorphisms, an
  object whose image under `r_A` is `G`-acyclic is `G'`-acyclic.
* `CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategoryPlus`: an exact functor
  reflecting isomorphisms induces a functor on bounded below derived categories reflecting
  isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Reflects

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.ReflectsIsomorphisms]

/-- **An exact functor reflecting isomorphisms induces a functor on bounded below derived
categories reflecting isomorphisms.** -/
theorem reflectsIsomorphisms_mapDerivedCategoryPlus :
    F.mapDerivedCategoryPlus.ReflectsIsomorphisms where
  reflects {K L} f hf := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro n
    have h : IsIso ((DerivedCategory.homologyFunctor B n).map
        (F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f))) :=
      (inferInstance : IsIso ((DerivedCategory.Plus.homologyFunctor B n).map
        (F.mapDerivedCategoryPlus.map f)))
    have h' := (F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff
      (DerivedCategory.Plus.ι.map f) n).1 h
    have h'' : IsIso (F.map ((DerivedCategory.Plus.homologyFunctor A n).map f)) := h'
    exact isIso_of_reflects_iso _ F

end Reflects

/-- The unit of `RG` (Mathlib's `rightDerivedFunctorPlusUnith`, whose definition is not exposed)
followed by the comparison isomorphism with the `totalRightDerived` presentation is the unit of
`totalRightDerived`. -/
private lemma totalRightDerivedUnit_app_eq {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E] [EnoughInjectives D]
    (G : D ⥤ E) [G.Additive] (Y : HomotopyCategory.Plus D) :
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app Y =
      G.rightDerivedFunctorPlusUnith.app Y ≫
        (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
          (HomotopyCategory.Plus.quasiIso D) _
          ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
            DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))).app
          (DerivedCategory.Plus.Qh.obj Y) :=
  (Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _ _ Y).symm

private lemma isIso_rightDerivedDesc_totalRightDerivedUnit {D E : Type*} [Category* D]
    [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives D] (G : D ⥤ E) [G.Additive] :
    IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance

/-- An object is right acyclic for `G` exactly when the unit `rightDerivedFunctorPlusUnith` is
invertible at the single complex on it in degree zero. -/
private lemma rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app {D E : Type*}
    [Category* D] [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D]
    [HasDerivedCategory E] [EnoughInjectives D] (G : D ⥤ E) [G.Additive] (X : D) :
    G.rightAcyclic X ↔ IsIso (G.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor D 0).obj X)) := by
  have := isIso_rightDerivedDesc_totalRightDerivedUnit G
  change IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app _) ↔ _
  rw [totalRightDerivedUnit_app_eq]
  exact isIso_comp_right_iff _ _

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory M'] [HasDerivedCategory M]
  [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  (G' : A' ⥤ M') (G : A ⥤ M) (rA : A' ⥤ A) (rM : M' ⥤ M)
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive]
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rM] [PreservesFiniteColimits rM]
  (e : G' ⋙ rM ≅ rA ⋙ G) (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I))

include e hac in
/-- The unit of `RG` at `r_A(X[0])` is invertible exactly when `r_M` of the unit of `RG'` at
`X[0]` is. -/
lemma isIso_unit_map_iff (X : A') :
    IsIso (G.rightDerivedFunctorPlusUnith.app
        (rA.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A' 0).obj X))) ↔
      IsIso (rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor A' 0).obj X))) := by
  have h := map_unit_comp_rightDerivedRestrictionIso_hom_app G' G rA rM e hac
    ((HomotopyCategory.Plus.singleFunctor A' 0).obj X)
  constructor
  · intro hu
    have : IsIso (rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor A' 0).obj X)) ≫
          (rightDerivedRestrictionIso G' G rA rM e hac).hom.app
            (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A' 0).obj X))) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _
      ((rightDerivedRestrictionIso G' G rA rM e hac).hom.app _)
  · intro hu
    have h' : IsIso (rM.mapDerivedCategoryPlusFactorsh.hom.app
          (G'.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A' 0).obj X)) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).hom.app _ ≫
            (mapHomotopyCategoryPlusNatIso e).hom.app _ ≫
            (mapHomotopyCategoryPlusCompIso (Iso.refl (rA ⋙ G))).inv.app _) ≫
        G.rightDerivedFunctorPlusUnith.app
          (rA.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A' 0).obj X)) ≫
        G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlusFactorsh.inv.app _)) := by
      rw [← h]; infer_instance
    rwa [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at h'

include e hac in
/-- **`r_A` carries `G'`-acyclic objects to `G`-acyclic objects.** -/
theorem rightAcyclic_obj_of_rightAcyclic (X : A') (hX : G'.rightAcyclic X) :
    G.rightAcyclic (rA.obj X) := by
  have hX' : IsIso (G'.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A' 0).obj X)) :=
    (rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app G' X).1 hX
  have hu := (isIso_unit_map_iff G' G rA rM e hac X).2 inferInstance
  exact (rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app G (rA.obj X)).2
    ((NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnith
      (rA.mapHomotopyCategoryPlusObjSingleIso 0 X)).1 hu)

include e hac in
/-- **Acyclicity descends along `r_A` when `r_M` reflects isomorphisms.** -/
theorem rightAcyclic_of_rightAcyclic_obj [rM.ReflectsIsomorphisms] (X : A')
    (hX : G.rightAcyclic (rA.obj X)) : G'.rightAcyclic X := by
  have hX' : IsIso (G.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj (rA.obj X))) :=
    (rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app G (rA.obj X)).1 hX
  have hu := (NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnith
    (rA.mapHomotopyCategoryPlusObjSingleIso 0 X)).2 hX'
  have hm := (isIso_unit_map_iff G' G rA rM e hac X).1 hu
  have := reflectsIsomorphisms_mapDerivedCategoryPlus rM
  have := isIso_rightDerivedDesc_totalRightDerivedUnit G'
  have hm' : IsIso (rM.mapDerivedCategoryPlus.map
      (((G'.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A')).app
        ((HomotopyCategory.Plus.singleFunctor A' 0).obj X))) := by
    rw [totalRightDerivedUnit_app_eq, Functor.map_comp]
    infer_instance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ rM.mapDerivedCategoryPlus hm' _

end CategoryTheory.Functor

end
