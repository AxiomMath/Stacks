module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Pullback on étale cohomology is functorial

For morphisms of schemes `b : Z ⟶ Y` and `a : Y ⟶ X`, restriction of étale cohomology classes
along `a` and then along `b` is restriction along `b ≫ a`, read through the comparison
`(b ≫ a)^{-1} ≅ b^{-1} a^{-1}` of inverse images. The comparisons `π^{-1} 𝐆_{m} ⟶ 𝐆_{m}` and
`π^{-1} μ_n ⟶ μ_n` are compatible with that comparison, so the pullback
`Stacks.EtaleCohomology.rootsOfUnityPullbackMap` on `H^q(-, μ_n)` is a contravariant functor:
`b^* ∘ a^* = (b ≫ a)^*`.

## Main results

* `Stacks.EtaleCohomology.multiplicativeDirectImageComparison_comp`,
  `Stacks.EtaleCohomology.multiplicativeInverseImageComparison_comp`,
  `Stacks.EtaleCohomology.rootsOfUnityInverseImageComparison_comp`: the comparisons on `𝐆_m` and
  `μ_n` for a composite.
* `Stacks.EtaleCohomology.rootsOfUnityPullbackMap_comp`: `b^* (a^* x) = (b ≫ a)^* x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry Stacks.Kummer

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- **Restriction in two steps, abstractly.** For exact functors `A : C ⥤ D`, `B : D ⥤ E` and
`L : C ⥤ E` with `e : L ≅ A ⋙ B`, and identifications `κ_A : A Z_C ≅ Z_D`, `κ_B : B Z_D ≅ Z_E`,
`κ_L : L Z_C ≅ Z_E` compatible with `e`, the two ways of carrying a class of `Ext(Z_C, F)` to
`Ext(Z_E, B A F)` agree. -/
theorem _root_.Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor_comp_iso
    {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
    {E : Type*} [Category* E] [Abelian E] [HasExt.{w} C] [HasExt.{w} D] [HasExt.{w} E]
    [EnoughInjectives C]
    (A : C ⥤ D) [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    (B : D ⥤ E) [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    (L : C ⥤ E) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ≅ A ⋙ B) {ZC : C} {ZD : D} {ZE : E} (κA : A.obj ZC ≅ ZD) (κB : B.obj ZD ≅ ZE)
    (κL : L.obj ZC ≅ ZE) (h : B.map κA.hom ≫ κB.hom = e.inv.app ZC ≫ κL.hom)
    {F : C} {q : ℕ} (x : Ext.{w} ZC F q) :
    (Ext.mk₀ κB.inv).comp (((Ext.mk₀ κA.inv).comp (x.mapExactFunctor A)
        (zero_add q)).mapExactFunctor B) (zero_add q) =
      ((Ext.mk₀ κL.inv).comp (x.mapExactFunctor L) (zero_add q)).comp
        (Ext.mk₀ (e.hom.app F)) (add_zero q) := by
  have hκ : κB.inv ≫ B.map κA.inv = κL.inv ≫ e.hom.app ZC := by
    have h' := congrArg (fun i => i.symm.hom)
      (Iso.ext h : B.mapIso κA ≪≫ κB = (e.app ZC).symm ≪≫ κL)
    exact h'
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor, Ext.mk₀_comp_mk₀_assoc, hκ,
    ← Ext.mk₀_comp_mk₀_assoc, Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.hom,
    Ext.comp_assoc_of_third_deg_zero]

variable {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y) (ba : Z ⟶ X) (hba : ba = b ≫ a)

include hba in
/-- **The direct-image comparison on `𝐆_m` for a composite**: restricting an invertible function
along `V ×_X Y ⟶ V` and then along `(V ×_X Y) ×_Y Z ⟶ V ×_X Y` is restricting it along
`V ×_X Z ⟶ V`, read through the comparison of the two base changes. -/
theorem multiplicativeDirectImageComparison_comp :
    multiplicativeDirectImageComparison.{u, v} a ≫
        (etaleAbelianDirectImage.{u, v} a).map (multiplicativeDirectImageComparison.{u, v} b) =
      multiplicativeDirectImageComparison.{u, v} ba ≫
        (etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
          (multiplicativeSheaf.{u, v} Z) := by
  ext V s
  obtain ⟨x, rfl⟩ := ofUnit_surjective (X := X) (U := V.unop) s
  have hfst := smallEtaleBaseChangeComp'_inv_fst b a ba hba V.unop
  show ofUnit.{u, v} (Units.map
      (pullback.fst ((smallEtaleBaseChange a).obj V.unop).hom b).appTop.hom.toMonoidHom
      (Units.map (pullback.fst V.unop.hom a).appTop.hom.toMonoidHom x)) =
    ((etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
      (multiplicativeSheaf.{u, v} Z)).hom.app V
        (ofUnit.{u, v} (Units.map (pullback.fst V.unop.hom ba).appTop.hom.toMonoidHom x))
  rw [etaleAbelianDirectImageCompIso'_inv_app_hom_app.{u, v}]
  refine Eq.trans ?_ (map_ofUnit.{u, v} _ _).symm
  congr 1
  ext
  have h2 := congrArg (fun f => f.appTop.hom (x : Γ((unop V).left, ⊤))) hfst
  exact h2.symm

include hba in
/-- **The comparison `π^{-1} 𝐆_m ⟶ 𝐆_m` for a composite**: taking the inverse image along `b`
of the comparison for `a` and then the comparison for `b` is the comparison for `b ≫ a`, read
through `(b ≫ a)^{-1} ≅ b^{-1} a^{-1}`. -/
theorem multiplicativeInverseImageComparison_comp :
    (etaleAbelianInverseImage.{u, v} b).map (multiplicativeInverseImageComparison.{u, v} a) ≫
        multiplicativeInverseImageComparison.{u, v} b =
      (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app
          (multiplicativeSheaf.{u, v} X) ≫
        multiplicativeInverseImageComparison.{u, v} ba := by
  have hconj := unit_conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} ba)
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} b))
    (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv (multiplicativeSheaf.{u, v} X)
  rw [conjugateEquiv_etaleAbelianInverseImageCompIso'_inv.{u, v} b a ba hba] at hconj
  apply (((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
    (etaleAbelianInverseImageDirectImageAdj.{u, v} b)).homEquiv _ _).injective
  have hL : ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} b)).homEquiv _ _
          ((etaleAbelianInverseImage.{u, v} b).map
              (multiplicativeInverseImageComparison.{u, v} a) ≫
            multiplicativeInverseImageComparison.{u, v} b) =
      multiplicativeDirectImageComparison.{u, v} a ≫
        (etaleAbelianDirectImage.{u, v} a).map (multiplicativeDirectImageComparison.{u, v} b) := by
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left, multiplicativeInverseImageComparison_transpose,
      Adjunction.homEquiv_naturality_right, multiplicativeInverseImageComparison_transpose]
  have hR : ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} b)).homEquiv _ _
          ((etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app
              (multiplicativeSheaf.{u, v} X) ≫
            multiplicativeInverseImageComparison.{u, v} ba) =
      multiplicativeDirectImageComparison.{u, v} ba ≫
        (etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
          (multiplicativeSheaf.{u, v} Z) := by
    have hnat := ((etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.naturality
      (multiplicativeInverseImageComparison.{u, v} ba)).symm
    conv_lhs => rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit, ← hconj]
    rw [Category.assoc, hnat, ← Category.assoc, ← Adjunction.homEquiv_unit,
      multiplicativeInverseImageComparison_transpose]
  rw [hL, hR]
  exact multiplicativeDirectImageComparison_comp.{u, v} a b ba hba

include hba in
/-- **The comparison `π^{-1} μ_n ⟶ μ_n` for a composite**, read through
`(b ≫ a)^{-1} ≅ b^{-1} a^{-1}`. -/
theorem rootsOfUnityInverseImageComparison_comp (n : ℕ) :
    (etaleAbelianInverseImage.{u, v} b).map (rootsOfUnityInverseImageComparison.{u, v} a n) ≫
        rootsOfUnityInverseImageComparison.{u, v} b n =
      (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app
          (rootsOfUnitySheaf.{u, v} X n) ≫
        rootsOfUnityInverseImageComparison.{u, v} ba n := by
  rw [← cancel_mono (rootsOfUnityι.{u, v} Z n), Category.assoc, Category.assoc,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityι,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, ← Functor.map_comp_assoc,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, Functor.map_comp, Category.assoc,
    multiplicativeInverseImageComparison_comp.{u, v} a b ba hba,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.naturality
    (rootsOfUnityι.{u, v} X n)

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include hba in
/-- Restriction along `a` and then along `b` is restriction along `b ≫ a` followed by the
comparison `(b ≫ a)^{-1} F ≅ b^{-1} a^{-1} F`. -/
theorem etaleCohomologyRestrictionMap_comp_eq_map_hom
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    etaleCohomologyRestrictionMap.{u, v, w} b ((etaleAbelianInverseImage.{u, v} a).obj F) q
        (etaleCohomologyRestrictionMap.{u, v, w} a F q x) =
      Sheaf.H.map ((etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).hom.app F) q
        (etaleCohomologyRestrictionMap.{u, v, w} ba F q x) := by
  rw [etaleCohomologyRestrictionMap_apply.{u, v, w} ba F q x,
    etaleCohomologyRestrictionMap_apply.{u, v, w} a F q x,
    etaleCohomologyRestrictionMap_apply.{u, v, w} b _ q, Sheaf.H.map_apply]
  exact Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor_comp_iso
    (etaleAbelianInverseImage.{u, v} a) (etaleAbelianInverseImage.{u, v} b)
    (etaleAbelianInverseImage.{u, v} ba) (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba)
    ((etaleAbelianInverseImageConstantIso.{u, v} a).app (AddCommGrpCat.of (ULift ℤ)))
    ((etaleAbelianInverseImageConstantIso.{u, v} b).app (AddCommGrpCat.of (ULift ℤ)))
    ((etaleAbelianInverseImageConstantIso.{u, v} ba).app (AddCommGrpCat.of (ULift ℤ)))
    (etaleAbelianInverseImageConstantIso_comp.{u, v} a b ba hba _) x

include hba in
/-- **Pullback on `H^q(-, μ_n)` is functorial**: `b^* (a^* x) = (b ≫ a)^* x` for
`Stacks.EtaleCohomology.rootsOfUnityPullbackMap`. -/
theorem rootsOfUnityPullbackMap_comp (n q : ℕ) (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) q) :
    rootsOfUnityPullbackMap.{u, v, w} b n q (rootsOfUnityPullbackMap.{u, v, w} a n q x) =
      rootsOfUnityPullbackMap.{u, v, w} ba n q x := by
  have hres := etaleCohomologyRestrictionMap_comp_eq_map_hom.{u, v, w} a b ba hba
    (rootsOfUnitySheaf.{u, v} X n) q x
  simp only [rootsOfUnityPullbackMap_apply, Sheaf.H.map_apply]
  rw [etaleCohomologyRestrictionMap_comp_mk₀, hres, Sheaf.H.map_apply,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, rootsOfUnityInverseImageComparison_comp a b ba hba,
    Iso.hom_inv_id_app_assoc]

end Stacks.EtaleCohomology

end
