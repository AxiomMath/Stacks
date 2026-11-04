module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance

/-!
# The identity functor on bounded below derived categories, on the image of the localization

`CategoryTheory.Functor.mapDerivedCategoryPlusIdIso : (𝟭 A).mapDerivedCategoryPlus ≅ 𝟭` is, at the
image of a bounded below complex, the factorization of `(𝟭 A).mapDerivedCategoryPlus` through the
localization.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryPlusIdIso_hom_app_Qh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The unbounded identity comparison `Stacks.Homology.mapDerivedCategoryIdIso` at the image of a
complex of the homotopy category. -/
lemma _root_.Stacks.Homology.mapDerivedCategoryIdIso_hom_app_Qh_quotient
    (K : CochainComplex A ℤ) :
    (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      (𝟭 A).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) := by
  have hQ : (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app K) := by
    simp [Stacks.Homology.mapDerivedCategoryIdIso, Localization.liftNatIso_hom,
      Localization.liftNatTrans_app]
    rfl
  have n := (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).hom.app K)
  have hid : (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
    ext n; simp
  have hq : DerivedCategory.Qh.map
      (((𝟭 A).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hB : (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K := by
    rw [hQ, hid]
    exact (whisker_eq _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  simp only [Functor.id_map, Functor.comp_obj] at n
  have n' : (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      ((𝟭 A).mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
        (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)).hom.app (DerivedCategory.Q.obj K)) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app K := by
    rw [n, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, hq]
  refine n'.trans ?_
  rw [hB, Category.assoc]
  exact whisker_eq _ (whisker_eq _ (Category.comp_id _).symm)

/-- **`mapDerivedCategoryPlusIdIso` at the image of a bounded below complex** is the
factorization of `(𝟭 A).mapDerivedCategoryPlus` through the localization. -/
lemma mapDerivedCategoryPlusIdIso_hom_app_Qh (N : HomotopyCategory.Plus A) :
    (mapDerivedCategoryPlusIdIso (A := A)).hom.app (DerivedCategory.Plus.Qh.obj N) =
      (𝟭 A).mapDerivedCategoryPlusFactorsh.hom.app N := by
  apply DerivedCategory.Plus.ι.map_injective
  have h : Functor.whiskerRight (mapDerivedCategoryPlusIdIso (A := A)).hom DerivedCategory.Plus.ι =
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
          (Stacks.Homology.mapDerivedCategoryIdIso (C₁ := A)) ≪≫
        Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm).hom :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).map_preimage _
  have h' := NatTrans.congr_app h (DerivedCategory.Plus.Qh.obj N)
  simp only [Functor.whiskerRight_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.symm_hom,
    Functor.leftUnitor_inv_app, Category.comp_id] at h'
  rw [h']
  obtain ⟨⟨K⟩, hK⟩ := N
  exact (Category.comp_id _).trans (Stacks.Homology.mapDerivedCategoryIdIso_hom_app_Qh_quotient K)

end CategoryTheory.Functor
