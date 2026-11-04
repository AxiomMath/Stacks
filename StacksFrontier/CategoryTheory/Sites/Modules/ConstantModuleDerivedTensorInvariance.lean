module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorTotalComparison
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# The derived tensor product depends only on the class of the module complex

Let `P` and `R` be K-projective complexes of `Λ`-modules which are K-flat for the tensor product
with sheaves of `Λ`-modules. If `P` and `R` are isomorphic in `D(Λ)`, then `K ⊗^L_Λ P ≅ K ⊗^L_Λ R`
for every object `K` of the derived category of sheaves: a quasi-isomorphism between K-projective
complexes is a homotopy equivalence, and `Tot(K ⊗_Λ -)` carries homotopy equivalences to homotopy
equivalences.

In particular `K ⊗^L_Λ M`, computed with the chosen projective resolution of `M`, may be computed
with any bounded complex of finitely generated projective modules representing a perfect module
`M`.

## Main results

* `Stacks.ConstantModuleTensor.nonempty_derivedTensor_obj_iso`: for K-projective, K-flat
  complexes `P` and `R` isomorphic in `D(Λ)`, `K ⊗^L_Λ P ≅ K ⊗^L_Λ R` for every `K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁

namespace Stacks.ConstantModuleTensor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {Λ : Type w} [CommRing Λ]
  [HasSheafify J (ModuleCat.{w} Λ)]

omit [HasSheafify J (ModuleCat.{w} Λ)] in
/-- `Tot(K ⊗_Λ -)` applied to a composite `φ ≫ φ'` of morphisms of complexes of `Λ`-modules is
the composite of the induced morphisms. -/
@[reassoc]
theorem mapBifunctorMap_id_comp (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    [HasSheafify J (ModuleCat.{w} Λ)] {P P' P'' : CochainComplex (ModuleCat.{w} Λ) ℤ}
    (φ : P ⟶ P') (φ' : P' ⟶ P'') :
    HomologicalComplex.mapBifunctorMap (𝟙 K) (φ ≫ φ') (sheafTensor J Λ) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 K) φ (sheafTensor J Λ) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K) φ' (sheafTensor J Λ) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun n =>
    HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, HomologicalComplex.comp_f, Functor.map_comp, Category.assoc]

variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))] [HasDerivedCategory (ModuleCat.{w} Λ)]

/-- `Tot(K ⊗_Λ -)` carries a homotopy equivalence to an isomorphism in the derived category. -/
def totalComplexIsoOfHomotopyEquiv (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    {P R : CochainComplex (ModuleCat.{w} Λ) ℤ} (E : HomotopyEquiv P R) :
    DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K P (sheafTensor J Λ)
        (ComplexShape.up ℤ)) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K R (sheafTensor J Λ)
        (ComplexShape.up ℤ)) where
  hom := DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 K) E.hom (sheafTensor J Λ) (ComplexShape.up ℤ))
  inv := DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 K) E.inv (sheafTensor J Λ) (ComplexShape.up ℤ))
  hom_inv_id := by
    rw [← Functor.map_comp, ← mapBifunctorMap_id_comp, DerivedCategory.Q_map_eq_of_homotopy (h :=
      HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) E.homotopyHomInvId (sheafTensor J Λ)
        (ComplexShape.up ℤ)), mapBifunctorMap_id_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, ← mapBifunctorMap_id_comp, DerivedCategory.Q_map_eq_of_homotopy (h :=
      HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) E.homotopyInvHomId (sheafTensor J Λ)
        (ComplexShape.up ℤ)), mapBifunctorMap_id_id, CategoryTheory.Functor.map_id]

/-- **`K ⊗^L_Λ P` depends only on the class of `P` in `D(Λ)`**, for K-projective and K-flat
complexes `P`, `R`. -/
theorem nonempty_derivedTensor_obj_iso (P R : CochainComplex (ModuleCat.{w} Λ) ℤ)
    [P.IsKProjective] [R.IsKProjective] [Stacks.DerivedTensor.IsKFlat (sheafTensor J Λ) P]
    [Stacks.DerivedTensor.IsKFlat (sheafTensor J Λ) R]
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj R)
    (N : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    Nonempty ((Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) P).obj N ≅
      (Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) R).obj N) := by
  obtain ⟨χ, hχ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj R)).2
      ((DerivedCategory.quotientCompQhIso _).hom.app P ≫ e.hom ≫
        (DerivedCategory.quotientCompQhIso _).inv.app R)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective χ
  have hφ : QuasiIso φ := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    have h := DerivedCategory.quotientCompQhIso_hom_naturality φ
    rw [hχ] at h
    have : DerivedCategory.Q.map φ = e.hom := by
      simpa using h.symm
    rw [this]
    infer_instance
  obtain ⟨E, hE⟩ := (CochainComplex.IsKProjective.quasiIso_iff φ).1 hφ
  let N' := DerivedCategory.Q.objPreimage N
  let eN : DerivedCategory.Q.obj N' ≅ N := DerivedCategory.Q.objObjPreimageIso N
  exact ⟨(Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) P).mapIso eN.symm ≪≫
    Stacks.DerivedTensor.derivedTensorObjIso (sheafTensor J Λ) P N' ≪≫
    totalComplexIsoOfHomotopyEquiv J N' E ≪≫
    (Stacks.DerivedTensor.derivedTensorObjIso (sheafTensor J Λ) R N').symm ≪≫
    (Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) R).mapIso eN⟩

end Stacks.ConstantModuleTensor
