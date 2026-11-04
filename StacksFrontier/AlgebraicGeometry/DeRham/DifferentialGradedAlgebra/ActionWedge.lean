module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionTotalComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity

/-!
# The action of the relative de Rham complex on itself

The action `Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` of the regular right differential graded module of the
relative de Rham complex is its wedge product, read on the extensions by zero to `ℤ`-indexed
complexes.

## Main results

* `AlgebraicGeometry.SheafOfModules.dgAction_regular_deRham`: the action of the regular
  differential graded module of `deRhamDifferentialGradedAlgebra B D` is
  `multiplicationInt (wedgeProduct B D)`.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace ComplexShape
open scoped TensorProduct
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- An `eqToHom` between sheaves of modules does not move local sections, up to transport. -/
private theorem eqToHom_val_app_heq' {P Q : _root_.SheafOfModules.{u} (ringSheaf A)} (h : P = Q)
    (U : (Opens X.carrier)ᵒᵖ) (x : P.val.obj U) : HEq ((eqToHom h).val.app U x) x := by
  subst h
  rfl

/-- The identification of a term of an extension by zero with the original term does not move
local sections, up to transport. -/
private theorem extendXIso_hom_val_app_heq
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ) {i : ℕ} {i' : ℤ}
    (h : embeddingUpNat.f i = i') (U : (Opens X.carrier)ᵒᵖ)
    (x : ((K.extend embeddingUpNat).X i').val.obj U) :
    HEq x ((K.extendXIso embeddingUpNat h).hom.val.app U x) := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom]
  exact (eqToHom_val_app_heq' _ U x).symm

private theorem extendXIso_inv_val_app_heq
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ) {i : ℕ} {i' : ℤ}
    (h : embeddingUpNat.f i = i') (U : (Opens X.carrier)ᵒᵖ) (x : (K.X i).val.obj U) :
    HEq ((K.extendXIso embeddingUpNat h).inv.val.app U x) x := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.inv]
  exact eqToHom_val_app_heq' _ U x

/-- **The action of the relative de Rham complex on itself is the wedge product**: the action
`Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` of the regular right differential graded module is the wedge product of
Tag 0FM2, read on the extensions by zero to `ℤ`-indexed complexes. -/
theorem dgAction_regular_deRham :
    dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule
      (deRhamDifferentialGradedAlgebra B D)) = multiplicationInt (wedgeProduct B D) := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
  have hij' : i + j = k := hij
  by_cases hneg : i < 0 ∨ j < 0
  · exact (HomologicalComplex.MapBifunctorExtend.isZero_summand (sheafTensor A)
      (deRhamComplex B D) (deRhamComplex B D) i j hneg).eq_of_src _ _
  · push Not at hneg
    obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hneg.1
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hneg.2
    obtain rfl : k = ((p + q : ℕ) : ℤ) := by omega
    let K := deRhamComplex B D
    have hR : HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat) (K.extend embeddingUpNat)
          (sheafTensor A) (ComplexShape.up ℤ) p q ((p + q : ℕ) : ℤ) hij ≫
          (multiplicationInt (wedgeProduct B D)).f ((p + q : ℕ) : ℤ) =
        ((sheafTensor A).map
            (K.extendXIso embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp)).hom).app _ ≫
          ((sheafTensor A).obj (K.X p)).map
            (K.extendXIso embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp)).hom ≫
          HomologicalComplex.ιMapBifunctor K K (sheafTensor A) (ComplexShape.up ℕ) p q (p + q) rfl ≫
          (wedgeProduct B D).f (p + q) ≫
          (K.extendXIso embeddingUpNat (i' := ((p + q : ℕ) : ℤ)) (i := p + q) (by simp)).inv := by
      unfold multiplicationInt
      have h1 := HomologicalComplex.ι_mapBifunctorExtendHom_f (sheafTensor A) K K (p + q) p q hij
      have h2 := HomologicalComplex.extendMap_f (wedgeProduct B D) embeddingUpNat (i := p + q)
        (i' := ((p + q : ℕ) : ℤ)) rfl
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) h1).trans ?_
      refine (congrArg (_ ≫ ·) h2).trans ?_
      simp only [Category.assoc]
      refine congrArg (fun t => _ ≫ _ ≫ _ ≫ t) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ _) (Iso.inv_hom_id _)).trans (Category.id_comp _)
    refine Eq.trans ?_ hR.symm
    refine (ι_dgActionDesc _ p q ((p + q : ℕ) : ℤ) hij).trans ?_
    refine sheafTensor_hom_ext fun U x y => ?_
    let e₁ := K.extendXIso embeddingUpNat (i' := (p : ℤ)) (i := p) (by simp)
    let e₂ := K.extendXIso embeddingUpNat (i' := (q : ℤ)) (i := q) (by simp)
    refine eq_of_heq (HEq.trans (b := formProduct B p q U (e₁.hom.val.app U x)
      (e₂.hom.val.app U y)) ?_ ?_)
    · refine (heq_of_eq (congrArg (fun z => ((deRhamDifferentialGradedAlgebra B D).complex.XIsoOfEq
        hij).hom.val.app U z) (dgActionComponent_unit_apply
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule
            (deRhamDifferentialGradedAlgebra B D)) p q U x y))).trans ?_
      refine (heq_of_eq (XIsoOfEq_hom_val_app _ hij U _)).trans ?_
      refine (_root_.SheafOfModules.gradedCast_heq _ _ _).trans ?_
      exact deRhamDifferentialGradedAlgebra_mul B D p q U x y _ _
        (extendXIso_hom_val_app_heq K _ U x) (extendXIso_hom_val_app_heq K _ U y)
    · refine HEq.symm ?_
      refine (extendXIso_inv_val_app_heq K _ U _).trans ?_
      have R1 := tensorFunctor_map_unit_apply (A := A) (N := (K.extend embeddingUpNat).X q)
        e₁.hom U x y
      have R2 := tensorFunctor_obj_map_unit_apply (A := A) (M := K.X p) e₂.hom U
        (e₁.hom.val.app U x) y
      refine (heq_of_eq (congrArg (fun z => (HomologicalComplex.ιMapBifunctor K K (sheafTensor A)
        (up ℕ) p q (p + q) rfl ≫ (wedgeProduct B D).f (p + q)).val.app U z)
          ((congrArg (fun z => (((sheafTensor A).obj (K.X p)).map e₂.hom).val.app U z) R1).trans
            R2))).trans ?_
      exact wedgeProduct_summand_unit_apply B D p q U _ _

end AlgebraicGeometry.SheafOfModules
