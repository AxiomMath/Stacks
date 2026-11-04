module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleDerivedTensor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Tensoring with a complex killed by a scalar

Let `P` be a K-projective complex of `Λ`-modules on which `μ ∈ Λ` acts by zero in `D(Λ)`. Then
`μ` acts by zero on `K ⊗^L_Λ P` for every `K`: multiplication by `μ` on `P` is null-homotopic,
so it is on `Tot(K ⊗ P)`. Hence `- ⊗^L_Λ P` kills every object on which some power of `μ` acts
invertibly.

## Main results

* `Stacks.ConstantModuleTensor.Q_map_totRight_smul_eq_zero`.
* `Stacks.ConstantModuleTensor.isZero_derivedTensor_obj_of_isIso_smul`: `- ⊗^L P` kills every
  object on which `μ` acts invertibly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v₁ u₁

namespace Stacks.ConstantModuleTensor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  [HasSheafify J (ModuleCat.{w} Λ)]

attribute [local instance] HasDerivedCategory.standard

/-- Multiplication by a scalar on `Tot(K ⊗ P)` is multiplication by that scalar on `K`. -/
theorem totRight_map_smul (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (μ : Λ) :
    (Stacks.DerivedTensor.totRight (sheafTensor J Λ) P).map (μ • 𝟙 K) =
      HomologicalComplex.mapBifunctorMap (𝟙 K) (μ • 𝟙 P) (sheafTensor J Λ) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  change HomologicalComplex.ιMapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ) i₁ i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap (μ • 𝟙 K) (𝟙 P) (sheafTensor J Λ)
        (ComplexShape.up ℤ)).f j = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  refine Eq.trans ?_ (HomologicalComplex.ι_mapBifunctorMap (𝟙 K) (μ • 𝟙 P) (sheafTensor J Λ)
    (ComplexShape.up ℤ) i₁ i₂ j h).symm
  simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, sheafTensor_map_smul,
    NatTrans.app_smul, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Linear.smul_comp, Linear.comp_smul, Functor.map_smul]

/-- `Tot(- ⊗ P)` is `Λ`-linear: it carries multiplication by a scalar on `K` to multiplication
by that scalar on `Tot(K ⊗ P)`. -/
theorem totRight_map_smul_id (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (μ : Λ) :
    (Stacks.DerivedTensor.totRight (sheafTensor J Λ) P).map (μ • 𝟙 K) = μ • 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  change HomologicalComplex.ιMapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ) i₁ i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap (μ • 𝟙 K) (𝟙 P) (sheafTensor J Λ)
        (ComplexShape.up ℤ)).f j = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, sheafTensor_map_smul,
    NatTrans.app_smul, CategoryTheory.Functor.map_id, NatTrans.id_app, Linear.smul_comp,
    Category.id_comp]
  exact ((Linear.comp_smul _ _ _
    (HomologicalComplex.ιMapBifunctor K P (sheafTensor J Λ) (ComplexShape.up ℤ) i₁ i₂ j h) μ
    (𝟙 _)).trans (congrArg (μ • ·) (Category.comp_id _))).symm

variable [HasExactColimitsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ))]

omit [HasExactColimitsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ))] in
/-- If `μ` acts by zero on the K-projective complex `P` in `D(Λ)`, then multiplication by `μ`
on `Tot(K ⊗ P)` is zero in the derived category. -/
theorem Q_map_totRight_smul_eq_zero (P : CochainComplex (ModuleCat.{w} Λ) ℤ) [P.IsKProjective]
    (μ : Λ) (hμ : μ • 𝟙 (DerivedCategory.Q.obj P) = 0)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    DerivedCategory.Q.map ((Stacks.DerivedTensor.totRight (sheafTensor J Λ) P).map (μ • 𝟙 K)) =
      0 := by
  have h0 : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (μ • 𝟙 P) = 0 := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P _).1
    rw [Functor.map_zero]
    have : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (μ • 𝟙 P)) =
        (DerivedCategory.quotientCompQhIso _).hom.app P ≫ DerivedCategory.Q.map (μ • 𝟙 P) ≫
          (DerivedCategory.quotientCompQhIso _).inv.app P := by
      rw [← Category.assoc, ← NatTrans.naturality]
      simp
    rw [this, Functor.map_smul, CategoryTheory.Functor.map_id, hμ]
    simp
  have H := HomotopyCategory.homotopyOfEq _ _ (h0.trans (Functor.map_zero _ _ _).symm)
  rw [totRight_map_smul]
  refine Eq.trans (DerivedCategory.Q_map_eq_of_homotopy (h :=
    HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) H (sheafTensor J Λ) (ComplexShape.up ℤ))) ?_
  have : HomologicalComplex.mapBifunctorMap (𝟙 K) (0 : P ⟶ P) (sheafTensor J Λ)
      (ComplexShape.up ℤ) = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun j => ?_
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.zero_f_apply, HomologicalComplex.id_f, Functor.map_zero,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Limits.zero_comp, Limits.comp_zero]
  rw [this]
  exact Functor.map_zero _ _ _

omit [HasExactColimitsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ))] in
/-- **`- ⊗^L P` kills the objects on which `μ` acts invertibly**, when `μ` acts by zero on the
K-projective, K-flat complex `P`. -/
theorem isZero_derivedTensor_obj_of_isIso_smul (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    [P.IsKProjective] [Stacks.DerivedTensor.IsKFlat (sheafTensor J Λ) P]
    (μ : Λ) (hμ : μ • 𝟙 (DerivedCategory.Q.obj P) = 0)
    (N : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (hN : IsIso (μ • 𝟙 N)) :
    IsZero ((Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) P).obj N) := by
  let M := DerivedCategory.Q.objPreimage N
  let e : DerivedCategory.Q.obj M ≅ N := DerivedCategory.Q.objObjPreimageIso N
  have hsmul : μ • 𝟙 (DerivedCategory.Q.obj M) = e.hom ≫ (μ • 𝟙 N) ≫ e.inv := by
    simp
  have hiso : IsIso (μ • 𝟙 (DerivedCategory.Q.obj M)) := by
    rw [hsmul]
    infer_instance
  have hzero : (Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) P).map
      (μ • 𝟙 (DerivedCategory.Q.obj M)) = 0 := by
    have hQ : μ • 𝟙 (DerivedCategory.Q.obj M) = DerivedCategory.Q.map (μ • 𝟙 M) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    have hnat := (Stacks.DerivedTensor.derivedTensorQIso (sheafTensor J Λ) P).hom.naturality
      (μ • 𝟙 M)
    dsimp only [Functor.comp_map] at hnat
    rw [Q_map_totRight_smul_eq_zero J Λ P μ hμ M, Limits.comp_zero, ← hQ] at hnat
    rw [← cancel_mono ((Stacks.DerivedTensor.derivedTensorQIso (sheafTensor J Λ) P).hom.app M),
      hnat, Limits.zero_comp]
  exact (IsZero.of_mono_eq_zero _ hzero).of_iso
    ((Stacks.DerivedTensor.derivedTensor (sheafTensor J Λ) P).mapIso e).symm

end Stacks.ConstantModuleTensor
