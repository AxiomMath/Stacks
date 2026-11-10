module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionPointProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.ProjectionMapComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointProjectionFormulaBoundedBelow.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageBoundedBelowSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Examples
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection

/-!
# The projection formula to a separably closed point, on bounded below objects over `ℤ`

Let `k` be a separably closed field and `π : X ⟶ Spec k` a quasi-compact and quasi-separated
morphism. For `E ∈ D⁺(X_étale)` and `K ∈ D⁺(Spec(k)_étale) = D⁺(ℤ)` the canonical map of
Cohomology on Sites, Section 21.50 ([Stacks, Tag 0943]),

`Rπ_*E ⊗^L_ℤ K ⟶ Rπ_*(E ⊗^L_ℤ π^{-1}K)`,

is an isomorphism. Through `D(Spec(k)_étale) = D(ℤ)` this is
`RΓ(X, E ⊗^L_ℤ K̲) = RΓ(X, E) ⊗^L_ℤ K`, the statement of [Stacks, Tag 0F0E] for a
quasi-compact and quasi-separated scheme over a separably closed field. It is the input of the
proofs of [Stacks, Tag 0F0F] (at the geometric fibres) and of [Stacks, Tag 0F14] (1).

## The proof

The dévissage of `Stacks.EtaleCohomology.PointProjectionFormulaBoundedBelow.isIso_app_of_isGE`
in the variable `K`, through `D(ℤ) ≌ D(Spec(k)_étale)`: `ℤ` has no `Ext²`, the map is
invertible at the shifts of `ℤ` (the abstract projection formula,
`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_unitShift`), the
source commutes with all direct sums, and the target commutes with the direct sums of families
with a common lower bound, as follows. `π^{-1}` and `E ⊗^L -` commute with direct sums; for a
module `A` placed in degree `i`, `E ⊗^L π^{-1}A[-i]` lies in degrees `≥ a + i - 1` when `E` lies
in degrees `≥ a` (a projective resolution of `A` of length one,
`Stacks.EtaleCohomology.PointProjectionFormulaBoundedBelow.isGE_obj_single`); and `Rπ_*`
commutes with direct sums of families with a common lower bound ([Stacks, Tag 0GIW],
`Stacks.EtaleCohomology.preservesColimit_of_isGE_of_isRightDerivedFunctor`, whose input
[Stacks, Tag 09Z1] holds for `π` quasi-compact and quasi-separated).

This replaces the source's reduction through stupid truncations of a torsion-free
representative of `K` and filtered colimits of free modules by the splitting of a bounded below
complex of abelian groups into its cohomology groups; no finiteness of cohomological dimension is
needed.

## Main results

* `Stacks.EtaleCohomology.isIso_projectionFormulaMap_of_isGE_of_isSepClosed`: on the constant
  ringed topoi.
* `Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_of_isGE_of_isSepClosed`: on
  `D(X_étale, ℤ)`.

## References

* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
* [Stacks Project, Tag 0GIW](https://stacks.math.columbia.edu/tag/0GIW)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

/- The statements below are about `D(X_étale, ℤ̲)` in the model of `etaleDerivedEquivalence`,
`HasDerivedCategory.standard`; the locally small model of sheaves of modules would otherwise be
found first. -/

universe u

namespace Stacks.EtaleCohomology

open StacksDraft.InjectiveDimension in
/-- `Ext²` vanishes between any two abelian groups. -/
theorem ext_two_eq_zero_int (A B : ModuleCat.{u + 1} ℤ) (e : Abelian.Ext.{u + 1} B A 2) :
    e = 0 :=
  have := (dedekindDomain_ideal_projective_and_bounded_complex_splitting.{0, u + 1} ℤ).2.2.2.1
    B A 2 le_rfl
  Subsingleton.elim _ _

/-- The identification `D(X_étale, ℤ) ≌ D(X_étale, ℤ̲)` preserves lower bounds, backwards. -/
theorem isGE_etaleDerivedEquivalence_inverse_obj {X : Scheme.{u}}
    (W : DerivedCategory (EtaleRingedModules.{u, 0} ℤ X)) (a : ℤ) (hW : W.IsGE a) :
    ((etaleDerivedEquivalence.{u, 0} ℤ X).inverse.obj W).IsGE a :=
  Functor.isGE_obj_mapDerivedCategory (etaleModulesEquivalence.{u, 0} ℤ X).inverse W a hW

/-- **`Rπ_*` on the constant ringed topoi commutes with direct sums of families with a common lower
bound**, for `π` quasi-compact and quasi-separated: [Stacks, Tag 0GIW] read through
`Stacks.EtaleCohomology.etaleDerivedEquivalence`. -/
theorem preservesColimit_etaleRingedDerivedPushforward_of_isGE {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {J : Type (u + 1)}
    (W : J → DerivedCategory (EtaleRingedModules.{u, 0} ℤ X)) (a : ℤ) (hW : ∀ j, (W j).IsGE a) :
    PreservesColimit (Discrete.functor W) (etaleRingedDerivedPushforward.{u, 0} ℤ f) := by
  let eX := etaleDerivedEquivalence.{u, 0} ℤ X
  let eY := etaleDerivedEquivalence.{u, 0} ℤ Y
  let RF := etaleModuleDerivedDirectImageUnbounded.{u, 0} ℤ f
  have : PreservesColimit (Discrete.functor fun j => eX.inverse.obj (W j)) RF :=
    preservesColimit_of_isGE_of_isRightDerivedFunctor (etaleModuleDirectImage.{u, 0} ℤ f)
      (fun p => preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage ℤ f p J) RF
      (Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit
        (etaleModuleDirectImage.{u, 0} ℤ f) RF
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} ℤ f))
      _ a fun j => isGE_etaleDerivedEquivalence_inverse_obj (W j) a (hW j)
  have : PreservesColimit (Discrete.functor W ⋙ eX.inverse) RF :=
    preservesColimit_of_iso_diagram RF (K₁ := Discrete.functor fun j => eX.inverse.obj (W j))
      (K₂ := Discrete.functor W ⋙ eX.inverse) (Discrete.natIso fun _ => Iso.refl _)
  let e : eX.inverse ⋙ RF ⋙ eY.functor ≅ etaleRingedDerivedPushforward.{u, 0} ℤ f :=
    Functor.isoWhiskerLeft _ (etaleDerivedPushforwardIso.{u, 0} ℤ f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eX.counitIso _ ≪≫ Functor.leftUnitor _
  exact preservesColimit_of_natIso _ e

/-- **The projection formula to a separably closed point, on bounded below objects over `ℤ`**
(the case of [Stacks, Tag 0F0E] for a scheme over a separably closed field). Let `k` be a
separably closed field and `π : X ⟶ Spec k` a quasi-compact and quasi-separated morphism. For
`E ∈ D(X_étale, ℤ̲)` and `K ∈ D(Spec(k)_étale, ℤ̲)`, both bounded below, the map of
[Stacks, Tag 0B56] `Rπ_*E ⊗^L K ⟶ Rπ_*(E ⊗^L π^{-1}K)` along the morphism of constant ringed
topoi of `π` is an isomorphism. -/
theorem isIso_projectionFormulaMap_of_isGE_of_isSepClosed {X : Scheme.{u}}
    (k : Type u) [Field k] [IsSepClosed k] (π : X ⟶ Spec (.of k)) [QuasiCompact π]
    [QuasiSeparated π] (E : DerivedCategory (EtaleRingedModules.{u, 0} ℤ X)) (a : ℤ)
    (hE : E.IsGE a) (K : DerivedCategory (EtaleRingedModules.{u, 0} ℤ (Spec (.of k)))) (b : ℤ)
    (hK : K.IsGE b) :
    IsIso (projectionFormulaMap (etaleRingedToposHom.{u, 0} ℤ π) E K) := by
  let f := etaleRingedToposHom.{u, 0} ℤ π
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ X)
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} ℤ (Spec (.of k)))
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} ℤ)
  have := hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} f
  let TX := RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} ℤ X)
  let TY := RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} ℤ (Spec (.of k)))
  let adj := derivedAdjunction (X := TX) (Y := TY) f
  let Lπ := derivedPullback (X := TX) (Y := TY) f
  let Rπ := derivedPushforward (X := TX) (Y := TY) f
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, 0} ℤ X).O).commShift_right _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, 0} ℤ X).O).exact_right _
  let _ : Lπ.CommShift ℤ := derivedPullback_commShift f
  let _ : Lπ.IsTriangulated := derivedPullback_isTriangulated f
  let _ : Rπ.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let _ : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let _ : Rπ.IsTriangulated := adj.isTriangulated_rightAdjoint
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O).obj E ⋙ Rπ).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ (Spec (.of k))).O).obj
      (Rπ.obj E)).CommShift ℤ :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, 0} ℤ (Spec (.of k))).O).commShift_right _
  let _ : ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ (Spec (.of k))).O).obj
      (Rπ.obj E)).IsTriangulated :=
    (canonicalDerivedTensorProduct (etaleRingedSite.{u, 0} ℤ (Spec (.of k))).O).exact_right _
  let Ψ := etalePointDerived.{u, 0} ℤ k
  let T := (derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ X).O).obj E
  have hLπ : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) Lπ := fun I => by
    have := adj.leftAdjoint_preservesColimits
    infer_instance
  have hT : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) T := fun I =>
    preservesColimitsOfShape_discrete_derivedTensorProductFunctor _ I E
  have hF : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((derivedTensorProductFunctor (etaleRingedSite.{u, 0} ℤ (Spec (.of k))).O).obj
        (Rπ.obj E)) :=
    fun I => preservesColimitsOfShape_discrete_derivedTensorProductFunctor _ I _
  have hbase : PointProjectionFormulaBoundedBelow.Inv _ _ (projectionFormulaNatTrans f E) Ψ
      ((DerivedCategory.singleFunctor _ 0).obj
        (PointProjectionFormulaBoundedBelow.unitModule : ModuleCat.{u + 1} ℤ)) := fun n =>
    ((projectionFormulaNatTrans f E).isIso_app_iff_of_iso
      ((shiftFunctor _ n).mapIso (etalePointDerivedUnitIso.{u, 0} ℤ k))).2
        (isIso_projectionFormulaMap_unitShift f E n)
  -- the lower bound of `E ⊗^L π^{-1}(-)` on modules placed in one degree
  have hunit : ((Ψ ⋙ Lπ ⋙ T).obj ((DerivedCategory.singleFunctor _ 0).obj
      (PointProjectionFormulaBoundedBelow.unitModule : ModuleCat.{u + 1} ℤ))).IsGE a := by
    refine DerivedCategory.TStructure.t.isGE_of_iso (X := E) ?_ a
    exact ((canonicalDerivedTensorProduct (etaleRingedSite.{u, 0} ℤ X).O).rightUnitorNatIso
        (etaleRingedSite.{u, 0} ℤ X)).symm.app E ≪≫
      T.mapIso ((shiftFunctorZero _ ℤ).symm.app _ ≪≫ (derivedPullbackUnitShiftIso f 0).symm ≪≫
        Lπ.mapIso ((shiftFunctorZero _ ℤ).app _ ≪≫ (etalePointDerivedUnitIso.{u, 0} ℤ k).symm))
  have hG : ∀ (J : Type (u + 1)) (i : J → ℤ) (A : J → ModuleCat.{u + 1} ℤ) (c : ℤ),
      (∀ j, c ≤ i j) → ∀ n : ℤ, PreservesColimit
        (Discrete.functor fun j => (Ψ.obj ((DerivedCategory.singleFunctor _ (i j)).obj (A j)))⟦n⟧)
        (Lπ ⋙ T ⋙ Rπ) := by
    intro J i A c hc n
    let W := fun j => (Ψ.obj ((DerivedCategory.singleFunctor _ (i j)).obj (A j)))⟦n⟧
    have hb : ∀ j, ((Lπ ⋙ T).obj (W j)).IsGE (a + c - 1 - n) := fun j => by
      have := PointProjectionFormulaBoundedBelow.isGE_obj_single (Ψ ⋙ Lπ ⋙ T) a hunit
        ext_two_eq_zero_int.{u} (A j) (i j)
      have := DerivedCategory.TStructure.t.isGE_shift
        ((Ψ ⋙ Lπ ⋙ T).obj ((DerivedCategory.singleFunctor _ (i j)).obj (A j)))
        (a + i j - 1) n (a + i j - 1 - n) (by omega)
      have : ((Lπ ⋙ T).obj (W j)).IsGE (a + i j - 1 - n) :=
        DerivedCategory.TStructure.t.isGE_of_iso
          (X := ((Ψ ⋙ Lπ ⋙ T).obj ((DerivedCategory.singleFunctor _ (i j)).obj (A j)))⟦n⟧)
          (((Lπ ⋙ T).commShiftIso n).app _).symm _
      exact DerivedCategory.TStructure.t.isGE_of_ge _ _ (a + i j - 1 - n) (by linarith [hc j])
    have := hLπ J
    have := hT J
    have : PreservesColimit ((Discrete.functor W ⋙ Lπ) ⋙ T)
        (etaleRingedDerivedPushforward.{u, 0} ℤ π) :=
      have := preservesColimit_etaleRingedDerivedPushforward_of_isGE π
        (fun j => (Lπ ⋙ T).obj (W j)) _ hb
      preservesColimit_of_iso_diagram _ (K₁ := Discrete.functor fun j => (Lπ ⋙ T).obj (W j))
        (K₂ := (Discrete.functor W ⋙ Lπ) ⋙ T) (Discrete.natIso fun _ => Iso.refl _)
    change PreservesColimit (Discrete.functor W) (Lπ ⋙ T ⋙ etaleRingedDerivedPushforward.{u, 0} ℤ π)
    infer_instance
  let e := etalePointDerivedEquivalence.{u, 0} ℤ k
  have hM : (e.inverse.obj K).IsGE b :=
    Functor.isGE_obj_mapDerivedCategory (etalePointModuleEquivalence.{u, 0} ℤ k).inverse K b hK
  exact ((projectionFormulaNatTrans f E).isIso_app_iff_of_iso
    ((shiftFunctorZero _ ℤ).app _ ≪≫ e.counitIso.app K)).1
      (PointProjectionFormulaBoundedBelow.isIso_app_of_isGE (R := ℤ)
        (α := projectionFormulaNatTrans f E) (Ψ := Ψ) hF hG hbase ext_two_eq_zero_int.{u}
        (e.inverse.obj K) b 0)

/-- **The projection formula to a separably closed point, on bounded below objects over `ℤ`**, on
`D(X_étale, ℤ)`: for `π : X ⟶ Spec k` quasi-compact and quasi-separated, `k` separably closed,
and `E`, `K` bounded below, the projection map `Rπ_*E ⊗^L K ⟶ Rπ_*(E ⊗^L π^{-1}K)` is an
isomorphism. -/
theorem isIso_etalePushforwardProjectionMap_of_isGE_of_isSepClosed {X : Scheme.{u}}
    (k : Type u) [Field k] [IsSepClosed k] (π : X ⟶ Spec (.of k)) [QuasiCompact π]
    [QuasiSeparated π] (E : DerivedCategory (EtaleModules.{u, 0} ℤ X)) (a : ℤ) (hE : E.IsGE a)
    (K : DerivedCategory (EtaleModules.{u, 0} ℤ (Spec (.of k)))) (b : ℤ) (hK : K.IsGE b) :
    IsIso (etalePushforwardProjectionMap.{u, 0} ℤ π E K) :=
  (isIso_etalePushforwardProjectionMap_iff ℤ π E K).2
    (isIso_projectionFormulaMap_of_isGE_of_isSepClosed k π _ a
      (Functor.isGE_obj_mapDerivedCategory (etaleModulesEquivalence.{u, 0} ℤ X).functor E a hE) _ b
      (Functor.isGE_obj_mapDerivedCategory
        (etaleModulesEquivalence.{u, 0} ℤ (Spec (.of k))).functor K b hK))

end Stacks.EtaleCohomology

end
