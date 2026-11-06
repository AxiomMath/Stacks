module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.RingTheory.Dualizing.Complex
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange.Homothety

/-!
# The derived endomorphism object and the tensor unit

Auxiliary results for `Dualizing.polynomialBaseChange_isDualizingComplex`: an isomorphism of the
derived endomorphism object with the tensor unit makes the canonical map `R → End K` invertible,
and this condition transports along polynomial base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace Dualizing

universe u v w x

/-- A lax monoidal exact functor whose unit comparison is invertible sends the derived unit to
the derived unit. -/
private noncomputable def unitIsoMapDerivedCategory
    {R S : Type w} [CommRing R] [CommRing S] (F : ModuleCat.{w} R ⥤ ModuleCat.{w} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.LaxMonoidal]
    [IsIso (Functor.LaxMonoidal.ε F)] :
    DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} S) ℤ)) ≅
      F.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) :=
  let m : (𝟙_ (ModuleCat.{w} S)) ≅ F.obj (𝟙_ (ModuleCat.{w} R)) :=
    asIso (Functor.LaxMonoidal.ε F)
  let c : (𝟙_ (CochainComplex (ModuleCat.{w} S) ℤ)) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) :=
    ((CochainComplex.singleFunctor (ModuleCat.{w} S) 0).mapIso m) ≪≫
      ((Functor.mapCochainComplexSingleFunctor F 0).app (𝟙_ (ModuleCat.{w} R))).symm
  DerivedCategory.Q.mapIso c ≪≫
    (F.mapDerivedCategoryFactors.app
      (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))).symm

private noncomputable def restrictScalarsUnitIso
    {R S : Type w} [CommRing R] [CommRing S] (e : S ≃+* R) :
    let F := ModuleCat.restrictScalars.{w} e.toRingHom
    DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} S) ℤ)) ≅
      F.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) := by
  intro F
  letI : F.LaxMonoidal := inferInstance
  haveI : IsIso (Functor.LaxMonoidal.ε F) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hfun : (fun s : S => (Functor.LaxMonoidal.ε F).hom s) = e := by
      funext s
      exact ModuleCat.restrictScalars_η e.toRingHom s
    change Function.Bijective (fun s : S => (Functor.LaxMonoidal.ε F).hom s)
    rw [hfun]
    exact e.bijective
  exact unitIsoMapDerivedCategory F

private noncomputable def transportedEndomorphismIsoUnit
    {R : Type w} [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (hcanon : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
        K K).symm (𝟙 K))) :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{w, w} R).obj (Opposite.op K, K) ≅
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) := by
  let U := ULift.{w} R
  let e : U ≃+* R := ULift.ringEquiv
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{w, w} R
  have hLift : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction U).homZeroEquiv
        (E.functor.obj K) (E.functor.obj K)).symm (𝟙 (E.functor.obj K))) := by
    change IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction U).homZeroEquiv
        ((ModuleCat.restrictScalars.{w} e.toRingHom).mapDerivedCategory.obj K)
        ((ModuleCat.restrictScalars.{w} e.toRingHom).mapDerivedCategory.obj K)).symm
          (𝟙 ((ModuleCat.restrictScalars.{w} e.toRingHom).mapDerivedCategory.obj K)))
    exact isIso_canonicalHomothety_restrictScalars e K hK hcanon
  let m := asIso
    (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction U).homZeroEquiv
      (E.functor.obj K) (E.functor.obj K)).symm (𝟙 (E.functor.obj K)))
  change E.inverse.obj
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction U).hom.obj
        (Opposite.op (E.functor.obj K), E.functor.obj K)) ≅ _
  exact E.inverse.mapIso m.symm ≪≫ (restrictScalarsUnitIso e.symm).symm

private noncomputable def liftedEndomorphismIsoUnitOfTransported
    {R : Type w} [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (h : (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{w, w} R).obj
      (Opposite.op K, K) ≅
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) :
    let U := ULift.{w} R
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{w, w} R
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction U).hom.obj
      (Opposite.op (E.functor.obj K), E.functor.obj K) ≅
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} U) ℤ)) := by
  intro U E
  let H := (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction U).hom.obj
    (Opposite.op (E.functor.obj K), E.functor.obj K)
  change H ≅ _
  exact (E.counitIso.app H).symm ≪≫ E.functor.mapIso h ≪≫
    (restrictScalarsUnitIso (ULift.ringEquiv : U ≃+* R)).symm

private noncomputable def polynomialExtensionUnitIso
    {R : Type w} [CommRing R] :
    let f : R →+* Polynomial R := Polynomial.C
    let E := ModuleCat.extendScalars.{w, w, w} f
    letI : PreservesFiniteLimits E :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by
        rw [show f = algebraMap R (Polynomial R) from rfl,
          RingHom.flat_algebraMap_iff]
        infer_instance)
    letI : E.Additive := by
      have : PreservesColimitsOfShape (Discrete WalkingPair) E := inferInstance
      have : PreservesBinaryBiproducts E :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      exact Functor.additive_of_preservesBinaryBiproducts _
    DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} (Polynomial R)) ℤ)) ≅
      E.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) := by
  let f : R →+* Polynomial R := Polynomial.C
  let E := ModuleCat.extendScalars.{w, w, w} f
  letI : PreservesFiniteLimits E :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by
      rw [show f = algebraMap R (Polynomial R) from rfl,
        RingHom.flat_algebraMap_iff]
      infer_instance)
  letI : E.Additive := by
    have : PreservesColimitsOfShape (Discrete WalkingPair) E := inferInstance
    have : PreservesBinaryBiproducts E :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  letI : E.Monoidal := inferInstance
  exact unitIsoMapDerivedCategory E

/-- The monoidal product of the identity of `P` with a scalar multiple of the identity of the
tensor unit is that scalar multiple of the identity. Stated in the monoidal spelling `⊗ₘ`, which
is the form the comparison isomorphism's naturality produces; converting to the underlying
`mapBifunctorMap` is the one definitional step, and it is taken here rather than at the use
site so that it is paid once and in isolation. -/
private theorem tensorComplex_map_smul_unit
    {R : Type w} [CommRing R]
    (P : CochainComplex (ModuleCat.{w} R) ℤ) (r : R) :
    (𝟙 P ⊗ₘ r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) =
      r • 𝟙 (P ⊗ 𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) := by
  show HomologicalComplex.mapBifunctorMap (𝟙 P)
      (r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)))
      (moduleTensor R) (ComplexShape.up ℤ) =
    r • 𝟙 (tensorComplex P (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)))
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, HomologicalComplex.smul_f_apply,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Linear.comp_smul,
    Category.comp_id]
  have hs : ((moduleTensor R).obj (P.X i)).map
      (r • 𝟙 ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)).X j)) =
      r • 𝟙 (((moduleTensor R).obj (P.X i)).obj
        ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)).X j)) := by
    apply ModuleCat.hom_ext
    show LinearMap.lTensor (P.X i)
      (r • (LinearMap.id :
        ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)).X j) →ₗ[R]
          ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)).X j))) =
        r • LinearMap.id
    rw [LinearMap.lTensor_smul, LinearMap.lTensor_id]
  rw [hs]
  rw [Linear.smul_comp, Category.id_comp]

/-- Scalar multiples of the identity of the tensor unit are sent by the model tensor functor to
the corresponding scalar multiples of the identity, for an object of the derived category given
by an actual complex. This is the case of `modelTensor_map_smul_unit` proved directly from the
model comparison; the general case is transported along a resolution.

The naturality square of the tensor comparison is rearranged in term mode: the square's two
sides are only definitionally the shapes the rewriting lemmas expect, so `rw … at` cannot form
a type-correct motive for them, and every step is taken with an explicitly typed `congrArg`
instead. -/
private theorem modelTensor_map_smul_unit_of_Q_obj
    {R : Type w} [CommRing R]
    (P : CochainComplex (ModuleCat.{w} R) ℤ) (r : R) :
    let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
    let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
    D.tensor.map (𝟙 (DerivedCategory.Q.obj P), r • 𝟙 U) =
      r • 𝟙 (D.tensor.obj (DerivedCategory.Q.obj P, U)) := by
  intro D U
  let hunit := StacksDraft.DerivedHom.DerivedHomData.unit_kFlat (R := R)
  have hnat := D.tensorIso_naturality (𝟙 P)
    (r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) hunit hunit
  have hlin : (DerivedCategory.Q (C := ModuleCat.{w} R)).Linear R := inferInstance
  have hsrc : ((DerivedCategory.Q.map (𝟙 P) :
        DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P),
      (DerivedCategory.Q.map
        (r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) : U ⟶ U)) =
      (𝟙 (DerivedCategory.Q.obj P), r • 𝟙 U) := by
    rw [DerivedCategory.Q.map_id, Functor.Linear.map_smul,
      CategoryTheory.Functor.map_id]
  have htgt : DerivedCategory.Q.map
      (𝟙 P ⊗ₘ r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) =
      r • 𝟙 (DerivedCategory.Q.obj
        (P ⊗ 𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) := by
    rw [tensorComplex_map_smul_unit P r, Functor.Linear.map_smul,
      CategoryTheory.Functor.map_id]
  apply (cancel_mono (D.tensorIso P _ hunit).hom).mp
  calc
    D.tensor.map (𝟙 (DerivedCategory.Q.obj P), r • 𝟙 U) ≫
        (D.tensorIso P _ hunit).hom
        = D.tensor.map (DerivedCategory.Q.map (𝟙 P),
            DerivedCategory.Q.map
              (r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)))) ≫
          (D.tensorIso P _ hunit).hom :=
        congrArg
          (fun z : (DerivedCategory.Q.obj P, U) ⟶ (DerivedCategory.Q.obj P, U) =>
            D.tensor.map z ≫ (D.tensorIso P _ hunit).hom) hsrc.symm
    _ = (D.tensorIso P _ hunit).hom ≫ DerivedCategory.Q.map
          (𝟙 P ⊗ₘ r • 𝟙 (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) := hnat
    _ = (D.tensorIso P _ hunit).hom ≫
          (r • 𝟙 (DerivedCategory.Q.obj
            (P ⊗ 𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)))) :=
        congrArg
          (fun z : DerivedCategory.Q.obj
              (P ⊗ 𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⟶
              DerivedCategory.Q.obj
                (P ⊗ 𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) =>
            (D.tensorIso P _ hunit).hom ≫ z) htgt
    _ = (r • 𝟙 (D.tensor.obj (DerivedCategory.Q.obj P, U))) ≫
          (D.tensorIso P _ hunit).hom := by
        simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- Scalar multiples of the identity of the tensor unit are sent by the model tensor functor to
the corresponding scalar multiples of the identity. -/
private theorem modelTensor_map_smul_unit
    {R : Type w} [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R)) (r : R) :
    let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
    let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
    D.tensor.map (𝟙 K, r • 𝟙 U) = r • 𝟙 (D.tensor.obj (K, U)) := by
  intro D U
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hP : D.tensor.map (𝟙 (DerivedCategory.Q.obj P), r • 𝟙 U) =
      r • 𝟙 (D.tensor.obj (DerivedCategory.Q.obj P, U)) :=
    modelTensor_map_smul_unit_of_Q_obj P r
  let α : (DerivedCategory.Q.obj P, U) ⟶ (K, U) := (e.hom, 𝟙 U)
  have : IsIso α := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (D.tensor.map α) := inferInstance
  have hcomm :
      D.tensor.map α ≫ D.tensor.map (𝟙 K, r • 𝟙 U) =
        D.tensor.map (𝟙 (DerivedCategory.Q.obj P), r • 𝟙 U) ≫
          D.tensor.map α := by
    rw [← D.tensor.map_comp, ← D.tensor.map_comp]
    congr 1
    ext <;> simp [α, Linear.smul_comp]
  apply (cancel_epi (D.tensor.map α)).mp
  rw [hcomm, hP]
  simp only [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id]

private theorem modelTensor_map_smul_left_unit
    {R : Type w} [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R)) (r : R) :
    let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
    let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
    D.tensor.map (r • 𝟙 U, 𝟙 K) = r • 𝟙 (D.tensor.obj (U, K)) := by
  intro D U
  have hswap := D.tensorSwap_naturality (r • 𝟙 U) (𝟙 K)
  have hright := modelTensor_map_smul_unit K r
  apply (cancel_mono (D.tensorSwap U K).hom).mp
  rw [hswap, hright]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  have hid : (D.tensorSwap U K).hom ≫
      𝟙 (D.tensor.obj (K, U)) = (D.tensorSwap U K).hom := Category.comp_id _
  rw [hid]

private theorem homZeroEquiv_map_smul
    {R : Type w} [CommRing R]
    (K M : DerivedCategory (ModuleCat.{w} R)) (r : R)
    (a : DerivedCategory.Q.obj
      (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⟶
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).hom.obj
        (Opposite.op K, M)) :
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv K M
      (r • a) =
        r • (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
          K M a := by
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
  have hnat := D.homEquiv_naturality_left (r • 𝟙 U) a
  have hs : (r • 𝟙 U) ≫ a = r • a := by
    rw [Linear.smul_comp, Category.id_comp]
  rw [hs, modelTensor_map_smul_left_unit K r] at hnat
  simp only [Linear.smul_comp] at hnat
  show (D.tensorUnitLeft K).inv ≫ D.homEquiv U K M (r • a) =
    r • ((D.tensorUnitLeft K).inv ≫ D.homEquiv U K M a)
  rw [hnat]
  simp only [Linear.comp_smul]
  have hid : 𝟙 (D.tensor.obj (U, K)) ≫ D.homEquiv U K M a =
      D.homEquiv U K M a := Category.id_comp _
  show r • ((D.tensorUnitLeft K).inv ≫ (𝟙 (D.tensor.obj (U, K)) ≫
    D.homEquiv U K M a)) = r • ((D.tensorUnitLeft K).inv ≫
      D.homEquiv U K M a)
  rw [hid]

private noncomputable def homZeroLinearEquiv
    {R : Type w} [CommRing R]
    (K M : DerivedCategory (ModuleCat.{w} R)) :
    let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
    let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
    (U ⟶ D.hom.obj (Opposite.op K, M)) ≃ₗ[R] (K ⟶ M) := by
  intro D U
  exact { D.homZeroEquiv K M with
    map_smul' := fun r a => homZeroEquiv_map_smul K M r a }

private noncomputable def fullyFaithfulLinearEquiv
    {R : Type w} [CommRing R]
    {C : Type u} [Category C] [Preadditive C] [Linear R C]
    {D : Type v} [Category D] [Preadditive D] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] [F.Linear R] (X Y : C) :
    (X ⟶ Y) ≃ₗ[R] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv f := F.map_injective (F.map_preimage _)
  right_inv f := F.map_preimage f
  map_add' _ _ := F.map_add
  map_smul' r f := by simp

private noncomputable def derivedUnitEndLinearEquiv
    {R : Type w} [CommRing R] :
    let U := DerivedCategory.Q.obj
      (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
    (U ⟶ U) ≃ₗ[R] R := by
  intro U
  let F := DerivedCategory.singleFunctor (ModuleCat.{w} R) 0
  let V := ModuleCat.of R R
  have hU : U = F.obj V := rfl
  subst U
  let e₁ := (fullyFaithfulLinearEquiv (R := R) F V V).symm
  let e₂ : (V ⟶ V) ≃ₗ[R] (R →ₗ[R] R) :=
    ModuleCat.homLinearEquiv (M := V) (N := V) (S := R)
  exact (e₁.trans e₂).trans (LinearMap.ringLmapEquivSelf R R R)

private theorem derivedUnitEndLinearEquiv_symm_apply
    {R : Type w} [CommRing R] (r : R) :
    let U := DerivedCategory.Q.obj
      (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
    (derivedUnitEndLinearEquiv (R := R)).symm r = r • 𝟙 U := by
  intro U
  let e := derivedUnitEndLinearEquiv (R := R)
  apply e.injective
  rw [e.apply_symm_apply, map_smul]
  have h₁ : e (𝟙 U) = 1 := by
    let F := DerivedCategory.singleFunctor (ModuleCat.{w} R) 0
    let V := ModuleCat.of R R
    have hpre : F.preimage (𝟙 U) = 𝟙 V := by
      show F.preimage (𝟙 (F.obj V)) = 𝟙 V
      exact F.preimage_id
    show (LinearMap.ringLmapEquivSelf R R R)
      (ModuleCat.homLinearEquiv (S := R)
        ((fullyFaithfulLinearEquiv (R := R)
          F V V).symm (𝟙 U))) = 1
    simp [fullyFaithfulLinearEquiv, LinearMap.ringLmapEquivSelf_apply, hpre]
  rw [h₁, smul_eq_mul, mul_one]

private theorem bijective_algebraMap_of_linearEquiv_self
    {R : Type w} {S : Type x} [CommRing R] [Ring S] [Algebra R S]
    (e : R ≃ₗ[R] S) : Function.Bijective (algebraMap R S) := by
  by_cases h : Subsingleton R
  · let : Subsingleton R := h
    have : Subsingleton S := by
      have hz : (0 : R) = 1 := Subsingleton.elim _ _
      have hz' : (0 : S) = 1 := by
        simpa using congrArg (algebraMap R S) hz
      exact subsingleton_of_zero_eq_one hz'
    constructor
    · intro _ _ _
      exact Subsingleton.elim _ _
    · intro s
      exact ⟨0, Subsingleton.elim _ _⟩
  · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
    let : Module.Free R S := Module.Free.of_equiv' (by infer_instance : Module.Free R R) e
    have hfin : Module.finrank R S = 1 := by
      rw [← e.finrank_eq]
      exact Module.finrank_self R
    exact Module.Free.bijective_algebraMap_of_finrank_eq_one hfin

theorem isIso_canonicalHomothety_of_endomorphism_iso_unit
    {R : Type w} [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (h : (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).hom.obj
      (Opposite.op K, K) ≅
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))) :
    IsIso (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
      K K).symm (𝟙 K)) := by
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ))
  let H := D.hom.obj (Opposite.op K, K)
  let e₁ : (U ⟶ H) ≃ₗ[R] (U ⟶ U) :=
    { toFun := fun a => a ≫ h.hom
      invFun := fun a => a ≫ h.inv
      left_inv := by intro a; simp [Category.assoc]
      right_inv := by intro a; simp [Category.assoc]
      map_add' := by intro a b; simp [Preadditive.add_comp]
      map_smul' := by intro r a; simp [Linear.smul_comp] }
  let e₂ := derivedUnitEndLinearEquiv (R := R)
  let e₃ : (U ⟶ H) ≃ₗ[R] End K := (homZeroLinearEquiv K K).trans End.linearEquiv.symm
  let eEnd : R ≃ₗ[R] (End K) := (e₂.symm.trans e₁.symm).trans e₃
  have hb : Function.Bijective (algebraMap R (End K)) :=
    bijective_algebraMap_of_linearEquiv_self eEnd
  let c := (D.homZeroEquiv K K).symm (𝟙 K)
  have hc : e₃ c = 1 := by
    show End.linearEquiv.symm (D.homZeroEquiv K K c) = 1
    rw [AddEquiv.apply_symm_apply]
    rfl
  have hcomp (f : U ⟶ U) : e₃ (f ≫ c) =
      (algebraMap R (End K)) (e₂ f) := by
    have hf : f = (e₂ f) • 𝟙 U := by
      calc
        f = e₂.symm (e₂ f) := (e₂.symm_apply_apply f).symm
        _ = (e₂ f) • 𝟙 U := derivedUnitEndLinearEquiv_symm_apply (e₂ f)
    calc
      e₃ (f ≫ c) = e₃ ((e₂ f) • c) := by
        apply congrArg e₃
        calc
          f ≫ c = ((e₂ f) • 𝟙 U) ≫ c := congrArg (fun t => t ≫ c) hf
          _ = (e₂ f) • c := by rw [Linear.smul_comp, Category.id_comp]
      _ = (e₂ f) • (1 : End K) := by rw [map_smul, hc]
      _ = (algebraMap R (End K)) (e₂ f) := by
        rw [Algebra.algebraMap_eq_smul_one]
  have hpost : Function.Bijective (fun f : U ⟶ U => f ≫ c) := by
    constructor
    · intro f g hfg
      apply e₂.injective
      apply hb.1
      calc
        (algebraMap R (End K)) (e₂ f) = e₃ (f ≫ c) := (hcomp f).symm
        _ = e₃ (g ≫ c) := congrArg e₃ hfg
        _ = (algebraMap R (End K)) (e₂ g) := hcomp g
    · intro q
      obtain ⟨r, hr⟩ := hb.2 (e₃ q)
      refine ⟨e₂.symm r, ?_⟩
      apply e₃.injective
      rw [hcomp, e₂.apply_symm_apply, hr]
  let d : U ⟶ U := c ≫ h.hom
  obtain ⟨f, hf⟩ := hpost.2 h.inv
  change f ≫ c = h.inv at hf
  have hleft : f ≫ d = 𝟙 U := by
    show f ≫ (c ≫ h.hom) = 𝟙 U
    rw [← Category.assoc, hf]
    simp
  have hinjD : Function.Injective (fun f : U ⟶ U => f ≫ d) := by
    intro f g hfg
    apply hpost.1
    apply (cancel_mono h.hom).mp
    simpa only [d, Category.assoc] using hfg
  have hright : d ≫ f = 𝟙 U := by
    apply hinjD
    calc
      (d ≫ f) ≫ d = d ≫ (f ≫ d) := by rw [Category.assoc]
      _ = d := by rw [hleft]; simp
      _ = (𝟙 U) ≫ d := by simp
  let i : U ≅ U := ⟨d, f, hright, hleft⟩
  have : IsIso (c ≫ h.hom) := by
    show IsIso d
    exact i.isIso_hom
  exact IsIso.of_isIso_comp_right c h.hom

private theorem isDualizingComplex_of_canonicalHomothety
    {R : Type w} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{w} R))
    (hI : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (hH : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K))
    (hcanon : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
        K K).symm (𝟙 K))) :
    IsDualizingComplex K := by
  refine ⟨hI, hH, ?_⟩
  intro I hrep hinj hbound
  obtain ⟨eI⟩ := hrep
  obtain ⟨a, b, hge, hle⟩ := hbound
  let : I.IsStrictlyGE a := hge
  let : ∀ i, Injective (I.X i) := hinj
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have hQI : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
        (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj I)).symm
          (𝟙 (DerivedCategory.Q.obj I))) :=
    isIso_canonicalHomothety_of_iso eI.symm hcanon
  exact (isIso_homZeroEquiv_symm_id_iff I).1 hQI

end Dualizing
