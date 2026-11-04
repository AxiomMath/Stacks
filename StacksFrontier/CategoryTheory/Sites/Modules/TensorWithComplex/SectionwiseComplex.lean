module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseTensor
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseTensor

/-!
# The sectionwise tensor complex and the evaluation of the regular module

Part of `StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex` (see there for the overview).
This file constructs the differential of the sectionwise tensor product, obeying the signed
Leibniz rule, assembles the complex of presheaves `M ⊗_E K(-)`, and builds the sectionwise
evaluation map from the tensor product of the regular module `E = Hom(K, K)` with `K` to `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open DifferentialGraded DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o r i

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

attribute [local instance]
  instAdditiveSheafOfModulesCRingSheafOPresheafOfModulesObjFunctorOppositeRingCatIsSheafJForget

-- `PresheafOfModules.map` lands in `ModuleCat.restrictScalars`, whose carrier is the underlying
-- module; unfolding it is what lets the sectionwise rewrite lemmas below match.
attribute [local implicit_reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]

section


private lemma endomorphismAction_d
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (U : X.Cᵒᵖ) (n q : ℤ)
    (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n)
    (y : tensorSections.{u, v, w, t, s} X K U q) :
    ((((liftComplex.{u, v, w, t, s} X K).d (q + n) (q + (n + 1))).val.app U)
      (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y)) =
    (((((Rep.{u, v, w, t, s, o} X R K).algebraHom (n + 1)
      ⟨(Rep.{u, v, w, t, s, o} X R K).algebra.d a,
        (Rep.{u, v, w, t, s, o} X R K).algebra.d_mem n a a.property⟩).v q
          (q + (n + 1)) (by omega)).val.app U) y) +
    (n.negOnePow : ℤ) •
      (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v (q + 1)
          (q + (n + 1)) (by omega)).val.app U)
        ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)) := by
  have hd := congrArg
    (fun f => ((f.v q (q + (n + 1)) (by omega)).val.app U) y)
    ((Rep.{u, v, w, t, s, o} X R K).algebra_d n a)
  rw [CochainComplex.dgCategoryLinear_d_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
    ((Rep.{u, v, w, t, s, o} X R K).algebraHom n a) q (q + (n + 1))
      (by omega) (q + n) (q + 1) (by omega) (by omega)] at hd
  rw [Units.smul_def] at hd
  simp only [SheafOfModules.add_val, SheafOfModules.comp_val,
    PresheafOfModules.add_app, PresheafOfModules.comp_app] at hd
  rw [sheafModule_zsmul_val] at hd
  simp only [PresheafOfModules.zsmul_app, 
    ModuleCat.hom_add, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply] at hd
  rw [Int.negOnePow_succ] at hd
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply, 
    ] at hd
  rw [Units.val_neg, neg_smul] at hd
  rw [← sub_eq_add_neg] at hd
  exact (sub_eq_iff_eq_add).mp hd.symm

private noncomputable def tensorDifferentialBalanced
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d
      (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U (d + 1))) where
  toFun p q h :=
    ((tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) (p + 1) q
      (by omega)).comp
        ((M.gradedDifferential p).toAddMonoidHom.toIntLinearMap)) +
    (p.negOnePow : ℤ) •
      ((tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p (q + 1)
        (by omega)).compl₂
        ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U).hom.restrictScalars ℤ))
  map_smul := by
    intro p q h x a y
    simp only [LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.compl₂_apply]
    have hd :
        ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U).hom.restrictScalars ℤ)
            (a • y) =
          a • ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U).hom.restrictScalars ℤ) y
              :=
      (((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U).hom.map_smul a y
    rw [hd]
    change (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U (d + 1)).toFun
        (p + 1) q _ ((M.gradedDifferential p).toAddMonoidHom.toIntLinearMap x) (a • y) +
      (p.negOnePow : ℤ) •
        (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U (d + 1)).toFun
          p (q + 1) _ x (a • _) = _
    rw [(tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U (d + 1)).map_smul,
      (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U (d + 1)).map_smul]
    rw [smul_add, smul_comm a (p.negOnePow : ℤ)]
    rfl
  balance := by
    intro p q n h₁ h₂ x a y
    simp only [LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.compl₂_apply]
    let A := (Rep.{u, v, w, t, s, o} X R K).algebra
    let xa : M.grading (p + n) :=
      ⟨MulOpposite.op (a : A.A) • (x : M.M),
        M.smul_mem p n x a x.property a.property⟩
    let da : A.grading (n + 1) := ⟨A.d a, A.d_mem n a a.property⟩
    have hM : M.gradedDifferential (p + n) xa =
        (⟨MulOpposite.op (a : A.A) • (M.gradedDifferential p x : M.M), by
          simpa only [DifferentialGradedModule.gradedDifferential_apply,
            add_assoc, add_comm, add_left_comm] using
            M.smul_mem (p + 1) n (M.d x) a (M.d_mem p x x.property) a.property⟩ :
          M.grading (p + n + 1)) +
        (p.negOnePow : ℤ) •
          (⟨MulOpposite.op (da : A.A) • (x : M.M), by
            simpa only [add_assoc, add_comm, add_left_comm] using
              M.smul_mem p (n + 1) x (A.d a) x.property
                (A.d_mem n a a.property)⟩ : M.grading (p + n + 1)) := by
      apply Subtype.ext
      exact M.leibniz_apply p x x.property a
    change tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) ((p + n) + 1) q
        (by omega) (M.gradedDifferential (p + n) xa) y + _ = _
    rw [hM, map_add, map_zsmul]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    have hfirst := tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U (d + 1)
      (p + 1) q n (by omega) (by omega) (M.gradedDifferential p x) a y
    have hfirst' := (tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U (d + 1)
      ((p + n) + 1) ((p + 1) + n) q (by omega) (by omega) (by omega)
      (⟨MulOpposite.op (a : A.A) • (M.gradedDifferential p x : M.M), by
        simpa only [DifferentialGradedModule.gradedDifferential_apply,
          add_assoc, add_comm, add_left_comm] using
          M.smul_mem (p + 1) n (M.d x) a (M.d_mem p x x.property) a.property⟩ :
        M.grading ((p + n) + 1))
      (⟨MulOpposite.op (a : A.A) • (M.gradedDifferential p x : M.M),
        M.smul_mem (p + 1) n _ _ (M.gradedDifferential p x).property a.property⟩ :
        M.grading ((p + 1) + n)) rfl y).trans hfirst
    rw [hfirst']
    have hsecond := tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U (d + 1)
      p q (n + 1) (by omega) (by omega) x da y
    have hsecond' := (tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U (d + 1)
      ((p + n) + 1) (p + (n + 1)) q (by omega) (by omega) (by omega)
      (⟨MulOpposite.op (da : A.A) • (x : M.M), by
        simpa only [add_assoc] using
          M.smul_mem p (n + 1) x (A.d a) x.property
            (A.d_mem n a a.property)⟩ : M.grading ((p + n) + 1))
      (⟨MulOpposite.op (da : A.A) • (x : M.M),
        M.smul_mem p (n + 1) x (A.d a) x.property
          (A.d_mem n a a.property)⟩ : M.grading (p + (n + 1))) rfl y).trans hsecond
    rw [hsecond']
    have hthird := tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U (d + 1)
      p (q + 1) n (by omega) (by omega) x a
      ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)
    have hthird' :
        tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) (p + n) (q + 1)
          (by omega) xa ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) =
        tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p (q + (n + 1))
          (by omega) x
          (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v (q + 1)
            (q + (n + 1)) (by omega)).val.app U)
            ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)) := by
      convert hthird using 1
      let F : {z : ℤ // q + 1 + n = z ∧ p + z = d + 1} →
          TensorDegree.{u, v, w, t, s, o} X R K M U (d + 1) := fun z =>
        tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p z.1 z.2.2 x
          (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v (q + 1) z.1 z.2.1).val.app U)
            ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y))
      change F ⟨q + (n + 1), by omega, by omega⟩ =
        F ⟨q + 1 + n, by omega, by omega⟩
      congr 1
      apply Subtype.ext
      change q + (n + 1) = q + 1 + n
      omega
    change _ + _ + _ •
      tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) (p + n) (q + 1)
        (by omega) xa ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) = _
    rw [hthird']
    let ay := (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q
      (q + n) (by omega)).val.app U) y)
    have hright :
        tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p (q + n + 1)
          (by omega) x
          ((((liftComplex.{u, v, w, t, s} X K).d (q + n) (q + n + 1)).val.app U) ay) =
        tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p (q + (n + 1))
          (by omega) x
          ((((liftComplex.{u, v, w, t, s} X K).d (q + n) (q + (n + 1))).val.app U) ay) := by
      let F : {z : ℤ // p + z = d + 1} →
          TensorDegree.{u, v, w, t, s, o} X R K M U (d + 1) := fun z =>
        tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p z.1 z.2 x
          ((((liftComplex.{u, v, w, t, s} X K).d (q + n) z.1).val.app U) ay)
      change F ⟨q + n + 1, by omega⟩ =
        F ⟨q + (n + 1), by omega⟩
      congr 1
      apply Subtype.ext
      change q + n + 1 = q + (n + 1)
      omega
    change _ = _ + (p.negOnePow : ℤ) •
      tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p (q + n + 1)
        (by omega) x
        ((((liftComplex.{u, v, w, t, s} X K).d (q + n) (q + n + 1)).val.app U) ay)
    rw [hright]
    have hd := endomorphismAction_d.{u, v, w, t, s, o} X R K U n q a y
    rw [hd, map_add, map_zsmul, smul_add]
    simp only [Int.negOnePow_add, Units.val_mul, smul_smul, add_assoc]
    rfl

private noncomputable def tensorDegreeDifferential
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) :
    TensorDegree.{u, v, w, t, s, o} X R K M U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      TensorDegree.{u, v, w, t, s, o} X R K M U (d + 1) :=
  tensorDegreeLift.{u, v, w, t, s, o} X R K M U d _
    (tensorDifferentialBalanced.{u, v, w, t, s, o} X R K M U d)

private lemma tensorDegreeDifferential_pure
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p q : ℤ) (h : p + q = d)
    (x : M.grading p) (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U d
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
    tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) (p + 1) q (by omega)
      (M.gradedDifferential p x) y +
    (p.negOnePow : ℤ) •
      tensorDegreePure.{u, v, w, t, s, o} X R K M U (d + 1) p (q + 1) (by omega)
        x ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) := by
  exact tensorDegreeLift_pure.{u, v, w, t, s, o} X R K M U d _
    (tensorDifferentialBalanced.{u, v, w, t, s, o} X R K M U d) p q h x y

private noncomputable def tensorPresheafDifferential
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (d : ℤ) :
    tensorDegreePresheaf.{u, v, w, t, s, o} X R K M d ⟶
      tensorDegreePresheaf.{u, v, w, t, s, o} X R K M (d + 1) where
  app U := ModuleCat.ofHom (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U d)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d _
    intro p q h x y
    change tensorDegreeDifferential.{u, v, w, t, s, o} X R K M V d
        (tensorDegreeRestriction.{u, v, w, t, s, o} X R K M f d
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y)) =
      tensorDegreeRestriction.{u, v, w, t, s, o} X R K M f (d + 1)
        (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U d
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y))
    rw [tensorDegreeRestriction_pure, tensorDegreeDifferential_pure,
      tensorDegreeDifferential_pure, map_add, map_zsmul,
      tensorDegreeRestriction_pure, tensorDegreeRestriction_pure]
    have hn := (((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val).naturality f
    have he := congrArg (fun g => g y) hn
    change (((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app V)
        ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y) =
      (((liftComplex.{u, v, w, t, s} X K).X (q + 1)).val.map f)
        ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) at he
    rw [he]

private lemma tensorDegreeDifferential_comp
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) :
    (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U (d + 1)).comp
      (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U d) = 0 := by
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d
    (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U (d + 1 + 1)))
  intro p q h x y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [tensorDegreeDifferential_pure, map_add, map_zsmul,
    tensorDegreeDifferential_pure, tensorDegreeDifferential_pure]
  have hm : M.gradedDifferential (p + 1) (M.gradedDifferential p x) = 0 := by
    apply Subtype.ext
    change M.d (M.d x) = 0
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f => f (x : M.M)) M.d_comp_d
  have hk :
      (((liftComplex.{u, v, w, t, s} X K).d (q + 1) (q + 1 + 1)).val.app U)
        ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) = 0 := by
    have hdd := congrArg (fun f => (f.val.app U) y)
      ((liftComplex.{u, v, w, t, s} X K).d_comp_d q (q + 1) (q + 1 + 1))
    rw [sheafModule_zero_val] at hdd
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.hom_comp, LinearMap.comp_apply, PresheafOfModules.zero_app,
      ModuleCat.hom_zero,
      LinearMap.zero_apply] using hdd
  rw [hm, map_zero, hk, map_zero]
  simp only [smul_zero, add_zero]
  rw [Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

private noncomputable def tensorSectionwise
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) :
    CochainComplex
      (PresheafOfModules.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ :=
  CochainComplex.of (tensorDegreePresheaf.{u, v, w, t, s, o} X R K M)
    (tensorPresheafDifferential.{u, v, w, t, s, o} X R K M)
    (fun d => by
      ext U z
      change tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U (d + 1)
        (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U d z) = 0
      exact LinearMap.congr_fun
        (tensorDegreeDifferential_comp.{u, v, w, t, s, o} X R K M U d) z)

private lemma tensorDegreeMap_d
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ) (d : ℤ) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K ((dgCategory _).d f) U d (d + n + 1)
        (by omega) =
      (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U (d + n)).comp
          (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d (d + n) rfl) +
        ((n + 1).negOnePow : ℤ) •
          (tensorDegreeMap.{u, v, w, t, s, o} X R K f U (d + 1) (d + n + 1)
            (by omega)).comp
            (tensorDegreeDifferential.{u, v, w, t, s, o} X R K L U d) := by
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K L U d
    (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U (d + n + 1)))
  intro p q hpq x y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    tensorDegreeMap_pure.{u, v, w, t, s, o} X R K,
    tensorDegreeDifferential_pure.{u, v, w, t, s, o} X R K, map_add, map_zsmul]
  let z₁ : M.grading (p + (n + 1)) :=
    ⟨M.d (f.1 x), by
      simpa only [add_assoc] using
        M.d_mem (p + n) (f.1 x) (f.2.1 p x x.property)⟩
  let z₂ : M.grading (p + (n + 1)) :=
    ⟨f.1 (L.d x), by
      simpa only [add_assoc, add_left_comm, add_comm] using
        f.2.1 (p + 1) (L.d x) (L.d_mem p x x.property)⟩
  have hz : homogeneousGradedMap ((dgCategory _).d f) p x =
      z₁ + ((n + 1).negOnePow : ℤ) • z₂ := by
    apply Subtype.ext
    change (((dgCategory _).d f).1 : L.M →ₗ[ℤ] M.M) x =
      M.d (f.1 x) + ((n + 1).negOnePow : ℤ) • f.1 (L.d x)
    rw [dgCategory_d_val,
      show gradedSign R n = ((n.negOnePow : ℤ) : R) from (intCast_negOnePow n).symm]
    simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    rw [Int.negOnePow_succ, Units.val_neg, neg_smul]
    simp only [sub_eq_add_neg]
  have h₁ := tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U (d + n + 1)
    (p + n + 1) (p + (n + 1)) q (by omega) (by omega) (by omega)
    (M.gradedDifferential (p + n) (homogeneousGradedMap f p x)) z₁ rfl y
  have h₂ := tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U (d + n + 1)
    (p + 1 + n) (p + (n + 1)) q (by omega) (by omega) (by omega)
    (homogeneousGradedMap f (p + 1) (L.gradedDifferential p x)) z₂ rfl y
  rw [hz, map_add, map_smul, h₁, h₂]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [Int.negOnePow_succ, Int.negOnePow_add]
  simp only [Units.val_mul, Units.val_neg, 
    neg_mul, neg_smul, smul_add, smul_smul]
  rw [mul_comm (p.negOnePow : ℤ) (n.negOnePow : ℤ)]
  abel

private noncomputable def regularEvalMap (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (d p q : ℤ) (h : p + q = d) (U : X.Cᵒᵖ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p) :
    (((liftComplex.{u, v, w, t, s} X K).X q).val.obj U)
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      (((liftComplex.{u, v, w, t, s} X K).X d).val.obj U) :=
  ((((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) p x).v q d (by
      omega)).val.app U).hom

private lemma regularEvalMap_natural (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (d p q : ℤ) (h : p + q = d) {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
      (y :
        ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    ((liftComplex.{u, v, w, t, s} X K).X d).val.map f (regularEvalMap.{u, v, w, t, s, o} X R K d p q
      h U
        x y) =
      regularEvalMap.{u, v, w, t, s, o} X R K d p q h V x (((liftComplex.{u, v, w, t, s} X K).X
          q).val.map f y) := by
  have hn := (((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) p x).v q d
    (by
      omega)).val.naturality f
  have heq := congrArg (fun g => g y) hn
  change ((((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) p x).v q d
    (by
      omega)).val.app V).hom
      (((liftComplex.{u, v, w, t, s} X K).X q).val.map f y) =
    (((liftComplex.{u, v, w, t, s} X K).X d).val.map f)
      (((((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) p x).v q d (by
          omega)).val.app U).hom y) at heq
  exact heq.symm

private noncomputable def regularIdentity (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading 0 :=
  ((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) 0).symm
    ((CompDG.{u, v, w, t, s, o} X R).id (liftComplex.{u, v, w, t, s} X K))

private lemma regularEvalMap_identity (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (d : ℤ) (U : X.Cᵒᵖ) (y : ((liftComplex.{u, v, w, t, s} X K).X d).val.obj U) :
    regularEvalMap.{u, v, w, t, s, o} X R K d 0 d (by omega) U (regularIdentity.{u, v, w, t, s, o} X
      R K) y =
        y := by
  simp [regularEvalMap, regularIdentity, CochainComplex.dgCategoryLinear_id_v]

private lemma regularEvalMap_d (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (p q : ℤ) (U : X.Cᵒᵖ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
      (y :
        ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    (((liftComplex.{u, v, w, t, s} X K).d (p + q) (p + q + 1)).val.app U)
        (regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q (by omega) U x y) =
      regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) (p + 1) q (by omega) U
          ⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d x,
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d_mem p x
                x.property⟩ y +
        (p.negOnePow : ℤ) •
          regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) p (q + 1) (by omega) U x
            ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) := by
  let x' : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading (p
    +
      1) :=
    ⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d x,
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d_mem p x
          x.property⟩
  have hd := congrArg
    (fun f => ((f.v q (p + q + 1) (by omega)).val.app U) y)
    ((Rep.{u, v, w, t, s, o} X R K).module_d (liftComplex.{u, v, w, t, s} X K) p x)
  change regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) (p + 1) q (by omega) U x' y =
      ((((CompDG.{u, v, w, t, s, o} X R).d (((Rep.{u, v, w, t, s, o} X R K).moduleHom
        (liftComplex.{u, v, w,
          t, s} X K) p) x)).v q (p + q + 1) (by omega)).val.app U) y
    at hd
  rw [CochainComplex.dgCategoryLinear_d_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
    (((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) p) x) q (p + q + 1)
      (by
        omega)
      (p + q) (q + 1) (by omega) (by omega)] at hd
  rw [Units.smul_def] at hd
  simp only [SheafOfModules.add_val, SheafOfModules.comp_val,
    PresheafOfModules.add_app, PresheafOfModules.comp_app] at hd
  rw [sheafModule_zsmul_val] at hd
  simp only [PresheafOfModules.zsmul_app, 
    ModuleCat.hom_add, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp] at hd
  rw [Int.negOnePow_succ] at hd
  change (((liftComplex.{u, v, w, t, s} X K).d (p + q) (p + q + 1)).val.app U)
      (regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q (by omega) U x y) =
    regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) (p + 1) q (by omega) U x' y +
      (p.negOnePow : ℤ) •
        regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) p (q + 1) (by omega) U x
          ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)
  rw [hd]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    ]
  dsimp only [regularEvalMap]
  let b := (((liftComplex.{u, v, w, t, s} X K).d (p + q) (p + q + 1)).val.app U)
    (regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q (by omega) U x y)
  let c := regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) p (q + 1) (by omega) U x
    ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)
  change b = (b + (-p.negOnePow : ℤ) • c) + p.negOnePow • c
  have hcancel : (-p.negOnePow : ℤ) • c + p.negOnePow • c = 0 := by
    have hs : (-p.negOnePow : ℤ) = -(p.negOnePow : ℤ) := by simp
    rw [hs, neg_zsmul]
    exact neg_add_cancel _
  calc
    b = b + 0 := by simp
    _ = b + ((-p.negOnePow : ℤ) • c + p.negOnePow • c) := by rw [hcancel]
    _ = (b + (-p.negOnePow : ℤ) • c) + p.negOnePow • c :=
      (add_assoc b ((-p.negOnePow : ℤ) • c) (p.negOnePow • c)).symm

private noncomputable def regularEvalAddHom (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (d p q : ℤ) (h : p + q = d) (U : X.Cᵒᵖ) :
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p →+
      ((((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) →ₗ[ℤ] (((liftComplex.{u, v, w, t, s} X
          K).X d).val.obj U)) where
  toFun x := (regularEvalMap.{u, v, w, t, s, o} X R K d p q h U x).restrictScalars ℤ
  map_zero' := by
    ext y
    simp [regularEvalMap]
    rfl
  map_add' := by
    intro x y
    ext z
    simp [regularEvalMap]

private noncomputable def regularBalanced (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (U : X.Cᵒᵖ) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K ((Rep.{u, v, w, t, s, o} X R
      K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)) U d
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        (((liftComplex.{u, v, w, t, s} X K).X d).val.obj U))
          where
  toFun p q h := (regularEvalAddHom.{u, v, w, t, s, o} X R K d p q h U).toIntLinearMap
  map_smul := by
    intro p q h x r y
    change ((regularEvalMap.{u, v, w, t, s, o} X R K d p q h U x) (r • y)) =
      r • ((regularEvalMap.{u, v, w, t, s, o} X R K d p q h U x) y)
    exact (regularEvalMap.{u, v, w, t, s, o} X R K d p q h U x).map_smul r y
  balance := by
    intro p q n h₁ h₂ x a y
    let x' : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading
      (p +
        n) :=
      ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : ((Rep.{u, v, w, t, s, o}
        X R
          K).functor.obj (liftComplex.{u, v, w, t, s} X K)).M),
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).smul_mem p n
          x a
            x.property a.property⟩
    obtain ⟨z, hz, hcomp⟩ := (Rep.{u, v, w, t, s, o} X R K).module_action
      (liftComplex.{u, v, w, t, s} X
        K) p n (p + n) (by omega) x a
    have hx : x' = z := by
      apply Subtype.ext
      exact hz.symm
    have hm := congrArg (fun z => (Rep.{u, v, w, t, s, o} X R K).moduleHom
      (liftComplex.{u, v, w, t, s}
        X K) (p + n) z) hx
    change regularEvalMap.{u, v, w, t, s, o} X R K d (p + n) q h₁ U x' y =
      regularEvalMap.{u, v, w, t, s, o} X R K d p (q + n) h₂ U x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U).hom y)
    simp only [regularEvalMap]
    rw [hm, hcomp]
    rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
      (h := (show p + n = p + n from by omega))
      (g := ((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) p) x)
      (f := ((Rep.{u, v, w, t, s, o} X R K).algebraHom n) a)
      q (q + n) d (by omega) (by omega)]
    rfl

private def intLinearPrecomp {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (g : A →ₗ[ℤ] B) : (B →ₗ[ℤ] C) →ₗ[ℤ] (A →ₗ[ℤ] C) where
  toFun f := f.comp g
  map_add' f h := by ext x; simp
  map_smul' r f := by ext x; simp

private def intLinearPostcomp {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : B →ₗ[ℤ] C) : (A →ₗ[ℤ] B) →ₗ[ℤ] (A →ₗ[ℤ] C) where
  toFun g := f.comp g
  map_add' g h := by ext x; simp
  map_smul' r g := by ext x; simp

private noncomputable def regularBalanced_afterMap (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {U V : X.Cᵒᵖ} (f : U ⟶ V) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K ((Rep.{u, v, w, t, s, o} X R
      K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)) U d
      ((ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
        (((liftComplex.{u, v, w, t, s} X K).X d).val.obj V)) where
  toFun p q h :=
    intLinearPrecomp ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f).hom.restrictScalars ℤ) ∘ₗ
      (regularEvalAddHom.{u, v, w, t, s, o} X R K d p q h V).toIntLinearMap
  map_smul := by
    intro p q h x r y
    change regularEvalMap.{u, v, w, t, s, o} X R K d p q h V x
        ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) (r • y)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom r •
        regularEvalMap.{u, v, w, t, s, o} X R K d p q h V x ((((liftComplex.{u, v, w, t, s} X K).X
            q).val.map f) y)
    rw [PresheafOfModules.map_smul]
    exact (regularEvalMap.{u, v, w, t, s, o} X R K d p q h V x).map_smul _ _
  balance := by
    intro p q n h₁ h₂ x a y
    let yV : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj V := (((liftComplex.{u, v, w, t, s} X
        K).X q).val.map f) y
    let actU := (((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val
    let actV := (((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val
    have hn := actU.naturality f
    have heq := congrArg (fun g => g y) hn
    have hcomm :
        (((liftComplex.{u, v, w, t, s} X K).X (q + n)).val.map f) ((actU.app U).hom y) =
          (actV.app V).hom yV := by
      change (actV.app V).hom ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y) =
        (((liftComplex.{u, v, w, t, s} X K).X (q + n)).val.map f) ((actU.app U).hom y) at heq
      exact heq.symm
    change regularEvalMap.{u, v, w, t, s, o} X R K d (p + n) q h₁ V
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) •
          (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).M),
          ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).smul_mem p
            n x
              a x.property a.property⟩ yV =
      regularEvalMap.{u, v, w, t, s, o} X R K d p (q + n) h₂ V x
        ((((liftComplex.{u, v, w, t, s} X K).X (q + n)).val.map f) ((actU.app U).hom y))
    rw [hcomm]
    exact (regularBalanced.{u, v, w, t, s, o} X R K V d).balance p q n h₁ h₂ x a yV

private noncomputable def regularSectionwiseEval (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (U : X.Cᵒᵖ) (d : ℤ) :
    ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
      K))).X
        d).obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      (((liftComplex.{u, v, w, t, s} X K).X d).val.obj U) :=
  Classical.choose (ExistsUnique.exists
    (D.sectionwiseTensorUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t,
        s} X K)) U d
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        (((liftComplex.{u, v, w, t, s} X K).X d).val.obj U))
      (regularBalanced.{u, v, w, t, s, o} X R K U d)))

private lemma regularSectionwiseEval_pure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (U : X.Cᵒᵖ) (d p q : ℤ) (h : p + q = d)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
      (y :
        ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d
        (cast (congrArg
          (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v,
              w, t, s} X K))).X k).obj U : Type _)) h)
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) =
      (regularBalanced.{u, v, w, t, s, o} X R K U d).toFun p q h x y := by
  exact Classical.choose_spec (ExistsUnique.exists
    (D.sectionwiseTensorUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t,
        s} X K)) U d
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        (((liftComplex.{u, v, w, t, s} X K).X d).val.obj U))
      (regularBalanced.{u, v, w, t, s, o} X R K U d))) p q h x y

/-- The evaluation map on a pure tensor in degree `p + q` is the balanced map. -/
private lemma regularSectionwiseEval_pure_rfl (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (U : X.Cᵒᵖ) (p q : ℤ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q)
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)) p q U x y) =
      (regularBalanced.{u, v, w, t, s, o} X R K U (p + q)).toFun p q rfl x y := by
  simpa using regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U (p + q) p q rfl x y

private lemma sectionwiseTensorUniversal_ext (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (M : (dgCategory (Rep.{u, v, w, t, s, o} X
      R
        K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ)
    (P : ModuleCat.{max u v w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    (b : BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d P)
    {f g : ((D.sectionwise M).X d).obj U
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P}
    (hf : ∀ (p q : ℤ) (h : p + q = d) (x : M.grading p)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
      f (cast
        (congrArg (fun k : ℤ => (((D.sectionwise M).X k).obj U : Type _)) h)
        (D.sectionwisePure M p q U x y)) = b.toFun p q h x y)
    (hg : ∀ (p q : ℤ) (h : p + q = d) (x : M.grading p)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
      g (cast
        (congrArg (fun k : ℤ => (((D.sectionwise M).X k).obj U : Type _)) h)
        (D.sectionwisePure M p q U x y)) = b.toFun p q h x y) :
    f = g := by
  obtain ⟨u, hu, huniq⟩ := D.sectionwiseTensorUniversal M U d P b
  exact (huniq f hf).trans (huniq g hg).symm

private lemma regularSectionwiseEval_identity_pure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (U : X.Cᵒᵖ) (d : ℤ)
    (y : ((liftComplex.{u, v, w, t, s} X K).X d).val.obj U) :
    regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d
        (cast (congrArg
          (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v,
              w, t, s} X K))).X k).obj U : Type _))
          (by omega : 0 + d = d))
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) 0 d U (regularIdentity.{u, v, w, t, s, o} X R K) y)) = y := by
  rw [regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U d 0 d (by omega)
    (regularIdentity.{u, v, w, t, s, o} X R K) y]
  exact regularEvalMap_identity.{u, v, w, t, s, o} X R K d U y

private lemma regularSectionwiseEval_natural_pure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (p q : ℤ) (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
        K)).grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    regularSectionwiseEval.{u, v, w, t, s, o} X R K D V (p + q)
        (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).X (p + q)).map f
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) =
      ((liftComplex.{u, v, w, t, s} X K).X (p + q)).val.map f
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q)
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) := by
  let y' : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj V := (((liftComplex.{u, v, w, t, s} X
      K).X q).val.map f) y
  rw [D.sectionwisePure_natural ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s}
      X K)) p q f x y]
  change regularSectionwiseEval.{u, v, w, t, s, o} X R K D V (p + q)
      (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
        K))
          p q V x y') = _
  rw [regularSectionwiseEval_pure_rfl.{u, v, w, t, s, o} X R K D V p q x y',
    regularSectionwiseEval_pure_rfl.{u, v, w, t, s, o} X R K D U p q x y]
  dsimp only [regularBalanced, regularEvalAddHom]
  change regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q rfl V x y' =
    ((liftComplex.{u, v, w, t, s} X K).X (p + q)).val.map f
      (regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q rfl U x y)
  exact (regularEvalMap_natural.{u, v, w, t, s, o} X R K (p + q) p q rfl f x y).symm

private lemma regularSectionwiseEval_natural (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) {U V : X.Cᵒᵖ} (f : U ⟶ V) (d : ℤ) :
    (((ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).map
        (ModuleCat.ofHom (regularSectionwiseEval.{u, v, w, t, s, o} X R K D V d))).hom).comp
        (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).X d).map f).hom =
      (((liftComplex.{u, v, w, t, s} X K).X d).val.map f).hom.comp
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d) := by
  let P := ((ModuleCat.restrictScalars
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
    (((liftComplex.{u, v, w, t, s} X K).X d).val.obj V))
  let b := regularBalanced_afterMap.{u, v, w, t, s, o} X R K f d
  let left : ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s} X
      K))).X d).obj U →ₗ[
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P :=
    (((liftComplex.{u, v, w, t, s} X K).X d).val.map f).hom.comp
      (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d)
  let right : ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s} X
      K))).X d).obj U →ₗ[
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P :=
    (((ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).map
      (ModuleCat.ofHom (regularSectionwiseEval.{u, v, w, t, s, o} X R K D V d))).hom).comp
        (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).X d).map f).hom
  have hleft : ∀ (p q : ℤ) (h : p + q = d)
      (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
        (y
          : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
      left (cast (congrArg
        (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v,
            w, t, s} X K))).X k).obj U : Type _)) h)
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
          X
            K)) p q U x y)) = b.toFun p q h x y := by
    intro p q h x y
    cases h
    change (((liftComplex.{u, v, w, t, s} X K).X (p + q)).val.map f).hom
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q)
          (cast (congrArg
            (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
              (liftComplex.{u,
                v, w, t, s} X K))).X k).obj U : Type _))
            rfl) (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
              (liftComplex.{u, v, w,
                t, s} X K)) p q U x y))) = _
    rw [regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U (p + q) p q rfl x y]
    dsimp [left, b, regularBalanced_afterMap, regularBalanced, regularEvalAddHom,
      intLinearPrecomp]
    exact regularEvalMap_natural.{u, v, w, t, s, o} X R K (p + q) p q rfl f x y
  have hright : ∀ (p q : ℤ) (h : p + q = d)
      (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
        (y
          : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
      right (cast (congrArg
        (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v,
            w, t, s} X K))).X k).obj U : Type _)) h)
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
          X
            K)) p q U x y)) = b.toFun p q h x y := by
    intro p q h x y
    cases h
    exact (regularSectionwiseEval_natural_pure.{u, v, w, t, s, o} X R K D f p q x y).trans
      (hleft p q rfl x y)
  have hmaps := sectionwiseTensorUniversal_ext.{u, v, w, t, s, o} X R K D
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) U d P b hleft
      hright
  exact hmaps.symm

private lemma regularSectionwiseEval_d_pure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (U : X.Cᵒᵖ) (p q : ℤ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
      (y :
        ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    (((liftComplex.{u, v, w, t, s} X K).d (p + q) (p + q + 1)).val.app U)
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q)
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) =
      regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q + 1)
        (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).d (p + q) (p + q + 1)).app U
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) := by
  rw [D.sectionwisePure_d ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
    K))
      p q U x y]
  rw [map_add, map_zsmul]
  rw [regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U (p + q + 1) (p + 1) q (by omega)
    ⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d x,
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d_mem p x
          x.property⟩ y]
  rw [regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U (p + q + 1) p (q + 1) (by omega)
    x ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)]
  rw [regularSectionwiseEval_pure_rfl.{u, v, w, t, s, o} X R K D U p q x y]
  dsimp only [regularBalanced, regularEvalAddHom]
  change (((liftComplex.{u, v, w, t, s} X K).d (p + q) (p + q + 1)).val.app U)
      (regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q rfl U x y) =
    regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) (p + 1) q (by omega) U
        ⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d x,
          ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d_mem p x
              x.property⟩ y +
      (p.negOnePow : ℤ) •
        regularEvalMap.{u, v, w, t, s, o} X R K (p + q + 1) p (q + 1) (by omega) U x
          ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)
  exact regularEvalMap_d.{u, v, w, t, s, o} X R K p q U x y

private noncomputable def regularBalanced_differential (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (U : X.Cᵒᵖ) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K ((Rep.{u, v, w, t, s, o} X R
      K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)) U d
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        (((liftComplex.{u, v, w, t, s} X K).X (d + 1)).val.obj
          U)) where
  toFun p q h :=
    intLinearPostcomp ((((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app
        U).hom.restrictScalars ℤ) ∘ₗ
      (regularBalanced.{u, v, w, t, s, o} X R K U d).toFun p q h
  map_smul := by
    intro p q h x r y
    change (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom
        ((regularBalanced.{u, v, w, t, s, o} X R K U d).toFun p q h x (r • y)) =
      r • (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom
        ((regularBalanced.{u, v, w, t, s, o} X R K U d).toFun p q h x y)
    rw [(regularBalanced.{u, v, w, t, s, o} X R K U d).map_smul p q h x r y]
    exact (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom.map_smul _ _
  balance := by
    intro p q n h₁ h₂ x a y
    change (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom
        ((regularBalanced.{u, v, w, t, s, o} X R K U d).toFun (p + n) q h₁
          ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) •
            (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).M),
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).smul_mem
              p n
                x a x.property a.property⟩ y) =
      (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom
        ((regularBalanced.{u, v, w, t, s, o} X R K U d).toFun p (q + n) h₂ x
          (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U).hom
            y))
    exact congrArg (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom
      ((regularBalanced.{u, v, w, t, s, o} X R K U d).balance p q n h₁ h₂ x a y)

private lemma regularSectionwiseEval_d (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (D : TensorWithComplexData.{u, v, w, t, s, o} X R K) (U : X.Cᵒᵖ) (d : ℤ) :
    (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom.comp
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d) =
      (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (d + 1)).comp
        (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).d d (d + 1)).app U).hom := by
  let P := ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    (((liftComplex.{u, v, w, t, s} X K).X (d +
      1)).val.obj U)
  let b := regularBalanced_differential.{u, v, w, t, s, o} X R K U d
  let left : ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s} X
      K))).X d).obj U →ₗ[
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P :=
    (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom.comp
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d)
  let right : ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s} X
      K))).X d).obj U →ₗ[
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P :=
    (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (d + 1)).comp
      (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
        K))).d
          d (d + 1)).app U).hom
  have hleft : ∀ (p q : ℤ) (h : p + q = d)
      (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
        (y
          : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
      left (cast (congrArg
        (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v,
            w, t, s} X K))).X k).obj U : Type _)) h)
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
          X
            K)) p q U x y)) = b.toFun p q h x y := by
    intro p q h x y
    cases h
    change (((liftComplex.{u, v, w, t, s} X K).d (p + q) ((p + q) + 1)).val.app U).hom
        (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q)
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) = _
    rw [regularSectionwiseEval_pure_rfl.{u, v, w, t, s, o} X R K D U p q x y]
    dsimp [b, regularBalanced_differential]
    rfl
  have hright : ∀ (p q : ℤ) (h : p + q = d)
      (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
        (y
          : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
      right (cast (congrArg
        (fun k : ℤ => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v,
            w, t, s} X K))).X k).obj U : Type _)) h)
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
          X
            K)) p q U x y)) = b.toFun p q h x y := by
    intro p q h x y
    cases h
    change regularSectionwiseEval.{u, v, w, t, s, o} X R K D U ((p + q) + 1)
        (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).d (p + q) ((p + q) + 1)).app U
          (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
            (liftComplex.{u, v, w, t, s} X
              K)) p q U x y)) = _
    rw [(regularSectionwiseEval_d_pure.{u, v, w, t, s, o} X R K D U p q x y).symm]
    rw [regularSectionwiseEval_pure_rfl.{u, v, w, t, s, o} X R K D U p q x y]
    dsimp [b, regularBalanced_differential]
    rfl
  have hmaps := sectionwiseTensorUniversal_ext.{u, v, w, t, s, o} X R K D
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) U d P b hleft
      hright
  simpa only [left, right] using hmaps

private noncomputable def regularSectionwiseEvalHom
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) (D : TensorWithComplexData.{u, v, w, t, s, o} X R
      K) :
    D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (liftComplex.{u, v, w, t, s} X K) := by
  refine CochainComplex.ofHom (fun d => ?_) (fun d => ?_)
  · refine { app := fun U => ConcreteCategory.ofHom
               (C := ModuleCat.{max u v w t s}
                 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
               (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d)
             naturality := ?_ }
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact DFunLike.congr_fun (regularSectionwiseEval_natural.{u, v, w, t, s, o} X R K D f d) y
  · ext U y
    change (((liftComplex.{u, v, w, t, s} X K).d d (d + 1)).val.app U).hom
        ((regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d) y) =
      (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (d + 1))
        ((((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
            K))).d d (d + 1)).app U).hom y)
    exact LinearMap.congr_fun (regularSectionwiseEval_d.{u, v, w, t, s, o} X R K D U d) y

end

end AlgebraicGeometry.RingedSite
