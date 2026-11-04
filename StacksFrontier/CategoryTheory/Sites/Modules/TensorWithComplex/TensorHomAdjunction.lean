module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SheafifiedTensor
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseTensor
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseComplex
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SheafifiedTensor

/-!
# Linearity of the tensor functor and the tensor-Hom adjunction

Part of `StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex` (see there for the overview).
This file proves that the sheafified tensor complex is linear over the base ring, packages it as
a differential graded functor, constructs the tensor-Hom adjunction with the representable
functor `Hom(K, -)`, and proves the main results: `tensorWithComplexDG`,
`tensorWithComplexDG_regular` and `tensorWithComplexDG_preservesCoproducts`.
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

attribute [local instance_reducible] tensorSectionwise tensorDegreePresheaf tensorSheafified
  tensorPresheafMap tensorPresheafDifferential

/-! ### Linearity over the base ring

Stacks 0CS6 tensors over a sheaf of commutative `R`-algebras, so a base-ring scalar acts on
sections by multiplication by a section of `O`; that is the content of `ScalarSections`, assumed
from here on. On the left factor of a pure tensor the scalar `r` is the right action of the image
of `r` in the endomorphism algebra, by `DifferentialGradedModule.op_algebraMap_smul`, and the
balancing relation of the tensor product carries that action over to the right factor, where
`DGCategory.HomRepresentation.algebraHom_algebraMap` identifies it with `r` times the identity of
`K`, that is with multiplication by a section of `O`. Pure tensors are linear over the sections of
`O` in the right factor, so the scalar comes back out, and the tensor functor is `R`-linear and
not merely additive. -/

variable [ScalarSections.{u, v, w, t, s, o} X R]

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Two additive maps out of a degreewise tensor product agree as soon as they agree on pure
tensors. This is `AlgebraicGeometry.RingedSite.tensorDegree_hom_ext` for maps that are only
additive, which is what a comparison whose right-hand side multiplies by a section of the
structure sheaf is: that multiplication is not a map of modules over the sections. -/
private lemma tensorDegree_add_ext
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) {P : Type*} [AddCommGroup P]
    (f g : TensorDegree.{u, v, w, t, s, o} X R K M U d →+ P)
    (hfg : ∀ p q h x y, f (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
      g (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y))
    (z : TensorDegree.{u, v, w, t, s, o} X R K M U d) : f z = g z := by
  classical
  obtain ⟨z, rfl⟩ := (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add]; rw [hz, hz']
  | of pq z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add]; rw [hz, hz']
    | tmul y x => exact hfg pq.1.1 pq.1.2 pq.2 x y

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Pure tensors are linear over the sections of the structure sheaf in the right factor. -/
private lemma tensorDegreePure_smul_right
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p q : ℤ) (h : p + q = d) (x : M.grading p)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
      (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x (c • y) =
      c • tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y :=
  (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U d).map_smul p q h x c y

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- **Pure tensors do not see a change of the right-hand degree.** This is the companion of
`AlgebraicGeometry.RingedSite.tensorDegreePure_congr` for the second factor: there the two
elements of the differential graded module lie in gradings indexed by equal integers and are
compared by their common underlying value, here the two sections lie in the components `K^q` and
`K^{q'}` of the complex, which are different types, and are compared by `HEq`. -/
private lemma tensorDegreePure_congr_snd
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p q q' : ℤ) (hq : q = q')
    (h : p + q = d) (h' : p + q' = d) (x : M.grading p)
    (y : tensorSections.{u, v, w, t, s} X K U q)
    (y' : tensorSections.{u, v, w, t, s} X K U q') (hy : HEq y y') :
    tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y =
      tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q' h' x y' := by
  subst hq
  cases hy
  rfl

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- The identity of `K` in the differential graded category acts on sections as the identity,
once the degree it reaches has been identified with the degree it starts from. -/
private lemma identityCochain_app
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) (U : X.Cᵒᵖ) (q q' : ℤ) (hq : q + 0 = q')
    (y : tensorSections.{u, v, w, t, s} X K U q) :
    HEq ((((CompDG.{u, v, w, t, s, o} X R).id
      (liftComplex.{u, v, w, t, s} X K)).v q q' hq).val.app U y) y := by
  obtain rfl : q' = q := by omega
  rw [CochainComplex.dgCategoryLinear_id_v]
  rfl

/-- **A base-ring scalar on the left factor of a pure tensor is a section of `O`.** Multiplying
`x` by `r : R` is the right action of the image of `r` in the endomorphism algebra of `K`, and
the balancing relation of the tensor product moves that action to the right factor, where it is
the action of `r` times the identity of `K`, that is multiplication by `scalarSection r U`. -/
private lemma tensorDegreePure_smul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p q : ℤ) (h : p + q = d) (r : R)
    (x : M.grading p) (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h
        ⟨r • (x : M.M), (M.grading p).smul_mem r x.property⟩ y =
      ScalarSections.scalarSection r U •
        tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y := by
  have ha : algebraMap R (Rep.{u, v, w, t, s, o} X R K).algebra.A r ∈
      (Rep.{u, v, w, t, s, o} X R K).algebra.grading 0 :=
    (Rep.{u, v, w, t, s, o} X R K).algebraMap_mem_grading_zero r
  have hop : MulOpposite.op (algebraMap R (Rep.{u, v, w, t, s, o} X R K).algebra.A r) •
      (x : M.M) = r • (x : M.M) :=
    DifferentialGradedModule.op_algebraMap_smul M r (x : M.M)
  have hb := tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U d p q 0
    (by omega) (by omega) x ⟨_, ha⟩ y
  refine Eq.trans (tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U d p (p + 0) q
    (add_zero p).symm h (by omega)
    ⟨r • (x : M.M), (M.grading p).smul_mem r x.property⟩
    ⟨MulOpposite.op (algebraMap R (Rep.{u, v, w, t, s, o} X R K).algebra.A r) • (x : M.M),
      M.smul_mem p 0 x _ x.property ha⟩ hop.symm y) (hb.trans ?_)
  rw [(Rep.{u, v, w, t, s, o} X R K).algebraHom_algebraMap r,
    CochainComplex.HomComplex.Cochain.smul_v, ScalarSections.smul_app,
    tensorDegreePure_smul_right.{u, v, w, t, s, o} X R K M U d p (q + 0) (by omega) x]
  refine congrArg (fun z => ScalarSections.scalarSection r U • z) ?_
  exact tensorDegreePure_congr_snd.{u, v, w, t, s, o} X R K M U d p (q + 0) q
    (add_zero q) (by omega) h x _ y
    (identityCochain_app.{u, v, w, t, s, o} X R K U q (q + 0) rfl y)

/-- A base-ring scalar passes through the degreewise tensor product as multiplication by a
section of the structure sheaf. -/
private lemma tensorDegreeMap_smul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (r : R) (f : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ)
    (d e : ℤ) (hde : d + n = e) (z : TensorDegree.{u, v, w, t, s, o} X R K L U d) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K (r • f) U d e hde z =
      ScalarSections.scalarSection r U •
        tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde z := by
  refine tensorDegree_add_ext.{u, v, w, t, s, o} X R K L U d
    (tensorDegreeMap.{u, v, w, t, s, o} X R K (r • f) U d e hde).toAddMonoidHom
    ((AddMonoidHom.mk' (fun z => ScalarSections.scalarSection r U • z)
        (fun a b => smul_add (ScalarSections.scalarSection r U) a b)).comp
      (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde).toAddMonoidHom) ?_ z
  intro p q hpq x y
  change tensorDegreeMap.{u, v, w, t, s, o} X R K (r • f) U d e hde
      (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q hpq x y) =
    ScalarSections.scalarSection r U • tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde
      (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q hpq x y)
  rw [tensorDegreeMap_pure, tensorDegreeMap_pure,
    tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U e (p + n) (p + n) q rfl
      (by omega) (by omega) (homogeneousGradedMap (r • f) p x)
      ⟨r • (homogeneousGradedMap f p x : M.M),
        (M.grading (p + n)).smul_mem r (homogeneousGradedMap f p x).property⟩ rfl y]
  exact tensorDegreePure_smul.{u, v, w, t, s, o} X R K M U e (p + n) q (by omega) r
    (homogeneousGradedMap f p x) y

/-- Two morphisms out of a sheafification agree as soon as they agree on the sections that come
from the presheaf, that is after the unit of the sheafification adjunction. -/
private lemma sheafified_hom_ext
    {A : PresheafOfModules.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    {B : TensorModO.{u, v, w, t, s} X}
    (α β : (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj A ⟶ B)
    (hab : ∀ (U : X.Cᵒᵖ) (z : A.obj U),
      (α.val.app U) (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app A).app U z) =
        (β.val.app U) (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app A).app U z)) :
    α = β := by
  apply ((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv A B).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact hab U z

/-- **The tensor functor is linear over the base ring.** Two morphisms out of a sheafification
agree as soon as they agree after the unit of the adjunction, and there the comparison is the
degreewise statement `AlgebraicGeometry.RingedSite.tensorDegreeMap_smul`. -/
private lemma tensorSheafifiedCochain_smul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (r : R) (f : (dgCategory _).Hom L M n) :
    tensorSheafifiedCochain.{u, v, w, t, s, o} X R K (r • f) =
      r • tensorSheafifiedCochain.{u, v, w, t, s, o} X R K f := by
  let : (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).left_adjoint_additive
  apply CochainComplex.HomComplex.Cochain.ext
  intro d e h
  rw [CochainComplex.HomComplex.Cochain.smul_v]
  change (PresheafOfModules.sheafification.{max u v w t s}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (tensorPresheafMap.{u, v, w, t, s, o} X R K (r • f) d e h) =
    r • (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h)
  apply sheafified_hom_ext.{u, v, w, t, s} X
  intro U z
  have hrf := congrArg (fun a => (a.app U).hom z)
    ((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality
        (tensorPresheafMap.{u, v, w, t, s, o} X R K (r • f) d e h))
  have hf := congrArg (fun a => (a.app U).hom z)
    ((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality
        (tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h))
  change (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (tensorDegreePresheaf.{u, v, w, t, s, o} X R K M e)).app U)
      (tensorDegreeMap.{u, v, w, t, s, o} X R K (r • f) U d e h z) =
    ((PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (tensorPresheafMap.{u, v, w, t, s, o} X R K (r • f) d e h)).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            (tensorDegreePresheaf.{u, v, w, t, s, o} X R K L d)).app U z) at hrf
  change (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (tensorDegreePresheaf.{u, v, w, t, s, o} X R K M e)).app U)
      (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e h z) =
    ((PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h)).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            (tensorDegreePresheaf.{u, v, w, t, s, o} X R K L d)).app U z) at hf
  have step : (((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (tensorDegreePresheaf.{u, v, w, t, s, o} X R K M e)).app U)
      (tensorDegreeMap.{u, v, w, t, s, o} X R K (r • f) U d e h z) =
    ScalarSections.scalarSection r U •
      ((((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (tensorDegreePresheaf.{u, v, w, t, s, o} X R K M e)).app U)
        (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e h z)) := by
    rw [tensorDegreeMap_smul.{u, v, w, t, s, o} X R K r f U d e h z]
    exact map_smul _ _ _
  refine hrf.symm.trans (step.trans ?_)
  refine (congrArg (fun y => ScalarSections.scalarSection r U • y) hf).trans ?_
  exact (ScalarSections.smul_app r
    ((PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h)) U
    ((((PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (tensorDegreePresheaf.{u, v, w, t, s, o} X R K L d)).app U) z)).symm

private noncomputable def tensorDG
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    DGCategory.DGFunctor
      (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra)
      (CompDG.{u, v, w, t, s, o} X R) where
  obj := tensorSheafified.{u, v, w, t, s, o} X R K
  map := tensorSheafifiedCochain.{u, v, w, t, s, o} X R K
  map_add := tensorSheafifiedCochain_add.{u, v, w, t, s, o} X R K
  map_smul {_ _ _} r f := tensorSheafifiedCochain_smul.{u, v, w, t, s, o} X R K r f
  map_d f := tensorSheafifiedCochain_d_of_presheaf.{u, v, w, t, s, o} X R K f
      (tensorPresheafCochain_d.{u, v, w, t, s, o} X R K f)
  map_comp h g f := tensorSheafifiedCochain_comp.{u, v, w, t, s, o} X R K h g f
  map_id := tensorSheafifiedCochain_id.{u, v, w, t, s, o} X R K


section TensorHom

variable (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
variable (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
variable (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)

private noncomputable def uncurryBalanced
    (f : DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P))
    (U : X.Cᵒᵖ) (d : ℤ) : BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d ((P.X
        d).val.obj U) where
  toFun p q h := ((evaluationBalanced.{u, v, w, t, s, o} X R K P U d).toFun p q h).comp
    (f.gradedMap p).toAddMonoidHom.toIntLinearMap
  map_smul p q h x r y := (evaluationBalanced.{u, v, w, t, s, o} X R K P U d).map_smul p q h
      (f.gradedMap p x) r y
  balance p q n h₁ h₂ x a y := by
    change (evaluationBalanced.{u, v, w, t, s, o} X R K P U d).toFun (p+n) q h₁
      (f.gradedMap (p+n) ⟨_, M.smul_mem p n x a x.property a.property⟩) y = _
    have hx : f.gradedMap (p+n) ⟨_, M.smul_mem p n x a x.property a.property⟩ =
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (f.toFun x),
          ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).smul_mem p n (f.gradedMap p x) a
            (f.gradedMap p x).property a.property⟩ := by
      apply Subtype.ext
      exact f.map_smul x a
    rw [hx]
    exact (evaluationBalanced.{u, v, w, t, s, o} X R K P U d).balance p q n h₁ h₂ (f.gradedMap p x)
      a y

private noncomputable def uncurryDegree
    (f : DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P))
    (U : X.Cᵒᵖ) (d : ℤ) :
    TensorDegree.{u, v, w, t, s, o} X R K M U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] ((P.X d).val.obj U) :=
  tensorDegreeLift.{u, v, w, t, s, o} X R K M U d _ (uncurryBalanced.{u, v, w, t, s, o} X R K M P f
    U d)

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma uncurryDegree_pure
    (f : DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P))
    (U : X.Cᵒᵖ) (d p q : ℤ) (h : p + q = d) (x : M.grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    uncurryDegree.{u, v, w, t, s, o} X R K M P f U d (tensorDegreePure.{u, v, w, t, s, o} X R K M U
      d p q h x
        y) =
      evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U (f.gradedMap p x) y :=
  tensorDegreeLift_pure.{u, v, w, t, s, o} X R K M U d _ (uncurryBalanced.{u, v, w, t, s, o} X R K M
    P f U d)
      p q h x y

private noncomputable def uncurryPresheaf
    (f : DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P)) (d : ℤ) :
    tensorDegreePresheaf.{u, v, w, t, s, o} X R K M d ⟶ (P.X d).val where
  app U := ModuleCat.ofHom (uncurryDegree.{u, v, w, t, s, o} X R K M P f U d)
  naturality {U V} a := by
    apply ModuleCat.hom_ext
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d
      ((ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom).obj
        ((P.X d).val.obj V))
    intro p q h x y
    change uncurryDegree.{u, v, w, t, s, o} X R K M P f V d
        (tensorDegreeRestriction.{u, v, w, t, s, o} X R K M a d
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y)) =
      (P.X d).val.map a (uncurryDegree.{u, v, w, t, s, o} X R K M P f U d
        (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y))
    rw [tensorDegreeRestriction_pure, uncurryDegree_pure, uncurryDegree_pure]
    exact (evaluationEvalMap_natural.{u, v, w, t, s, o} X R K P d p q h a (f.gradedMap p x) y).symm

private noncomputable def uncurryHom
    (f : DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P)) :
    tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P where
  f := uncurryPresheaf.{u, v, w, t, s, o} X R K M P f
  comm' i j hij := by
    have hj : i+1=j := hij
    cases hj
    change uncurryPresheaf.{u, v, w, t, s, o} X R K M P f i ≫ (P.d i (i+1)).val =
      CochainComplex.of.d _ (tensorPresheafDifferential.{u, v, w, t, s, o} X R K M) i (i+1) ≫
        uncurryPresheaf.{u, v, w, t, s, o} X R K M P f (i+1)
    rw [CochainComplex.of_d]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U i ((P.X (i+1)).val.obj U)
    intro p q h x y
    change ((P.d i (i+1)).val.app U)
        (uncurryDegree.{u, v, w, t, s, o} X R K M P f U i
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U i p q h x y)) =
      uncurryDegree.{u, v, w, t, s, o} X R K M P f U (i+1)
        (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U i
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U i p q h x y))
    rw [uncurryDegree_pure, tensorDegreeDifferential_pure, map_add, map_zsmul,
      uncurryDegree_pure, uncurryDegree_pure]
    cases h
    rw [evaluationEvalMap_d]
    congr 2
    apply congrArg (evaluationEvalMap.{u, v, w, t, s, o} X R K P (p+q+1) (p+1) q (by omega) U)
    apply Subtype.ext
    exact (congrArg (fun z => z x) f.map_d).symm


end TensorHom

open CochainComplex.HomComplex

section TensorCurry

variable (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
variable (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
variable (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
private noncomputable abbrev ForgetComplex :
    CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ ⥤
      CochainComplex
        (PresheafOfModules.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ :=
  (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)

attribute [local instance_reducible] SheafOfModules.forget

private noncomputable def curryComponent
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) (x : M.grading p) (q d : ℤ) (h : q + p = d) :
    (liftComplex.{u, v, w, t, s} X K).X q ⟶ P.X d where
  val :=
    { app U := by
        let Q := ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U
        let V := (P.X d).val.obj U
        let gU : (tensorDegreePresheaf.{u, v, w, t, s, o} X R K M d).obj U ⟶ V := (g.f d).app U
        let b : Q →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
          TensorDegree.{u, v, w, t, s, o} X R K M U d :=
          { toFun y := tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y
            map_add' := (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x).map_add
            map_smul' r y := (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U d).map_smul p q (by
                omega) x r y }
        exact @ModuleCat.ofHom _ _ Q V Q.isAddCommGroup Q.isModule
          V.isAddCommGroup V.isModule (gU.hom.comp b)
      naturality {U V} f := by
        ext y
        change (g.f d).app V
            (tensorDegreePure.{u, v, w, t, s, o} X R K M V d p q _ x (((liftComplex.{u, v, w, t, s}
              X
                K).X q).val.map f y)) =
          (P.X d).val.map f ((g.f d).app U
            (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q _ x y))
        rw [← tensorDegreeRestriction_pure]
        exact congrArg (fun a => a.hom
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y))
          ((g.f d).naturality f) }

private noncomputable def curryCochain
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) : M.grading p →ₗ[ℤ] Cochain (liftComplex.{u, v, w, t, s} X K) P p :=
  AddMonoidHom.toIntLinearMap
    { toFun x := Cochain.mk (curryComponent.{u, v, w, t, s, o} X R K M P g p x)
      map_zero' := by
        apply Cochain.ext
        intro q d h
        ext U y
        change (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q _ 0 y) = 0
        simp
      map_add' := by
        intro x x'
        apply Cochain.ext
        intro q d h
        ext U y
        change (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q _ (x+x') y) =
          (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q _ x y) +
          (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q _ x' y)
        simp }

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma curryCochain_action
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p n : ℤ) (x : M.grading p) (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n) :
    curryCochain.{u, v, w, t, s, o} X R K M P g (p+n)
      ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
        M.smul_mem p n x a x.property a.property⟩ =
      (CompDG.{u, v, w, t, s, o} X R).comp rfl (curryCochain.{u, v, w, t, s, o} X R K M P g p x)
        ((Rep.{u, v, w, t, s, o} X R K).algebraHom n a) := by
  apply Cochain.ext
  intro q d h
  rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R) (h := rfl)
    _ _ q (q+n) d
      rfl (by omega)]
  ext U y
  change (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d (p+n) q _
    ⟨_, M.smul_mem p n x a x.property a.property⟩ y) =
      (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p (q+n) _ x
        ((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q+n) rfl).val.app U y))
  rw [tensorDegreePure_balance]

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma curryCochain_d
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) (x : M.grading p) :
    curryCochain.{u, v, w, t, s, o} X R K M P g (p+1) ⟨M.d x, M.d_mem p x x.property⟩ =
      (CompDG.{u, v, w, t, s, o} X R).d (curryCochain.{u, v, w, t, s, o} X R K M P g p x) := by
  apply Cochain.ext
  intro q d h
  rw [CochainComplex.dgCategoryLinear_d_v (B := TensorModO.{u, v, w, t, s} X) (R := R) _ q d h (p+q)
    (q+1) (by
      omega) rfl,
    Units.smul_def]
  ext U y
  have hg := congrArg (fun f => (f.app U).hom
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl x y)) (g.comm (p+q) d).symm
  have he : d = (p+q)+1 := by omega
  cases he
  change (g.f (p+q+1)).app U
      ((CochainComplex.of.d _ (tensorPresheafDifferential.{u, v, w, t, s, o} X R K M) (p+q)
        (p+q+1)).app
          U
        (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl x y)) =
    ((((ForgetComplex.{u, v, w, t, s} X).obj P).d (p+q) (p+q+1)).app U)
      ((g.f (p+q)).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl x y)) at hg
  rw [CochainComplex.of_d] at hg
  change (g.f (p+q+1)).app U
      (tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U (p+q)
        (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl x y)) = _ at hg
  rw [tensorDegreeDifferential_pure, map_add, map_zsmul] at hg
  simp only [SheafOfModules.add_val, PresheafOfModules.add_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_add,
    ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply]
  rw [sheafModule_zsmul_val.{u, v, w, t, s} X]
  simp only [PresheafOfModules.zsmul_app, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  change (g.f (p+q+1)).app U
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q+1) (p+1) q _ ⟨M.d x, _⟩ y) =
    ((((ForgetComplex.{u, v, w, t, s} X).obj P).d (p+q) (p+q+1)).app U)
      ((g.f (p+q)).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl x y)) +
    ((p+1).negOnePow : ℤ) •
      ((g.f (p+q+1)).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q+1) p (q+1) _ x
        (((liftComplex.{u, v, w, t, s} X K).d q (q+1)).val.app U y)))
  rw [← hg, Int.negOnePow_succ, Units.val_neg, neg_smul]
  simp
  rfl

/-- **Currying is linear over the base ring.** A scalar on the element of the differential graded
module becomes, on a pure tensor, multiplication by a section of the structure sheaf, which the
sections of the given map carry across; and that is again the base-ring scalar on the resulting
cochain. -/
private lemma curryCochain_smul
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) (r : R) (x : M.grading p) :
    curryCochain.{u, v, w, t, s, o} X R K M P g p
        ⟨r • (x : M.M), (M.grading p).smul_mem r x.property⟩ =
      r • curryCochain.{u, v, w, t, s, o} X R K M P g p x := by
  apply Cochain.ext
  intro q d h
  rw [Cochain.smul_v]
  ext U y
  change (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega)
      ⟨r • (x : M.M), (M.grading p).smul_mem r x.property⟩ y) = _
  rw [tensorDegreePure_smul.{u, v, w, t, s, o} X R K M U d p q (by omega) r x y,
    ScalarSections.smul_app]
  change (g.f d).app U (ScalarSections.scalarSection r U •
      tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y) =
    ScalarSections.scalarSection r U •
      (g.f d).app U (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y)
  exact map_smul _ _ _

private noncomputable def curryGraded
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P) (p
      : ℤ)
        :
    M.grading p →+ ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p :=
  by
    letI := (((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p).module
    let e := (Rep.{u, v, w, t, s, o} X R K).moduleHom P p
    exact e.toAddEquiv.symm.toAddMonoidHom.comp
      (curryCochain.{u, v, w, t, s, o} X R K M P g p).toAddMonoidHom


omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma curryGraded_spec
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) (x : M.grading p) :
    (Rep.{u, v, w, t, s, o} X R K).moduleHom P p (curryGraded.{u, v, w, t, s, o} X R K M P g p x) =
      curryCochain.{u, v, w, t, s, o} X R K M P g p x := by
  let _i := (((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p).module
  exact ((Rep.{u, v, w, t, s, o} X R K).moduleHom P p).toAddEquiv.apply_symm_apply _

/-- The graded components of the currying are linear over the base ring: the identification of
the degree-`p` part of `Hom(K, P)` with the degree-`p` morphisms is an `R`-linear equivalence, so
this is `AlgebraicGeometry.RingedSite.curryCochain_smul` read through it. -/
private lemma curryGraded_smul
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) (r : R) (x : M.grading p) :
    (curryGraded.{u, v, w, t, s, o} X R K M P g p
        ⟨r • (x : M.M), (M.grading p).smul_mem r x.property⟩ :
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).M) =
      r • (curryGraded.{u, v, w, t, s, o} X R K M P g p x :
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).M) := by
  let _i := (((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p).module
  have key : (Rep.{u, v, w, t, s, o} X R K).moduleHom P p
      (curryGraded.{u, v, w, t, s, o} X R K M P g p
        ⟨r • (x : M.M), (M.grading p).smul_mem r x.property⟩) =
    (Rep.{u, v, w, t, s, o} X R K).moduleHom P p
      (r • curryGraded.{u, v, w, t, s, o} X R K M P g p x) := by
    rw [curryGraded_spec, map_smul, curryGraded_spec]
    exact curryCochain_smul.{u, v, w, t, s, o} X R K M P g p r x
  rw [((Rep.{u, v, w, t, s, o} X R K).moduleHom P p).injective key]
  rfl

private noncomputable def curryHom
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P) :
    DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P) :=
  homOfGraded M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P) (fun p => by
    letI := (M.grading p).module
    letI := (((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p).module
    exact {
      toFun := fun x => curryGraded.{u, v, w, t, s, o} X R K M P g p x
      map_add' := by intro x y; exact map_add (curryGraded.{u, v, w, t, s, o} X R K M P g p) x y
      map_smul' := by
        intro r x
        exact Subtype.ext (curryGraded_smul.{u, v, w, t, s, o} X R K M P g p r x) })
    (by
      intro p n x a
      obtain ⟨z, hz, he⟩ := (Rep.{u, v, w, t, s, o} X R K).module_action P p n (p+n) rfl
        (curryGraded.{u, v, w, t, s, o} X R K M P g p x) a
      change (curryGraded.{u, v, w, t, s, o} X R K M P g (p+n)
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M), _⟩ :
          ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).M) =
        MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) •
          (curryGraded.{u, v, w, t, s, o} X R K M P g p x : ((Rep.{u, v, w, t, s, o} X R
            K).functor.obj P).M)
      rw [← hz]
      apply congrArg (fun z : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading (p+n) => z.val)
      apply ((Rep.{u, v, w, t, s, o} X R K).moduleHom P (p+n)).injective
      rw [he]
      rw [curryGraded_spec, curryGraded_spec]
      exact curryCochain_action.{u, v, w, t, s, o} X R K M P g p n x a)
    (by
      intro p x
      change (curryGraded.{u, v, w, t, s, o} X R K M P g (p+1) ⟨M.d x, _⟩ :
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).M) =
          (⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj P).d (curryGraded.{u, v, w, t, s, o} X R K M
            P g p x),
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).d_mem p _
              (curryGraded.{u, v, w, t, s, o} X R K M P g p x).property⟩ :
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading (p+1)).val
      apply congrArg (fun z : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading (p+1) => z.val)
      apply ((Rep.{u, v, w, t, s, o} X R K).moduleHom P (p+1)).injective
      rw [(Rep.{u, v, w, t, s, o} X R K).module_d]
      rw [curryGraded_spec, curryGraded_spec]
      exact curryCochain_d.{u, v, w, t, s, o} X R K M P g p x)


end TensorCurry

section TensorAdjunction


variable (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
variable (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
variable (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)

private lemma curryHom_gradedMap
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P)
    (p : ℤ) (x : M.grading p) :
    (curryHom.{u, v, w, t, s, o} X R K M P g).gradedMap p x =
      curryGraded.{u, v, w, t, s, o} X R K M P g p x := by
  apply Subtype.ext
  exact liftGraded_apply M _ _ p x

private lemma curryHom_uncurryHom
    (f : DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P)) :
    curryHom.{u, v, w, t, s, o} X R K M P (uncurryHom.{u, v, w, t, s, o} X R K M P f) = f := by
  apply DifferentialGradedModule.Hom.ext
  let : Module R M.M := M.module
  let : Module R ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).M :=
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).module
  apply DirectSum.decompose_lhom_ext M.grading
  intro p
  let : Module R (M.grading p) := (M.grading p).module
  apply LinearMap.ext
  intro x
  change ((curryHom.{u, v, w, t, s, o} X R K M P (uncurryHom.{u, v, w, t, s, o} X R K M P
    f)).gradedMap p
      x).val =
    (f.gradedMap p x).val
  apply congrArg Subtype.val
  rw [curryHom_gradedMap]
  apply ((Rep.{u, v, w, t, s, o} X R K).moduleHom P p).injective
  rw [curryGraded_spec]
  apply Cochain.ext
  intro q d h
  ext U y
  change uncurryDegree.{u, v, w, t, s, o} X R K M P f U d
    (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q (by omega) x y) = _
  exact uncurryDegree_pure.{u, v, w, t, s, o} X R K M P f U d p q (by omega) x y

private lemma uncurryHom_curryHom
    (g : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P) :
    uncurryHom.{u, v, w, t, s, o} X R K M P (curryHom.{u, v, w, t, s, o} X R K M P g) = g := by
  apply HomologicalComplex.Hom.ext
  funext d
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d ((P.X d).val.obj U)
  intro p q h x y
  change uncurryDegree.{u, v, w, t, s, o} X R K M P (curryHom.{u, v, w, t, s, o} X R K M P g) U d
    (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) = _
  rw [uncurryDegree_pure, curryHom_gradedMap]
  unfold evaluationEvalMap
  rw [curryGraded_spec]
  rfl

private noncomputable def sectionwiseHomEquiv :
    (tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶ (ForgetComplex.{u, v, w, t, s} X).obj P) ≃
      DifferentialGradedModule.Hom M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P) where
  toFun := curryHom.{u, v, w, t, s, o} X R K M P
  invFun := uncurryHom.{u, v, w, t, s, o} X R K M P
  left_inv := uncurryHom_curryHom.{u, v, w, t, s, o} X R K M P
  right_inv := curryHom_uncurryHom.{u, v, w, t, s, o} X R K M P

private noncomputable def tensorHomEquiv :
    (CompDG.{u, v, w, t, s, o} X R).Cocycle (tensorSheafified.{u, v, w, t, s, o} X R K M) P ≃
      (dgCategory _).Cocycle M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P) :=
  (CochainComplex.HomComplex.Cocycle.equivHom _ _).toEquiv.symm |>.trans
    ((complexSheafificationAdjunction.{u, v, w, t, s} X).homEquiv
      (tensorSectionwise.{u, v, w, t, s, o} X R K M) P) |>.trans
    (sectionwiseHomEquiv.{u, v, w, t, s, o} X R K M P) |>.trans
    (cocycleHomEquiv M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P)).symm

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma representedCocycle_ext
    (f g : (dgCategory _).Cocycle M ((Rep.{u, v, w, t, s, o} X R K).functor.obj P))
    (h : ∀ (p : ℤ) (x : M.grading p),
      (Rep.{u, v, w, t, s, o} X R K).moduleHom P p ((cocycleHom f).gradedMap p x) =
        (Rep.{u, v, w, t, s, o} X R K).moduleHom P p ((cocycleHom g).gradedMap p x)) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  let : Module R M.M := M.module
  let : Module R ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).M :=
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).module
  apply DirectSum.decompose_lhom_ext M.grading
  intro p
  let : Module R (M.grading p) := (M.grading p).module
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (((Rep.{u, v, w, t, s, o} X R K).moduleHom P p).injective (h p x))

private lemma tensorHomEquiv_pure
    (g : (CompDG.{u, v, w, t, s, o} X R).Cocycle (tensorSheafified.{u, v, w, t, s, o} X R K M) P)
    (p q d : ℤ) (h : p + q = d) (U : X.Cᵒᵖ) (x : M.grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U
      ((cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K M P g)).gradedMap p x) y =
        ((g.1.v d d (add_zero d)).val.app U)
          (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d).app U
            (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y)) := by
  change evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U
    ((curryHom.{u, v, w, t, s, o} X R K M P
      ((complexSheafificationAdjunction.{u, v, w, t, s} X).homEquiv _ P (Cocycle.homOf
          g))).gradedMap p x) y = _
  rw [curryHom_gradedMap]
  unfold evaluationEvalMap
  rw [curryGraded_spec]
  change (((complexSheafificationAdjunction.{u, v, w, t, s} X).homEquiv _ P (Cocycle.homOf g)).f
      d).app U
    (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) = _
  rw [(complexSheafificationAdjunction.{u, v, w, t, s} X).homEquiv_unit]
  rfl

private lemma tensorCocycle_map_pure
    {L : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    (f : (dgCategory _).Cocycle L M)
    (p q d : ℤ) (h : p + q = d) (U : X.Cᵒᵖ) (x : L.grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    ((((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle f).1.v d d (add_zero d)).val.app U)
      (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K L).f d).app U
        (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y)) =
      ((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d).app U
        (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h
          ((cocycleHom f).gradedMap p x) y) := by
  have hn := (PresheafOfModules.sheafificationAdjunction.{max u v w t s}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality
      (tensorPresheafMap.{u, v, w, t, s, o} X R K f.1 d d (add_zero d))
  have hv := congrArg (fun a => (a.app U).hom
    (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y)) hn
  change ((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d).app U
    (tensorDegreeMap.{u, v, w, t, s, o} X R K f.1 U d d (add_zero d)
      (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y)) =
    ((((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle f).1.v d d (add_zero d)).val.app U)
      (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K L).f d).app U
        (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y)) at hv
  rw [← hv, tensorDegreeMap_pure]
  apply congrArg (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d).app U)
  exact tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U d (p+0) p q (add_zero p)
    (by omega) h _ _ rfl y

private lemma tensorHomEquiv_naturality_left
    {L : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    (f : (dgCategory _).Cocycle L M)
    (g : (CompDG.{u, v, w, t, s, o} X R).Cocycle (tensorSheafified.{u, v, w, t, s, o} X R K M) P) :
    tensorHomEquiv.{u, v, w, t, s, o} X R K L P
      ((CompDG.{u, v, w, t, s, o} X R).compCocycle g ((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle
        f)) =
    (dgCategory _).compCocycle (tensorHomEquiv.{u, v, w, t, s, o} X R K M P g) f := by
  apply representedCocycle_ext.{u, v, w, t, s, o} X R K L P
  intro p x
  apply Cochain.ext
  intro q d h
  ext U y
  change evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q (by omega) U
    ((cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K L P
      ((CompDG.{u, v, w, t, s, o} X R).compCocycle g ((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle
          f)))).gradedMap p x) y =
    evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q (by omega) U
      ((cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K M P g)).gradedMap p
        ((cocycleHom f).gradedMap p x)) y
  rw [tensorHomEquiv_pure, tensorHomEquiv_pure]
  change ((((CompDG.{u, v, w, t, s, o} X R).comp (by omega) g.1
    ((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle f).1).v d d (add_zero d)).val.app U) _ = _
  rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
    (h := (show (0:ℤ)+0=0 from rfl)) g.1 ((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle f).1
    d d d (add_zero d) (add_zero d)]
  change ((g.1.v d d (add_zero d)).val.app U)
    (((((tensorDG.{u, v, w, t, s, o} X R K).mapCocycle f).1.v d d (add_zero d)).val.app U)
      (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K L).f d).app U
        (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q (by omega) x y))) = _
  rw [tensorCocycle_map_pure]

private lemma tensorHomEquiv_naturality_right
    (Q : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (f : (CompDG.{u, v, w, t, s, o} X R).Cocycle (tensorSheafified.{u, v, w, t, s, o} X R K M) P)
    (g : (CompDG.{u, v, w, t, s, o} X R).Cocycle P Q) :
    tensorHomEquiv.{u, v, w, t, s, o} X R K M Q ((CompDG.{u, v, w, t, s, o} X R).compCocycle g f) =
      (dgCategory _).compCocycle ((Rep.{u, v, w, t, s, o} X R K).functor.mapCocycle g)
        (tensorHomEquiv.{u, v, w, t, s, o} X R K M P f) := by
  apply representedCocycle_ext.{u, v, w, t, s, o} X R K M Q
  intro p x
  let a := (cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K M P f)).gradedMap p x
  obtain ⟨z, hz, he⟩ := (Rep.{u, v, w, t, s, o} X R K).map_comp P Q 0 p p (zero_add p) g.1 a
  have hx : (cocycleHom ((dgCategory _).compCocycle
      ((Rep.{u, v, w, t, s, o} X R K).functor.mapCocycle g)
        (tensorHomEquiv.{u, v, w, t, s, o} X R K M P f))).gradedMap p x = z := by
    apply Subtype.ext
    exact hz.symm
  rw [hx, he]
  apply Cochain.ext
  intro q d h
  rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
    (h := zero_add p) _ _ q d d h (add_zero d)]
  ext U y
  change evaluationEvalMap.{u, v, w, t, s, o} X R K Q d p q (by omega) U
    ((cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K M Q
      ((CompDG.{u, v, w, t, s, o} X R).compCocycle g f))).gradedMap p x) y =
    ((g.1.v d d (add_zero d)).val.app U)
      (evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q (by omega) U a y)
  dsimp only [a]
  rw [tensorHomEquiv_pure, tensorHomEquiv_pure]
  change ((((CompDG.{u, v, w, t, s, o} X R).comp (by omega) g.1 f.1).v d d (add_zero d)).val.app U)
    _ = _
  rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
    (h := (show (0:ℤ)+0=0 from rfl)) _ _ d d d (add_zero d) (add_zero d)]
  rfl

private noncomputable def tensorAdjunction :
    (tensorDG.{u, v, w, t, s, o} X R K).onComp ⊣ (Rep.{u, v, w, t, s, o} X R K).functor.onComp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv.{u, v, w, t, s, o} X R K
      homEquiv_naturality_left_symm := by
        intro L M P f g
        apply (tensorHomEquiv.{u, v, w, t, s, o} X R K L P).injective
        refine (Equiv.apply_symm_apply _ _).trans ?_
        exact (tensorHomEquiv_naturality_left.{u, v, w, t, s, o} X R K M P f
          ((tensorHomEquiv.{u, v, w, t, s, o} X R K M P).symm g)).trans
            (congrArg ((dgCategory _).compCocycle · f) (Equiv.apply_symm_apply _ g)) |>.symm
      homEquiv_naturality_right := by
        intro M P Q f g
        exact tensorHomEquiv_naturality_right.{u, v, w, t, s, o} X R K M P Q f g }

end TensorAdjunction

section TensorPackage

variable (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma tensorDegreePure_cast
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d d' p q : ℤ) (hd : d = d') (h : p + q = d) (h' : p + q = d')
    (x : M.grading p) (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    cast (congrArg (TensorDegree.{u, v, w, t, s, o} X R K M U) hd)
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
        tensorDegreePure.{u, v, w, t, s, o} X R K M U d' p q h' x y := by
  cases hd
  rfl

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma tensorDegreePure_heq
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d d' p q : ℤ) (h : p + q = d) (h' : p + q = d')
    (x : M.grading p) (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y)
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U d' p q h' x y) := by
  have hd : d = d' := h.symm.trans h'
  cases hd
  rfl

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma tensorSectionwiseUnit_heq
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d d' : ℤ) (hd : d = d')
    (z : TensorDegree.{u, v, w, t, s, o} X R K M U d)
    (z' : TensorDegree.{u, v, w, t, s, o} X R K M U d') (hz : HEq z z') :
    HEq (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d).app U z)
      (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d').app U z') := by
  cases hd
  cases hz
  rfl

omit [ScalarSections.{u, v, w, t, s, o} X R] in
private lemma tensorSheafifiedPure_heq
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (p q n : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
    (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n) (y : ((liftComplex.{u, v, w, t, s} X K).X
        q).val.obj U) :
    HEq (tensorSheafifiedPure.{u, v, w, t, s, o} X R K M (p+n) q U
      ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
        M.smul_mem p n x a x.property a.property⟩ y)
      (tensorSheafifiedPure.{u, v, w, t, s, o} X R K M p (q+n) U x
        ((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q+n) rfl).val.app U y)) := by
  let b := tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U ((p+n)+q) p q n rfl (by omega) x a
    y
  change HEq
    (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f ((p+n)+q)).app U
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U ((p+n)+q) (p+n) q rfl ⟨_, _⟩ y))
    (((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f (p+(q+n))).app U
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+(q+n)) p (q+n) rfl x _))
  rw [b]
  exact tensorSectionwiseUnit_heq.{u, v, w, t, s, o} X R K M U _ _ (by omega) _ _
    (tensorDegreePure_heq.{u, v, w, t, s, o} X R K M U ((p+n)+q) (p+(q+n)) p (q+n)
      (by omega) rfl x _)

private noncomputable def tensorDataOfAdjunction
    (adj : (tensorDG.{u, v, w, t, s, o} X R K).onComp ⊣ (Rep.{u, v, w, t, s, o} X R
      K).functor.onComp) :
    TensorWithComplexData.{u, v, w, t, s, o} X R K where
  functor := tensorDG.{u, v, w, t, s, o} X R K
  sectionwise := tensorSectionwise.{u, v, w, t, s, o} X R K
  sectionwisePure M p q U := tensorDegreePure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl
  sectionwisePure_balance M p q n U x a y :=
    (heq_of_eq (tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U ((p+n)+q) p q n rfl (by omega)
      x a
        y)).trans
      (tensorDegreePure_heq.{u, v, w, t, s, o} X R K M U ((p+n)+q) (p+(q+n)) p (q+n) (by omega) rfl
        x _)
  sectionwisePure_smul M p q U x r y := (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U
      (p+q)).map_smul p q rfl x r y
  sectionwisePure_natural M p q _ _ f x y := tensorDegreeRestriction_pure.{u, v, w, t, s, o} X R K M
    f
      (p+q) p q rfl x y
  sectionwiseTensorUniversal M U d P b := by
    obtain ⟨f, hf, hu⟩ := tensorDegreeUniversal.{u, v, w, t, s, o} X R K M U d P b
    refine ⟨f, ?_, ?_⟩
    · intro p q h x y
      cases h
      exact hf p q rfl x y
    · intro g hg
      apply hu g
      intro p q h x y
      cases h
      exact hg p q rfl x y
  sectionwisePure_d M p q U x y := by
    change (CochainComplex.of.d _ (tensorPresheafDifferential.{u, v, w, t, s, o} X R K M) (p+q)
        (p+q+1)).app U _ = _
    rw [CochainComplex.of_d]
    rw [tensorDegreePure_cast, tensorDegreePure_cast] <;> try omega
    exact tensorDegreeDifferential_pure.{u, v, w, t, s, o} X R K M U (p+q) p q rfl x y
  sectionwiseToSheaf := tensorSectionwiseUnit.{u, v, w, t, s, o} X R K
  sectionwiseUniversal := tensorSectionwiseUnit_universal.{u, v, w, t, s, o} X R K
  pure := tensorSheafifiedPure.{u, v, w, t, s, o} X R K
  pure_eq_sectionwise _ _ _ _ _ _ := rfl
  pure_balance := tensorSheafifiedPure_heq.{u, v, w, t, s, o} X R K
  map_pure := by
    intro L M n f p q U x y
    let d := p+q
    let d' := p+q+n
    have hn := (PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.naturality
        (tensorPresheafMap.{u, v, w, t, s, o} X R K f d d' rfl)
    have hv := congrArg (fun a => (a.app U).hom
      (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q rfl x y)) hn
    change ((tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M).f d').app U
        (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d d' rfl
          (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q rfl x y)) =
      (((tensorSheafifiedCochain.{u, v, w, t, s, o} X R K f).v d d' rfl).val.app U)
        (tensorSheafifiedPure.{u, v, w, t, s, o} X R K L p q U x y) at hv
    rw [tensorDegreeMap_pure] at hv
    exact (heq_of_eq hv.symm).trans
      (tensorSectionwiseUnit_heq.{u, v, w, t, s, o} X R K M U d' ((p+n)+q) (by dsimp [d']; omega) _
        _
        (tensorDegreePure_heq.{u, v, w, t, s, o} X R K M U d' ((p+n)+q) (p+n) q
          (by dsimp [d']; omega) rfl (homogeneousGradedMap f p x) y))
  adjunction := adj


end TensorPackage

/-- Tensoring with `K`, as the DG left adjoint to the representable DG functor
`Hom(K, -)`. -/
@[stacks 09LV "the differential graded tensor functor", no_expose]
public noncomputable def tensorWithComplexDG
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) : TensorWithComplexData.{u, v, w, t, s, o} X R K :=
  tensorDataOfAdjunction.{u, v, w, t, s, o} X R K (tensorAdjunction.{u, v, w, t, s, o} X R K)

private theorem tensorWithComplexDG_adjunction_homEquiv_eq
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (g : (CompDG.{u, v, w, t, s, o} X R).Cocycle
      ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) P) :
    (tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.homEquiv M P g =
      tensorHomEquiv.{u, v, w, t, s, o} X R K M P g := by
  change (tensorAdjunction.{u, v, w, t, s, o} X R K).homEquiv M P g = _
  rw [tensorAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- **The tensor--Hom adjunction of Tag 09LV on pure tensors.** For a closed degree-zero map
`g : M ⊗_E K ⟶ P`, the homogeneous element `x` of `M` is sent by the adjoint map `M ⟶ Hom(K, P)`
to the cochain `K ⟶ P` whose component at a section `y` is `g (x ⊗ y)`. -/
public theorem tensorWithComplexDG_adjunction_homEquiv_apply
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (g : (CompDG.{u, v, w, t, s, o} X R).Cocycle
      ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) P)
    (p q : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    (((((Rep.{u, v, w, t, s, o} X R K).moduleHom P p
        ⟨((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.homEquiv M P g).1.1 x, by
          have h := ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.homEquiv M P g).1.2.1
            p x x.property
          rw [add_zero] at h
          exact h⟩).v q (p + q) (by omega)).val.app U) y) =
      ((g.1.v (p + q) (p + q) (add_zero _)).val.app U)
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).pure M p q U x y) := by
  have h := tensorHomEquiv_pure.{u, v, w, t, s, o} X R K M P g p q (p + q) rfl U x y
  rw [← tensorWithComplexDG_adjunction_homEquiv_eq] at h
  exact h

/-- Tensoring the regular endomorphism module with `K` returns `K`. -/
@[stacks 09LV "the image of the regular module", no_expose]
public noncomputable def tensorWithComplexDG_regular
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    letI : Category (CompDG.{u, v, w, t, s, o} X R).Obj := (CompDG.{u, v, w, t, s, o} X
      R).instCategoryComp
    (((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) :
        (CompDG.{u, v, w, t, s, o} X R).Comp) ≅
      (liftComplex.{u, v, w, t, s} X K : (CompDG.{u, v, w, t, s, o} X R).Comp)) :=
  by
  letI : Category (CompDG.{u, v, w, t, s, o} X R).Obj :=
    (CompDG.{u, v, w, t, s, o} X R).instCategoryComp
  let e := regularSheafIso.{u, v, w, t, s, o} X R K (tensorWithComplexDG.{u, v, w, t, s, o} X R K)
  refine ⟨CochainComplex.HomComplex.Cocycle.ofHom e.hom,
    CochainComplex.HomComplex.Cocycle.ofHom e.inv, ?_, ?_⟩
  · apply Subtype.ext
    change (CochainComplex.HomComplex.Cochain.ofHom e.hom).comp
      (CochainComplex.HomComplex.Cochain.ofHom e.inv) (by omega) = _
    rw [← CochainComplex.HomComplex.Cochain.ofHom_comp, e.hom_inv_id]
    rfl
  · apply Subtype.ext
    change (CochainComplex.HomComplex.Cochain.ofHom e.inv).comp
      (CochainComplex.HomComplex.Cochain.ofHom e.hom) (by omega) = _
    rw [← CochainComplex.HomComplex.Cochain.ofHom_comp, e.inv_hom_id]
    rfl

/-- Tensoring with `K` commutes with all small direct sums. -/
@[stacks 09LV "preservation of direct sums"]
public theorem tensorWithComplexDG_preservesCoproducts
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) (I : Type i) :
    PreservesColimitsOfShape (Discrete I)
      (tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.onComp := by
  exact (tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.leftAdjoint_preservesColimits
    |>.preservesColimitsOfShape

end AlgebraicGeometry.RingedSite
