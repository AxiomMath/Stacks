module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorNatTransCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomTensorComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTransPositions

/-! # The second assertion of Stacks 0BZ0

Let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras, let `T` be a
differential graded `(A, B)`-bimodule and let `S = Hom_{Mod^{dg}_{(B, d)}}(T, B)` with the
differential graded `(B, A)`-bimodule structure of
`DifferentialGraded.Bimodule.homDualBimodule`, which is the first assertion of
[Stacks, Tag 0BZ0]. Assume

1. `T` defines a compact object of `D(B, d)`, and
2. `S` represents `R Hom(T, B)` in `D(A, d)`, that is, the comparison of Tag 09LI is invertible
   at the regular module `B`.

Then there is an isomorphism `N ⊗_B^𝐋 S ⟶ R Hom(T, N)` functorial in `N` in `D(B, d)`. That is
the second assertion of Tag 0BZ0 and it is proved here, as an isomorphism of the two functors
`D(B, d) ⥤ D(A, d)` of Tag 09LS and Tag 09LI.

## Main definitions

* `DifferentialGraded.Bimodule.derivedEvalNatTrans`: the comparison
  `- ⊗_B^𝐋 S ⟶ R Hom(T, -)`.
* `DifferentialGraded.Bimodule.derivedTensorHomDualFunctorIso`: **Stacks 0BZ0**, second
  assertion.

## Main results

* `DifferentialGraded.Bimodule.evalModuleNatTrans_commShift` and its descendants: the pairing
  `c : - ⊗_B S ⟶ Hom^•_B(T, -)` commutes with the shift.
* `DifferentialGraded.Bimodule.evalHom_regular`: at the regular module the pairing is the unit
  identification of Tag 0FQN, hence invertible.
* `DifferentialGraded.Bimodule.isIso_derivedEvalNatTrans`: the comparison is invertible.

## Implementation notes

*How the map is constructed, and why no Kan extension is used.* The comparison of Tag 09LS is a
transformation `ε : Q ⋙ (- ⊗_B^𝐋 S) ⟶ - ⊗_B S` on `K(B, d)` and the comparison of Tag 09LI is a
transformation `η : Hom^•_B(T, -) ⟶ Q ⋙ R Hom(T, -)` there; the pairing of Tag 09LC gives
`γ : - ⊗_B S ⟶ Hom^•_B(T, -)`, which is
`DifferentialGraded.Bimodule.evalToDerivedCategoryNatTrans`. The composite
`ε ≫ γ ≫ η : Q ⋙ (- ⊗_B^𝐋 S) ⟶ Q ⋙ R Hom(T, -)` then *descends* along the localization
`Q : K(B, d) ⥤ D(B, d)`, because whiskering with a localization functor is fully faithful on
transformations — `CategoryTheory.Localization.liftNatTrans`. No universal property of either
derived functor is used, and in particular the fact that both Kan extensions produce
transformations `R Hom(T, -) ⟶ - ⊗_B^𝐋 S`, in the direction opposite to the one asserted, is
irrelevant.

*The dévissage.* Invertibility is checked by Tag 0FQE. At a direct sum it is formal: `- ⊗_B^𝐋 S`
is a left adjoint by Tag 09LT, and `R Hom(T, -)` commutes with direct sums by
`DifferentialGraded.Bimodule.preservesColimitsOfShape_discrete_derivedHomFunctor`, which is where
hypothesis (1) is spent. Along a distinguished triangle it is the five lemma, both functors being
exact — `DifferentialGradedModule.derivedHomFunctor_isTriangulated` for the second — applied to
the triangle morphism with all three components the comparison, which exists because the
comparison commutes with the translation. At the regular module the comparison is the composite
of three invertible maps: `ε` is invertible there because the regular module is orthogonal on
the left to the acyclic modules (Tag 09K1), `γ` is invertible there because `c_B` is the unit
identification of Tag 0FQN, and `η` is invertible there by hypothesis (2). The shifts `B[k]`
follow from the unshifted case by the compatibility of the comparison with the translation.

## References

* [Stacks Project, Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0); the pairing is
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the derived functors are
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), the dévissage is
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE), the adjunction is
  [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT), the shift comparison of the tensor
  product is [Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN), and the left orthogonality of
  the regular module is [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1).
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The comparison `c` and the shift -/

/-- Two `R`-bilinear maps out of `N × S` agreeing on homogeneous pairs are equal. -/
private theorem bilinear_ext_of_homogeneous (T : Bimodule A B)
    (N : DifferentialGradedModule.{u, u, u} B) {Z : Type*} [AddCommGroup Z] [Module R Z]
    (F G : N.M →ₗ[R] (homDualModule T).M →ₗ[R] Z)
    (h : ∀ (q p : ℤ) (x : N.grading q) (f : (homDualModule T).grading p), F x.1 f.1 = G x.1 f.1)
    (y : N.M) (f : (homDualModule T).M) : F y f = G y f := by
  induction y using DirectSum.Decomposition.inductionOn N.grading with
  | zero => simp
  | @homogeneous q x =>
    induction f using DirectSum.Decomposition.inductionOn (homDualModule T).grading with
    | zero => simp
    | @homogeneous p g => exact h q p x g
    | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- The shift comparison of Tag 0FQR carries the value of the pairing `c` on `M` to its value on
`M[n]`, on homogeneous elements: both homogeneous maps send `t` to `y · f t`. -/
theorem homPresentationShiftIso_hom_evalTotal_graded (T : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} B) (n q p : ℤ)
    (x : (DifferentialGradedModule.shift M n).grading q)
    (f : (homDualModule T).grading p) :
    (homPresentationShiftIso A B T.rightModule T.leftAction M n).hom.toFun
        (evalTotal T M x.1 f.1) =
      evalTotal T (DifferentialGradedModule.shift M n) x.1 f.1 := by
  set hpsi := (homPresentationShiftIso A B T.rightModule T.leftAction M n).hom
  let xM : M.grading (q + n) := ⟨x.1, x.property⟩
  let u : (homPresentation T M).module.grading (q + p + n) :=
    ⟨evalTotal T M x.1 f.1, mem_grading_congr (show q + n + p = q + p + n by omega)
      (evalTotal_mem T M (q + n) p xM f)⟩
  have hw : hpsi.toFun (evalTotal T M x.1 f.1) ∈
      (homPresentation T (DifferentialGradedModule.shift M n)).module.grading (q + p) :=
    hpsi.map_grading (q + p) u.1 u.property
  refine Eq.trans (homModule_val_ext T (DifferentialGradedModule.shift M n)
    (rfl : q + p = q + p) ⟨hpsi.toFun (evalTotal T M x.1 f.1), hw⟩ (evalGraded T x f) ?_)
    (evalTotal_eq_evalGraded T (DifferentialGradedModule.shift M n) x f).symm
  intro k t
  refine Eq.trans (homPresentationShiftIso_apply A B T.rightModule T.leftAction M n
    (q + p) k u t) ?_
  refine Eq.trans (homogeneousEquiv_val_apply_congr (homPresentation T M)
    (show q + p + n = q + n + p by omega) u (evalGraded T xM f)
    (evalTotal_eq_evalGraded T M xM f) t) ?_
  have hev : ∀ (N : DifferentialGradedModule.{u, u, u} B) (m : ℤ) (z : N.grading m),
      (((homPresentation T N).homogeneousEquiv (m + p) (evalGraded T z f)).1 t : N.M) =
        MulOpposite.op ((((homDualPresentation T).homogeneousEquiv p) f).1
          (t : T.rightModule.M)) • z.1 := fun N m z => by
    rw [homogeneousEquiv_evalGraded, evalPair_apply]
  exact (hev M (q + n) xM).trans (hev (DifferentialGradedModule.shift M n) q x).symm

/-- The shift comparison of Tag 0FQR carries the value of the pairing `c` on `M` to its value on
`M[n]`. -/
theorem homPresentationShiftIso_hom_evalTotal (T : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) (y : M.M)
    (f : (homDualModule T).M) :
    (homPresentationShiftIso A B T.rightModule T.leftAction M n).hom.toFun
        (evalTotal T M y f) =
      evalTotal T (DifferentialGradedModule.shift M n) y f := by
  exact bilinear_ext_of_homogeneous T (DifferentialGradedModule.shift M n)
    ((evalTotal T M).compr₂
      (homPresentationShiftIso A B T.rightModule T.leftAction M n).hom.toFun)
    (evalTotal T (DifferentialGradedModule.shift M n))
    (homPresentationShiftIso_hom_evalTotal_graded T M n) y f


/-- **The comparison `c : - ⊗_B S ⟶ Hom^•_B(T, -)` commutes with the shift.** Both sides are
homomorphisms out of `M[n] ⊗_B S` sending the pure tensor `y ⊗ f` to the homogeneous map
`t ↦ y · f t`; on the source the comparison of Tag 0FQN is sign-free on pure tensors, and on the
target the comparison of Tag 0FQR is characterized by the values of the homogeneous maps. -/
instance evalModuleNatTrans_commShift (T : Bimodule A B) :
    NatTrans.CommShift (evalModuleNatTrans T) ℤ := by
  refine ⟨fun n => ?_⟩
  ext M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  refine tensorObj_hom_ext' (homDualBimodule T) (DifferentialGradedModule.shift M n) _ _
    fun x y => ?_
  set e := homPresentationShiftIso A B T.rightModule T.leftAction M n
  have hid : ∀ z, e.inv.toFun (e.hom.toFun z) = z := fun z =>
    LinearMap.congr_fun (congrArg DifferentialGradedModule.Hom.toFun e.hom_inv_id) z
  have hkey : e.inv.toFun (evalTotal T (DifferentialGradedModule.shift M n) x y) =
      evalTotal T M x y := by
    rw [← homPresentationShiftIso_hom_evalTotal T M n x y, hid]
  have hL : ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) n).map
        ((evalModuleNatTrans T).app M)).toFun
        ((((tensorCompFunctor (homDualBimodule T)).commShiftIso n).hom.app M).toFun
          (((tensorDGFunctor (homDualBimodule T)).pure
            (DifferentialGradedModule.shift M n)).toLinearMap x y)) =
      evalTotal T M x y := by
    rw [commShiftIso_tensorCompFunctor_hom_app]
    refine Eq.trans (congrArg
      (fun z : ((tensorDGFunctor (homDualBimodule T)).functor.obj M).M =>
        ((evalModuleNatTrans T).app M).toFun z)
      (tensorShiftIso_inv_pure (homDualBimodule T) M n x y)) ?_
    exact evalHom_pure T M x y
  have hR : ((((homModuleFunctor A B T.rightModule T.leftAction).commShiftIso n).hom.app M)).toFun
        (((evalModuleNatTrans T).app (DifferentialGradedModule.shift M n)).toFun
          (((tensorDGFunctor (homDualBimodule T)).pure
            (DifferentialGradedModule.shift M n)).toLinearMap x y)) =
      evalTotal T M x y := by
    rw [show ((evalModuleNatTrans T).app (DifferentialGradedModule.shift M n)).toFun
          (((tensorDGFunctor (homDualBimodule T)).pure
            (DifferentialGradedModule.shift M n)).toLinearMap x y) =
        evalTotal T (DifferentialGradedModule.shift M n) x y from
      evalHom_pure T (DifferentialGradedModule.shift M n) x y]
    exact hkey
  exact hL.trans hR.symm


/-- The comparison `c` on the homotopy categories, before descending along the quotient by
homotopy, commutes with the shift. -/
instance evalHomotopyNatTransAux_commShift (T : Bimodule A B) :
    NatTrans.CommShift (evalHomotopyNatTransAux T) ℤ :=
  inferInstanceAs (NatTrans.CommShift
    ((tensorCompFunctor_quotient (homDualBimodule T)).inv ≫
      Functor.whiskerRight (evalModuleNatTrans T) (toHomotopyCategory A) ≫
        (homHomotopyDescent T.rightModule T.leftAction).inv) ℤ)

/-- **The comparison `c` on the homotopy categories commutes with the shift.** -/
instance evalHomotopyNatTrans_commShift (T : Bimodule A B) :
    NatTrans.CommShift (evalHomotopyNatTrans T) ℤ := by
  have : NatTrans.CommShift
      (Functor.whiskerLeft (CategoryTheory.Quotient.functor (homotopyRel B))
        (evalHomotopyNatTrans T)) ℤ := by
    rw [show Functor.whiskerLeft (CategoryTheory.Quotient.functor (homotopyRel B))
        (evalHomotopyNatTrans T) = evalHomotopyNatTransAux T from
      CategoryTheory.whiskerLeft_natTransLift _]
    infer_instance
  exact NatTrans.commShift_of_whiskerLeft_quotientFunctor ℤ (evalHomotopyNatTrans T)

/-- **The comparison `c`, with the target localized, commutes with the shift.** -/
instance evalToDerivedCategoryNatTrans_commShift (T : Bimodule A B) :
    NatTrans.CommShift (evalToDerivedCategoryNatTrans T) ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Functor.whiskerRight (evalHomotopyNatTrans T) (quasiIsomorphisms' A).Q) ℤ)


/-- The transformation `c` read on the homotopy category of `B`, with both derived functors
already defined on `D(B, d)`: the counit of Tag 09LS, the comparison `c`, and the unit of
Tag 09LI, composed. -/
def evalDerivedAux (T : Bimodule A B) :
    (quasiIsomorphisms' B).Q ⋙ derivedTensorFunctor (homDualBimodule T) ⟶
      (quasiIsomorphisms' B).Q ⋙ (derivedHomData A B T.rightModule T.leftAction).functor :=
  derivedTensorFunctorCounit (homDualBimodule T) ≫ evalToDerivedCategoryNatTrans T ≫
    (derivedHomData A B T.rightModule T.leftAction).comparison

/-- The composite `evalDerivedAux T` of the counit of Tag 09LS, the comparison `c` and the unit
of Tag 09LI commutes with the shift. -/
instance evalDerivedAux_commShift (T : Bimodule A B) :
    NatTrans.CommShift (evalDerivedAux T) ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (derivedTensorFunctorCounit (homDualBimodule T) ≫ evalToDerivedCategoryNatTrans T ≫
      (derivedHomData A B T.rightModule T.leftAction).comparison) ℤ)

/-- **The comparison `N ⊗_B^𝐋 S ⟶ R Hom(T, N)` of Stacks 0BZ0**, as a transformation of
functors `D(B, d) ⥤ D(A, d)`. -/
def derivedEvalNatTrans (T : Bimodule A B) :
    derivedTensorFunctor (homDualBimodule T) ⟶
      (derivedHomData A B T.rightModule T.leftAction).functor :=
  Localization.liftNatTrans (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    ((quasiIsomorphisms' B).Q ⋙ derivedTensorFunctor (homDualBimodule T))
    ((quasiIsomorphisms' B).Q ⋙ (derivedHomData A B T.rightModule T.leftAction).functor)
    (derivedTensorFunctor (homDualBimodule T))
    (derivedHomData A B T.rightModule T.leftAction).functor (evalDerivedAux T)

/-- **The comparison of Stacks 0BZ0 commutes with the shift**, being the lift through the
localization of `evalDerivedAux T`, which does. -/
instance derivedEvalNatTrans_commShift (T : Bimodule A B) :
    NatTrans.CommShift (derivedEvalNatTrans T) ℤ :=
  Localization.liftNatTrans_compLeft_commShift (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    (derivedTensorFunctor (homDualBimodule T))
    (derivedHomData A B T.rightModule T.leftAction).functor ℤ (evalDerivedAux T)

/-- At the image in `D(B, d)` of an object of the homotopy category of `B`, the comparison of
Stacks 0BZ0 is the component of `evalDerivedAux T`. -/
theorem derivedEvalNatTrans_app_q (T : Bimodule A B) (X : HomotopyCategory B) :
    (derivedEvalNatTrans T).app ((quasiIsomorphisms' B).Q.obj X) =
      (evalDerivedAux T).app X := by
  simp [derivedEvalNatTrans]


/-! ### The comparison at the regular module -/

/-- **The pairing `c_B` is the unit identification**, on homogeneous elements: both send
`x ⊗ f` to the homogeneous map `t ↦ x · f t`, which is `t ↦ x * f t` on the regular module. -/
theorem evalTotal_regular_graded (T : Bimodule A B) (n p : ℤ) (x : B.grading n)
    (f : (homDualModule T).grading p) :
    evalTotal T (regularModule B) x.1 f.1 =
      leftActionTotal B A (homDualModule T) (homDualBimodule T).leftAction.1 x.1 f.1 := by
  have hR : leftActionTotal B A (homDualModule T) (homDualBimodule T).leftAction.1 x.1 f.1 =
      (homDualSmul T x f : (homDualModule T).M) := by
    rw [leftActionTotal_apply B A (homDualModule T) (homDualBimodule T).leftAction.1 n x]
    exact totalizeCochain_apply_of_eq A (homDualModule T) n p (p + n) rfl _ f
  rw [hR, evalTotal_eq_evalGraded T (regularModule B) x f]
  refine homModule_val_ext T (regularModule B) (show n + p = p + n by omega)
    (evalGraded T x f) (homDualSmul T x f) ?_
  intro k t
  rw [homogeneousEquiv_evalGraded, evalPair_apply,
    homDualBimodule_action_apply T n p k x f t, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]

/-- **The pairing `c_B` is the unit identification.** -/
theorem evalTotal_regular (T : Bimodule A B) (x : (regularModule B).M)
    (f : (homDualModule T).M) :
    evalTotal T (regularModule B) x f =
      leftActionTotal B A (homDualModule T) (homDualBimodule T).leftAction.1 x f := by
  exact bilinear_ext_of_homogeneous T (regularModule B) (evalTotal T (regularModule B))
    (leftActionTotal B A (homDualModule T) (homDualBimodule T).leftAction.1)
    (evalTotal_regular_graded T) x f

/-- **The comparison `c_B : B ⊗_B S ⟶ Hom^•_B(T, B)` is the unit isomorphism of Tag 0FQN.** -/
theorem evalHom_regular (T : Bimodule A B) :
    evalHom T (regularModule B) = (tensorRegularIso (homDualBimodule T)).1.hom := by
  refine tensorObj_hom_ext' (homDualBimodule T) (regularModule B) _ _ fun x y => ?_
  refine (evalHom_pure T (regularModule B) x y).trans ?_
  exact (evalTotal_regular T x y).trans ((tensorRegularIso (homDualBimodule T)).2 x y).symm

/-- **The comparison `c` is invertible at the regular module** in the derived category. -/
theorem isIso_evalToDerivedCategoryNatTrans_app_regular (T : Bimodule A B) :
    IsIso ((evalToDerivedCategoryNatTrans T).app
      ((toHomotopyCategory B).obj (regularModule B))) := by
  have : IsIso ((evalModuleNatTrans T).app (regularModule B)) := by
    rw [show (evalModuleNatTrans T).app (regularModule B) =
      (tensorRegularIso (homDualBimodule T)).1.hom from evalHom_regular T]
    exact Iso.isIso_hom _
  have : IsIso ((evalHomotopyNatTrans T).app
      ((toHomotopyCategory B).obj (regularModule B))) := by
    rw [evalHomotopyNatTrans_app T (regularModule B)]
    infer_instance
  rw [evalToDerivedCategoryNatTrans_app T ((toHomotopyCategory B).obj (regularModule B))]
  exact Functor.map_isIso _ _


/-! ### The second assertion of Stacks 0BZ0 -/

/-- **The comparison `N ⊗_B^𝐋 S ⟶ R Hom(T, N)` is invertible**, under the two hypotheses of
Stacks 0BZ0: `T` is compact in `D(B, d)`, and `S = Hom^•_B(T, B)` computes `R Hom(T, B)`.

The dévissage of Tag 0FQE reduces this to three clauses. At a direct sum it is formal: the
derived tensor product is a left adjoint, and derived Hom out of `T` commutes with direct sums
because `T` is compact. Along a distinguished triangle it is the five lemma, both functors being
exact. At the shifts `B[k]` of the regular module it is the composite of three invertible maps:
the comparison of Tag 09LS at the regular module, which is invertible because the regular module
is orthogonal on the left to the acyclic ones; the pairing `c_B`, which is the unit
identification of Tag 0FQN; and the comparison of Tag 09LI at the regular module, which is
hypothesis (2). The shifts come from the unshifted case because the comparison commutes with the
translation. -/
theorem isIso_derivedEvalNatTrans (T : Bimodule A B)
    (h1 : IsCompactObject.{u}
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj T.rightModule))
    (h2 : IsIso ((derivedHomData A B T.rightModule T.leftAction).comparison.app
      ((toHomotopyCategory B).obj (regularModule B)))) :
    IsIso (derivedEvalNatTrans T) := by
  have hc : IsCompactObject.{u} ((derivedTensorFunctor T).obj
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))) :=
    isCompactObject_of_iso (derivedTensorRegularIso T) h1
  have hF := (derivedTensorFunctor_adj_derivedHomFunctor
    (homDualBimodule T)).leftAdjoint_preservesColimits
  have hreg : IsIso ((derivedEvalNatTrans T).app
      ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj (regularModule B)))) := by
    rw [derivedEvalNatTrans_app_q T ((toHomotopyCategory B).obj (regularModule B))]
    have hε := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal (homDualBimodule T)
      ((toHomotopyCategory B).obj (regularModule B))
      (leftOrthogonal_acyclic_toHomotopyCategory_regularModule B)
    have hγ := isIso_evalToDerivedCategoryNatTrans_app_regular T
    exact inferInstanceAs (IsIso ((derivedTensorFunctorCounit (homDualBimodule T)).app
      ((toHomotopyCategory B).obj (regularModule B)) ≫
        ((evalToDerivedCategoryNatTrans T).app
            ((toHomotopyCategory B).obj (regularModule B)) ≫
          (derivedHomData A B T.rightModule T.leftAction).comparison.app
            ((toHomotopyCategory B).obj (regularModule B)))))
  have key : ∀ X, IsIso ((derivedEvalNatTrans T).app X) := by
    refine property_of_coproducts_of_two_out_of_three_of_shifts B
      (fun X => IsIso ((derivedEvalNatTrans T).app X)) (fun {ι} K hK => ?_)
      (fun Δ hΔ => ⟨?_, ?_, ?_⟩) (fun k => ?_)
    · have := preservesColimitsOfShape_discrete_derivedHomFunctor T ι
      exact StacksDraft.NatTransDevissage.isIso_app_of_isColimit (derivedEvalNatTrans T)
        (Discrete.functor K) (Limits.colimit.isColimit _) fun j => hK j.as
    · exact fun ha hb => StacksDraft.NatTransDevissage.isIso_app_obj₃ (derivedEvalNatTrans T)
        Δ hΔ ha hb
    · exact fun ha hb => StacksDraft.CompactDevissage.isIso_app_obj₂ (derivedEvalNatTrans T)
        Δ hΔ ha hb
    · exact fun ha hb => StacksDraft.CompactDevissage.isIso_app_obj₁ (derivedEvalNatTrans T)
        Δ hΔ ha hb
    · exact StacksDraft.NatTransDevissage.isIso_app_shift (derivedEvalNatTrans T) hreg k
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 0BZ0, second assertion.** Let `R` be a ring, let `(A, d)` and `(B, d)` be
differential graded `R`-algebras and let `T` be a differential graded `(A, B)`-bimodule. Assume

1. `T` defines a compact object of `D(B, d)`, and
2. `S = Hom_{Mod^{dg}_{(B, d)}}(T, B)` represents `R Hom(T, B)` in `D(A, d)`, that is, the
   comparison of Tag 09LI is invertible at the regular module.

Then there is an isomorphism `N ⊗_B^𝐋 S ⟶ R Hom(T, N)` functorial in `N` in `D(B, d)`: the
differential graded `(B, A)`-bimodule structure on `S` is
`DifferentialGraded.Bimodule.homDualBimodule`, and the functorial isomorphism is an isomorphism
of the two functors `D(B, d) ⥤ D(A, d)` of Tag 09LS and Tag 09LI.

The map itself is `DifferentialGraded.Bimodule.derivedEvalNatTrans`: the composition pairing of
Tag 09LC, read on differential graded modules and descended to the derived category, lifted
along the localization `K(B, d) ⥤ D(B, d)`. -/
@[stacks 0BZ0 "the second assertion: the functorial isomorphism N ⊗_B^L S ≅ RHom(T, N)"]
def derivedTensorHomDualFunctorIso (T : Bimodule A B)
    (h1 : IsCompactObject.{u}
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj T.rightModule))
    (h2 : IsIso ((derivedHomData A B T.rightModule T.leftAction).comparison.app
      ((toHomotopyCategory B).obj (regularModule B)))) :
    derivedTensorFunctor (homDualBimodule T) ≅
      (derivedHomData A B T.rightModule T.leftAction).functor :=
  have := isIso_derivedEvalNatTrans T h1 h2
  asIso (derivedEvalNatTrans T)

end DifferentialGraded.Bimodule

end
