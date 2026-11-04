module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlipBalance
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictLeft
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangePlainComparison
public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractDerived

/-! # The flip of a restricted regular module, and the plain base change

Let `φ : A → A₀` be a homomorphism of differential graded algebras over a commutative ring `R`.
The graded opposite of `A₀`, restricted along the graded opposite of `φ`, is a right
differential graded `A^{opp}`-module `X`: it is `A₀` with `A` acting on the left through `φ`,
recorded over `A^{opp}`. Read as a differential graded `(A, R)`-bimodule
(`DifferentialGraded.Bimodule.unflip`) it is the regular `(A, A₀)`-bimodule of `φ` with its right
action restricted to `R`, by the identification of the underlying graded module of the graded
opposite with that of `A₀`. This file records that identification and its consequence for tensor
products: for a right differential graded `A`-module `N`, the relative tensor product
`X ⊗_{A^{opp}} N̂` with the flip of `N` is `N ⊗_A A₀` read over `R`, and a semilinear homomorphism
`g : N ⟶ N₀|_φ` induces on these tensor products the plain transpose `N ⊗_A A₀ ⟶ N₀` of `g`, when
the target is tensored with the graded opposite of `A₀` itself.

## Main definitions

* `DifferentialGraded.Bimodule.restrictedRegularOpp`: the right differential graded
  `A^{opp}`-module `X` above.
* `DifferentialGraded.Bimodule.unflipRestrictedRegularIso`: `unflip X` is the regular bimodule of
  `φ` with its right action restricted to `R`.
* `DifferentialGraded.Bimodule.flipRestrictedRegularIso`: `X ⊗_{A^{opp}} N̂ ≅ (N ⊗_A A₀)|_R`.

## Main results

* `DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso_hom_pure`: restricting the right
  algebra of a bimodule does not change the pure tensors.
* `DifferentialGraded.Bimodule.quasiIso_flip_tensor_of_quasiIso_plainTranspose`: **if the plain
  transpose `N ⊗_A A₀ ⟶ N₀` of `g` is a quasi-isomorphism, so is the homomorphism
  `X ⊗_{A^{opp}} N̂ ⟶ X₀ ⊗_{A₀^{opp}} N̂₀` that `g` induces**, where `X₀` is the graded opposite
  of `A₀` restricted along a homomorphism `A₀ → A₀` acting as the identity.

## References

* [Stacks Project, Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0) and
  [Tag 09JG](https://stacks.math.columbia.edu/tag/09JG).
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), extension and
  restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A A₀ : DifferentialGradedAlgebra.{u, u} R}

/-! ### Restricting the right algebra does not change the pure tensors -/

/-- The inverse of the right unitor sends `x` to `x ⊗ 1`. -/
theorem tensorRegularRightIso_inv_toFun {C S : DifferentialGradedAlgebra.{u, u} R} (ψ : C.Hom S)
    (M : DifferentialGradedModule.{u, u, u} S) (x : M.M) :
    (tensorRegularRightIso ψ M).inv.toFun x =
      ((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x (1 : S.A) := by
  have h := tensorRegularRightIso_hom_pure ψ M x (1 : S.A)
  rw [MulOpposite.op_one, one_smul] at h
  have h' := congrArg (tensorRegularRightIso ψ M).inv.toFun h
  refine h'.symm.trans ?_
  have hid := (tensorRegularRightIso ψ M).hom_inv_id
  exact congrArg (fun f : tensorObj' (regularRight ψ) M ⟶ tensorObj' (regularRight ψ) M =>
    f.toFun (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x (1 : S.A))) hid

/-- **Restricting the right algebra of a bimodule does not change the pure tensors**: the
identification `DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso` carries `x ⊗ y` to
`x ⊗ y`. -/
theorem tensorCompFunctorRestrictRightIso_hom_pure {B C S : DifferentialGradedAlgebra.{u, u} R}
    (ψ : C.Hom S) (N : Bimodule B S) (M : DifferentialGradedModule.{u, u, u} B) (x : M.M)
    (y : N.rightModule.M) :
    ((tensorCompFunctorRestrictRightIso ψ N).hom.app M).toFun
        (((tensorDGFunctor (Bimodule.restrictRight ψ N)).pure M).toLinearMap x y) =
      ((tensorDGFunctor N).pure M).toLinearMap x y := by
  have h1 := tensorHomOfBimoduleHom_pure (compTensorRegularRightIso ψ N).inv M x y
  have h3 := tensorRegularRightIso_inv_toFun ψ N.rightModule y
  have h4 := assocForward_pure N (regularRight ψ) M x y (1 : S.A)
  have h5 := tensorRegularRightIso_hom_pure ψ ((tensorCompFunctor N).obj M)
    (((tensorDGFunctor N).pure M).toLinearMap x y) (1 : S.A)
  refine Eq.trans ?_ (h5.trans ?_)
  rotate_left
  · rw [MulOpposite.op_one]
    exact @one_smul (MulOpposite S.A) _ _
      (((tensorCompFunctor N).obj M).rmodule.toDistribMulAction.toMulAction) _
  show (tensorRegularRightIso ψ ((tensorCompFunctor N).obj M)).hom.toFun
    ((assocForward N (regularRight ψ) M).toFun
      ((tensorHomOfBimoduleHom (compTensorRegularRightIso ψ N).inv M).toFun
        (((tensorDGFunctor (Bimodule.restrictRight ψ N)).pure M).toLinearMap x y))) = _
  refine congrArg (tensorRegularRightIso ψ ((tensorCompFunctor N).obj M)).hom.toFun ?_
  refine Eq.trans ?_ h4
  refine congrArg (assocForward N (regularRight ψ) M).toFun ?_
  refine h1.trans ?_
  exact congrArg ((tensorPure (compTensor N (regularRight ψ)) M).toLinearMap x) h3

/-! ### The flip of a restricted regular module -/

/-- **`A₀` as a left differential graded `A`-module through `ψ`, recorded as a right
differential graded `A^{opp}`-module**: the graded opposite of `A₀` restricted along the graded
opposite of `ψ`. -/
abbrev restrictedRegularOpp (ψ : A.Hom A₀) : DifferentialGradedModule.{u, u, u} (oppAlgebra A) :=
  restrictScalars (oppHom ψ) (regularModule (oppAlgebra A₀))

/-- The right action of `A^{opp}` on `DifferentialGraded.Bimodule.restrictedRegularOpp` is
multiplication in the graded opposite of `A₀` by the image under the graded opposite of `ψ`. -/
theorem restrictedRegularOpp_op_smul (ψ : A.Hom A₀) (a : (oppAlgebra A).A)
    (x : (restrictedRegularOpp ψ).M) :
    MulOpposite.op a • x = (show (oppAlgebra A₀).A from x) * (oppHom ψ).toAlgebraHom a := rfl

section Unflip

variable (ψ φ : A.Hom A₀) (hψφ : ∀ a, ψ.toAlgebraHom a = φ.toAlgebraHom a)

/-- The identification of the underlying graded modules, from the right module of `unflip X` to
the regular module of `A₀` read over `R`. -/
def unflipRestrictedRegularHom :
    (unflip (restrictedRegularOpp ψ)).rightModule ⟶
      (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).rightModule where
  toFun := (opposite R A₀).equiv.toLinearMap
  map_smul x c := by
    rw [op_smul_eq_smul_of_smul_one _ (show c = c • (1 : (degreeZero R R).A) by simp) x,
      op_smul_eq_smul_of_smul_one _ (show c = c • (1 : (degreeZero R R).A) by simp)]
    exact (opposite R A₀).equiv.map_smul c x
  map_grading n x hx := ((opposite R A₀).mem_grading_iff n x).1 hx
  map_d := LinearMap.ext fun x => (opposite R A₀).map_d x

/-- The inverse identification. -/
def unflipRestrictedRegularInv :
    (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).rightModule ⟶
      (unflip (restrictedRegularOpp ψ)).rightModule where
  toFun := (opposite R A₀).equiv.symm.toLinearMap
  map_smul y c := by
    rw [op_smul_eq_smul_of_smul_one _ (show c = c • (1 : (degreeZero R R).A) by simp) y,
      op_smul_eq_smul_of_smul_one _ (show c = c • (1 : (degreeZero R R).A) by simp)]
    exact (opposite R A₀).equiv.symm.map_smul c y
  map_grading n y hy := by
    have h : ∀ z : A₀.A, z ∈ A₀.grading n →
        (opposite R A₀).equiv.symm z ∈ (oppAlgebra A₀).grading n := fun z hz => by
      rw [(opposite R A₀).mem_grading_iff, LinearEquiv.apply_symm_apply]
      exact hz
    exact h y hy
  map_d := LinearMap.ext fun y => by
    have h : ∀ z : A₀.A, (opposite R A₀).equiv.symm (A₀.d z) =
        (oppAlgebra A₀).d ((opposite R A₀).equiv.symm z) := fun z => by
      apply (opposite R A₀).equiv.injective
      rw [LinearEquiv.apply_symm_apply, (opposite R A₀).map_d, LinearEquiv.apply_symm_apply]
    exact h y

/-- The identification of the underlying graded modules, as an isomorphism of right modules over
`R` placed in degree zero. -/
def unflipRestrictedRegularRightIso :
    (unflip (restrictedRegularOpp ψ)).rightModule ≅
      (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).rightModule where
  hom := unflipRestrictedRegularHom ψ φ
  inv := unflipRestrictedRegularInv ψ φ
  hom_inv_id := DifferentialGradedModule.Hom.ext
    (LinearMap.ext fun x => (opposite R A₀).equiv.symm_apply_apply x)
  inv_hom_id := DifferentialGradedModule.Hom.ext
    (LinearMap.ext fun y => (opposite R A₀).equiv.apply_symm_apply y)

/-- The left action of the regular bimodule of `φ`, with its right action restricted, is left
multiplication through `φ`. -/
theorem leftActionTotal_restrictRight_regular {m n : ℤ} {a : A.A} (ha : a ∈ A.grading m)
    {y : A₀.A} (hy : y ∈ A₀.grading n) :
    leftActionTotal A (degreeZero R R)
        (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).rightModule
        (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).leftAction.1 a y =
      φ.toAlgebraHom a * y :=
  (leftActionTotal_eq_action_v (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ))
    (⟨a, ha⟩ : A.grading m) ⟨y, hy⟩).trans
    (regularBimoduleStructure_action φ m n ⟨a, ha⟩ ⟨y, hy⟩)

include hψφ in
/-- The identification of the underlying graded modules carries the left action of `A` on
`unflip X`, on homogeneous elements. -/
theorem unflipRestrictedRegular_leftAction_of_mem {m n : ℤ} {a : A.A} (ha : a ∈ A.grading m)
    {y : (restrictedRegularOpp ψ).M} (hy : y ∈ (restrictedRegularOpp ψ).grading n) :
    (opposite R A₀).equiv (leftActionTotal A (degreeZero R R)
        (unflip (restrictedRegularOpp ψ)).rightModule
        (unflip (restrictedRegularOpp ψ)).leftAction.1 a y) =
      φ.toAlgebraHom a * (opposite R A₀).equiv y := by
  have hy' : (opposite R A₀).equiv y ∈ A₀.grading n := ((opposite R A₀).mem_grading_iff n y).1 hy
  have hb : (oppHom ψ).toAlgebraHom ((opposite R A).equiv.symm a) ∈
      (oppAlgebra A₀).grading m := by
    refine (oppHom ψ).map_grading m _ ?_
    rw [(opposite R A).mem_grading_iff, LinearEquiv.apply_symm_apply]
    exact ha
  have hb' : (opposite R A₀).equiv ((oppHom ψ).toAlgebraHom ((opposite R A).equiv.symm a)) =
      φ.toAlgebraHom a := by
    rw [oppHom_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hψφ]
  rw [leftActionTotal_unflip (restrictedRegularOpp ψ) ha hy,
    oppLeftActionRingHom_apply_mem (restrictedRegularOpp ψ)
      ((oppOppHom A).map_grading m a ha) hy, equiv_oppOppHom_apply,
    restrictedRegularOpp_op_smul, map_smul,
    (opposite R A₀).map_mul_of_mem n m _ _ hy hb, hb', Units.smul_def,
    ← Int.cast_smul_eq_zsmul R, smul_smul, mul_comm m n, negOnePowR_self_mul, one_smul]

include hψφ in
/-- The identification of the underlying graded modules carries the left action of `A` on
`unflip X`, as an identity of linear maps. -/
theorem unflipRestrictedRegular_leftAction_comp (a : A.A) :
    (unflipRestrictedRegularHom ψ φ).toFun ∘ₗ leftActionTotal A (degreeZero R R)
        (unflip (restrictedRegularOpp ψ)).rightModule
        (unflip (restrictedRegularOpp ψ)).leftAction.1 a =
      leftActionTotal A (degreeZero R R)
        (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).rightModule
        (Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ)).leftAction.1 a ∘ₗ
        (unflipRestrictedRegularHom ψ φ).toFun := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => rw [map_zero, map_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  | add a b hA hB => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hA, hB]
  | @homogeneous m a =>
    refine LinearMap.ext fun y => ?_
    induction y using DirectSum.Decomposition.inductionOn
        (unflip (restrictedRegularOpp ψ)).rightModule.grading with
    | zero => rw [map_zero, map_zero]
    | add x y hX hY => rw [map_add, map_add, hX, hY]
    | @homogeneous n y =>
      exact (unflipRestrictedRegular_leftAction_of_mem ψ φ hψφ a.property y.property).trans
        (leftActionTotal_restrictRight_regular φ a.property
          (((opposite R A₀).mem_grading_iff n _).1 y.property)).symm

/-- **`unflip X` is the regular bimodule of `φ` with its right action restricted to `R`**, by the
identification of the underlying graded module of the graded opposite of `A₀` with that of
`A₀`. -/
def unflipRestrictedRegularIso :
    unflip (restrictedRegularOpp ψ) ≅ Bimodule.restrictRight (baseHom A₀) (Bimodule.regular φ) :=
  isoOfRightIso A (degreeZero R R) (unflipRestrictedRegularRightIso ψ φ)
    (fun a y => LinearMap.congr_fun (unflipRestrictedRegular_leftAction_comp ψ φ hψφ a) y)

/-- The underlying map of `DifferentialGraded.Bimodule.unflipRestrictedRegularIso`. -/
theorem unflipRestrictedRegularIso_hom_toFun (y : (restrictedRegularOpp ψ).M) :
    (unflipRestrictedRegularIso ψ φ hψφ).hom.rightHom.toFun y = (opposite R A₀).equiv y :=
  rfl

end Unflip

/-! ### The tensor product with the flip, and the plain transpose -/

section Transpose

variable {C : DifferentialGradedAlgebra.{u, u} R}

/-- Pure tensors under the identification of `unflip X` with the restricted regular bimodule,
after `tensorUnflipIso`. -/
private theorem tensorHomOfBimoduleHom_unflipIso_pure (ψ φ : A.Hom C)
    (hψφ : ∀ a, ψ.toAlgebraHom a = φ.toAlgebraHom a) (N : DifferentialGradedModule.{u, u, u} A)
    {p q : ℤ} {x : (restrictedRegularOpp ψ).M} (hx : x ∈ (restrictedRegularOpp ψ).grading q)
    {y : N.M} (hy : y ∈ N.grading p) :
    (tensorHomOfBimoduleHom (unflipRestrictedRegularIso ψ φ hψφ).hom N).toFun
        ((tensorUnflipIso N (restrictedRegularOpp ψ)).hom.toFun
          (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap x y)) =
      (((q * p).negOnePow : ℤ) : R) •
        ((tensorDGFunctor (Bimodule.restrictRight (baseHom C) (Bimodule.regular φ))).pure
          N).toLinearMap y ((opposite R C).equiv x) := by
  rw [tensorUnflipIso_hom_pure N (restrictedRegularOpp ψ) hx hy, LinearMap.map_smul]
  exact congrArg _ (tensorHomOfBimoduleHom_pure (unflipRestrictedRegularIso ψ φ hψφ).hom N y x)

/-- **The relative tensor product of a restricted regular module with the flip of `N`**:
`X ⊗_{A^{opp}} N̂ ≅ (N ⊗_A C)|_R`, where `X` is the graded opposite of `C` restricted along the
graded opposite of `ψ` and `C` is regarded as an `(A, C)`-bimodule through `φ`, which acts as
`ψ` does. -/
def flipRestrictedRegularIso (ψ φ : A.Hom C) (hψφ : ∀ a, ψ.toAlgebraHom a = φ.toAlgebraHom a)
    (N : DifferentialGradedModule.{u, u, u} A) :
    tensorObj (flip N) (restrictedRegularOpp ψ) ≅
      restrictScalars (baseHom C) (tensorObj (Bimodule.regular φ) N) :=
  tensorUnflipIso N (restrictedRegularOpp ψ) ≪≫
    (tensorModuleNatIso (unflipRestrictedRegularIso ψ φ hψφ)).app N ≪≫
      (tensorCompFunctorRestrictRightIso (baseHom C) (Bimodule.regular φ)).app N

/-- `DifferentialGraded.Bimodule.flipRestrictedRegularIso` on pure tensors of homogeneous
elements: `x ⊗ y ↦ (-1)^{(deg x)(deg y)} y ⊗ x`, the second factor read in `C`. -/
theorem flipRestrictedRegularIso_hom_pure (ψ φ : A.Hom C)
    (hψφ : ∀ a, ψ.toAlgebraHom a = φ.toAlgebraHom a) (N : DifferentialGradedModule.{u, u, u} A)
    {p q : ℤ} {x : (restrictedRegularOpp ψ).M} (hx : x ∈ (restrictedRegularOpp ψ).grading q)
    {y : N.M} (hy : y ∈ N.grading p) :
    (flipRestrictedRegularIso ψ φ hψφ N).hom.toFun
        (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap x y) =
      (((q * p).negOnePow : ℤ) : R) •
        ((tensorDGFunctor (Bimodule.regular φ)).pure N).toLinearMap y
          ((opposite R C).equiv x) := by
  show ((tensorCompFunctorRestrictRightIso (baseHom C) (Bimodule.regular φ)).hom.app N).toFun
    ((tensorHomOfBimoduleHom (unflipRestrictedRegularIso ψ φ hψφ).hom N).toFun
      ((tensorUnflipIso N (restrictedRegularOpp ψ)).hom.toFun
        (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap x y))) = _
  rw [tensorHomOfBimoduleHom_unflipIso_pure ψ φ hψφ N hx hy]
  refine (LinearMap.map_smul _ _ _).trans (congrArg _ ?_)
  exact tensorCompFunctorRestrictRightIso_hom_pure (baseHom C) (Bimodule.regular φ) N y
    ((opposite R C).equiv x)

/-- **The relative tensor product of the graded opposite of `C` with the flip of `N₀`**, over
the graded opposite of `C` acting through a homomorphism `ι` acting as the identity:
`X₀ ⊗_{C^{opp}} N̂₀ ≅ N₀|_R`. -/
def flipRestrictedRegularSelfIso (ι : C.Hom C) (hι : ∀ c, ι.toAlgebraHom c = c)
    (N₀ : DifferentialGradedModule.{u, u, u} C) :
    tensorObj (flip N₀) (restrictedRegularOpp ι) ≅ restrictScalars (baseHom C) N₀ :=
  tensorUnflipIso N₀ (restrictedRegularOpp ι) ≪≫
    (tensorModuleNatIso (unflipRestrictedRegularIso ι (idHom C)
      (fun c => (hι c).trans rfl))).app N₀ ≪≫
      tensorRegularRightIso (baseHom C) N₀

/-- `DifferentialGraded.Bimodule.flipRestrictedRegularSelfIso` on pure tensors of homogeneous
elements: `x ⊗ y ↦ (-1)^{(deg x)(deg y)} y x`, the element `x` read in `C`. -/
theorem flipRestrictedRegularSelfIso_hom_pure (ι : C.Hom C) (hι : ∀ c, ι.toAlgebraHom c = c)
    (N₀ : DifferentialGradedModule.{u, u, u} C) {p q : ℤ} {x : (restrictedRegularOpp ι).M}
    (hx : x ∈ (restrictedRegularOpp ι).grading q) {y : N₀.M} (hy : y ∈ N₀.grading p) :
    (flipRestrictedRegularSelfIso ι hι N₀).hom.toFun
        (((tensorDGFunctor (flip N₀)).pure (restrictedRegularOpp ι)).toLinearMap x y) =
      (((q * p).negOnePow : ℤ) : R) • (MulOpposite.op ((opposite R C).equiv x) • y) := by
  show (tensorRegularRightIso (baseHom C) N₀).hom.toFun
    ((tensorHomOfBimoduleHom (unflipRestrictedRegularIso ι (idHom C)
      (fun c => (hι c).trans rfl)).hom N₀).toFun
      ((tensorUnflipIso N₀ (restrictedRegularOpp ι)).hom.toFun
        (((tensorDGFunctor (flip N₀)).pure (restrictedRegularOpp ι)).toLinearMap x y))) = _
  rw [tensorHomOfBimoduleHom_unflipIso_pure ι (idHom C) _ N₀ hx hy]
  refine (LinearMap.map_smul _ _ _).trans (congrArg _ ?_)
  exact tensorRegularRightIso_hom_pure (baseHom C) N₀ y ((opposite R C).equiv x)

variable (φ ψ : A.Hom C) (ι : C.Hom C) (hψφ : ∀ a, ψ.toAlgebraHom a = φ.toAlgebraHom a)
  (hι : ∀ c, ι.toAlgebraHom c = c) {N : DifferentialGradedModule.{u, u, u} A}
  {N₀ : DifferentialGradedModule.{u, u, u} C} (g : N ⟶ restrictScalars φ N₀)
  (v : restrictedRegularOpp ψ ⟶ restrictScalars (oppHom φ) (restrictedRegularOpp ι))
  (hv : ∀ x, v.toFun x = x)
  (k : flip N ⟶ Bimodule.restrictLeft (oppHom φ) (flip N₀))
  (hk : ∀ y, k.rightHom.toFun y = g.toFun y)

include hv hk in
/-- **The square.** The homomorphism `X ⊗_{A^{opp}} N̂ ⟶ X₀ ⊗_{C^{opp}} N̂₀` induced by `g` is,
under the identifications with `(N ⊗_A C)|_R` and `N₀|_R`, the plain transpose of `g`. -/
theorem flipTensor_comp_selfIso :
    ((tensorCompFunctor (flip N)).map v ≫
        (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
          (restrictedRegularOpp ι)) ≫ (flipRestrictedRegularSelfIso ι hι N₀).hom =
      (flipRestrictedRegularIso ψ φ hψφ N).hom ≫
        restrictScalarsHom (baseHom C) (plainTranspose φ g) := by
  refine tensorObj_hom_ext' (flip N) (restrictedRegularOpp ψ) _ _ fun x y => ?_
  induction x using DirectSum.Decomposition.inductionOn (restrictedRegularOpp ψ).grading with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | @homogeneous q x =>
    induction y using DirectSum.Decomposition.inductionOn N.grading with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | @homogeneous p y =>
      have hgy : g.toFun (y : N.M) ∈ N₀.grading p := g.map_grading p _ y.property
      have h1 : ((tensorCompFunctor (flip N)).map v).toFun
          (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap
            (x : (restrictedRegularOpp ψ).M) (y : N.M)) =
          ((tensorDGFunctor (flip N)).pure
            ((restrictScalarsFunctor (oppHom φ)).obj (restrictedRegularOpp ι))).toLinearMap
            (x : (restrictedRegularOpp ψ).M) (y : N.M) :=
        (tensorCompFunctor_map_pure' (flip N) v _ _).trans
          (congrArg (fun z => ((tensorDGFunctor (flip N)).pure
            ((restrictScalarsFunctor (oppHom φ)).obj (restrictedRegularOpp ι))).toLinearMap z
              (y : N.M)) (hv _))
      have h2 := tensorCompNatTransOfSemilinear_app_pure (oppHom φ) (flip N) (flip N₀) k
        (restrictedRegularOpp ι) (x : (restrictedRegularOpp ψ).M) (y : N.M)
      have h3 := flipRestrictedRegularSelfIso_hom_pure ι hι N₀
        (x := (x : (restrictedRegularOpp ψ).M))
        x.property hgy
      have hL : (((tensorCompFunctor (flip N)).map v ≫
          (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
            (restrictedRegularOpp ι)) ≫ (flipRestrictedRegularSelfIso ι hι N₀).hom).toFun
          (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap
            (x : (restrictedRegularOpp ψ).M) (y : N.M)) =
          (((q * p).negOnePow : ℤ) : R) •
            @HSMul.hSMul C.Aᵐᵒᵖ N₀.M N₀.M _
              (MulOpposite.op ((opposite R C).equiv (x : (restrictedRegularOpp ψ).M)))
              (g.toFun (y : N.M)) := by
        refine Eq.trans ?_ h3
        show (flipRestrictedRegularSelfIso ι hι N₀).hom.toFun
          (((tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
            (restrictedRegularOpp ι)).toFun (((tensorCompFunctor (flip N)).map v).toFun
              (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap
                (x : (restrictedRegularOpp ψ).M) (y : N.M)))) = _
        refine congrArg (flipRestrictedRegularSelfIso ι hι N₀).hom.toFun ?_
        refine (congrArg _ h1).trans (h2.trans ?_)
        exact congrArg (((tensorDGFunctor (flip N₀)).pure (restrictedRegularOpp ι)).toLinearMap
          (x : (restrictedRegularOpp ψ).M)) (hk _)
      have h4 := flipRestrictedRegularIso_hom_pure ψ φ hψφ N x.property y.property
      have h5 := plainTranspose_pure φ g p y ((opposite R C).equiv (x : (restrictedRegularOpp ψ).M))
      have hR : ((flipRestrictedRegularIso ψ φ hψφ N).hom ≫
          restrictScalarsHom (baseHom C) (plainTranspose φ g)).toFun
          (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap
            (x : (restrictedRegularOpp ψ).M) (y : N.M)) =
          (((q * p).negOnePow : ℤ) : R) •
            @HSMul.hSMul C.Aᵐᵒᵖ N₀.M N₀.M _
              (MulOpposite.op ((opposite R C).equiv (x : (restrictedRegularOpp ψ).M)))
              (g.toFun (y : N.M)) := by
        show (plainTranspose φ g).toFun ((flipRestrictedRegularIso ψ φ hψφ N).hom.toFun
          (((tensorDGFunctor (flip N)).pure (restrictedRegularOpp ψ)).toLinearMap
            (x : (restrictedRegularOpp ψ).M) (y : N.M))) = _
        refine (congrArg (plainTranspose φ g).toFun h4).trans ?_
        refine (LinearMap.map_smul (plainTranspose φ g).toFun _ _).trans ?_
        exact congrArg (fun z => (((q * p).negOnePow : ℤ) : R) • z) h5
      exact hL.trans hR.symm

include hψφ hι hv hk in
/-- **If the plain transpose `N ⊗_A C ⟶ N₀` of `g` is a quasi-isomorphism, so is the
homomorphism `X ⊗_{A^{opp}} N̂ ⟶ X₀ ⊗_{C^{opp}} N̂₀` that `g` induces.** -/
theorem quasiIso_flipTensor_of_quasiIso_plainTranspose
    (hg : QuasiIso ((forgetToCochainComplex C).map (plainTranspose φ g))) :
    QuasiIso ((forgetToCochainComplex (degreeZero R R)).map
      ((tensorCompFunctor (flip N)).map v ≫
        (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
          (restrictedRegularOpp ι))) := by
  have hg' : QuasiIso ((forgetToCochainComplex (degreeZero R R)).map
      (restrictScalarsHom (baseHom C) (plainTranspose φ g))) := hg
  have harr : Arrow.mk ((tensorCompFunctor (flip N)).map v ≫
        (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
          (restrictedRegularOpp ι)) ≅
      Arrow.mk (restrictScalarsHom (baseHom C) (plainTranspose φ g)) :=
    Arrow.isoMk (flipRestrictedRegularIso ψ φ hψφ N) (flipRestrictedRegularSelfIso ι hι N₀)
      (flipTensor_comp_selfIso φ ψ ι hψφ hι g v hv k hk).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    ((forgetToCochainComplex (degreeZero R R)).mapArrow.mapIso harr)).2 hg'

end Transpose

end DifferentialGraded.Bimodule

end
