module

public import StacksFrontier.Algebra.DGA.BimoduleTensorExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorBimoduleVariable

/-! # Tensoring with a module commutes with the shift of the bimodule variable

Let `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R` and let `W`
be a right differential graded `B`-module. The ordinary tensor product `W ⊗_B -` of Tag 09LM,
read through Tag 0FQJ as a functor on right differential graded `Bᵒᵖ ⊗_R C`-modules, commutes
with the translation: `W ⊗_B (Y[k]) ≅ (W ⊗_B Y)[k]`, naturally in `W`.

Unlike the comparison of Tag 0FQN, which shifts the *module* variable and is sign-free, shifting
the *bimodule* variable needs the Koszul twist by the degree in `W`: the comparison sends a pure
tensor `x ⊗ y` to `(-1)^{k·|x|} · (x ⊗ y)`. The source differential sends `x ⊗ y` to
`dx ⊗ y + (-1)^{|x|}(-1)^k · x ⊗ dy`, because the differential of a shift carries the factor
`(-1)^k`, while the target differential is `(-1)^k` times `dx ⊗ y + (-1)^{|x|} · x ⊗ dy`; the
factor `(-1)^{k·|x|}` is exactly what reconciles the two. It also reconciles the two balance
conditions, since the left `B`-action on the shifted bimodule carries the Koszul sign of the
shifted degree, which differs from the unshifted one by `(-1)^{|b|·k}`.

## Main definitions

* `DifferentialGraded.Bimodule.gradingSignLinearMap`: the sign `(-1)^{k·n}` in degree `n`, as an
  endomorphism of the underlying module.
* `DifferentialGraded.Bimodule.tensorShiftTwistBalanced`: the twisted balanced bilinear map, for
  an abstract comparison `e` of the underlying right modules of two bimodules satisfying the
  twisted left-action condition.
* `DifferentialGraded.Bimodule.tensorShiftTwistHom` and
  `DifferentialGraded.Bimodule.tensorShiftTwistIso`: the comparison
  `W ⊗_B NS ⟶ (W ⊗_B N)[k]` that the twisted balanced bilinear map lifts to, and the fact that
  it is an isomorphism.
* `DifferentialGraded.Bimodule.tensorBimoduleShiftIso`: the comparison
  `W ⊗_B (Y[k]) ≅ (W ⊗_B Y)[k]` in the form the dévissage of Tag 0BZ5 consumes it.

## Main results

* `DifferentialGraded.Bimodule.tensorShiftTwistHom_pure`: the comparison on a pure tensor.
* `DifferentialGraded.Bimodule.tensorShiftTwistIso_naturality` and
  `DifferentialGraded.Bimodule.tensorBimoduleShiftIso_naturality`: naturality in the module
  variable `W`.
* `DifferentialGraded.Bimodule.ofTensorModuleShiftRightIso_leftActionTotal`: the twisted
  left-action condition at the bimodule attached to a right module over `Bᵒᵖ ⊗_R C`, which is
  what makes the abstract construction apply there.

## Implementation notes

*The construction is generic, and instantiated once.* All of the work is done for a pair of
bimodules `N`, `NS` together with an isomorphism `e : NS.rightModule ≅ N.rightModule[k]` of the
underlying right `C`-modules satisfying the twisted left-action condition; the shift of a module
over `Bᵒᵖ ⊗_R C` is then one instance, with `e` the identity on underlying modules and the
twisted condition the ratio of two applications of
`DifferentialGraded.Bimodule.ofTensorModule_leftActionTotal_apply`.

*Everything is read off the universal property.* The value `W ⊗_B N` is specified by
`DifferentialGraded.Bimodule.TensorDGFunctorData`, so the only handles on it are the universal
balanced bilinear map `DifferentialGraded.Bimodule.tensorPure`, the extensionality principle
`DifferentialGraded.Bimodule.tensorObj_hom_ext`, and the pure-tensor formulas. In particular
both composites of the comparison with its inverse, and the naturality square, are checked on
pure tensors after reducing the module argument to a homogeneous element.

*The balance condition is phrased through the totalized action.* The field
`DifferentialGraded.Bimodule.BalancedBilinearMap.balance` is stated with the cochain component
`Cochain.v` of the left action; `DifferentialGraded.Bimodule.leftAction_val` converts it into
`DifferentialGradedModule.leftActionTotal` form, which is the form in which the twisted
left-action condition is available.

*Universes are collapsed to one, inherited and not chosen here.*
`DifferentialGraded.Bimodule.TensorDGFunctorData` is stated for
`DifferentialGradedAlgebra.{u, u} R` and `DifferentialGradedModule.{u, u, u}`, so this file is
too.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the relative tensor
  product.
* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL), shifts of differential
  graded modules.
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules
  over the graded tensor product.
* [Stacks Project, Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN), the sign-free comparison
  for a shift of the module variable.
* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), where the comparison is
  used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (B C : DifferentialGradedAlgebra.{u, u} R)

/-! ### The degree-dependent sign -/

/-- **The sign `(-1)^{k·n}` in degree `n`**, as an endomorphism of the module underlying a right
differential graded `B`-module, assembled from the grading. -/
def gradingSignLinearMap (W : DifferentialGradedModule.{u, u, u} B) (k : ℤ) : W.M →ₗ[R] W.M :=
  (DirectSum.toModule R ℤ W.M (fun n =>
    ((k * n).negOnePow : ℤ) • (Submodule.subtype (W.grading n)))).comp
      (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- The sign of `DifferentialGraded.Bimodule.gradingSignLinearMap` on a homogeneous element. -/
theorem gradingSignLinearMap_apply (W : DifferentialGradedModule.{u, u, u} B) (k p : ℤ)
    (x : W.grading p) :
    gradingSignLinearMap B W k (x : W.M) = (k * p).negOnePow • (x : W.M) := by
  simp [gradingSignLinearMap, DirectSum.decomposeLinearEquiv_apply_coe, Units.smul_def]

/-- **The two Koszul signs of a shifted degree differ by the sign of the shift.** -/
theorem negOnePow_shift_cancel (m n k : ℤ) :
    (m * k).negOnePow * (m * (n + k)).negOnePow = (m * n).negOnePow := by
  have h : m * k + m * (n + k) = m * n + (m * k + m * k) := by ring
  rw [← Int.negOnePow_add, h, Int.negOnePow_add, Int.negOnePow_add, Int.units_mul_self, mul_one]

/-- **The ordinary tensor functor `- ⊗_B N` on a homomorphism of the module variable**, with its
type read at `DifferentialGraded.Bimodule.tensorObj` rather than at the value of
`DifferentialGraded.Bimodule.tensorCompFunctor`. The two are the same by unfolding, but only this
spelling keeps the source and target syntactically equal to the targets of the universal pure
tensors, which is what lets a rewrite underneath the map elaborate. -/
def tensorModuleHom (N : Bimodule B C) {V V' : DifferentialGradedModule.{u, u, u} B} (ρ : V ⟶ V') :
    tensorObj N V ⟶ tensorObj N V' :=
  (tensorCompFunctor N).map ρ

/-- The ordinary tensor functor on a homomorphism of the module variable, on a pure tensor. -/
theorem tensorModuleHom_pure (N : Bimodule B C)
    {V V' : DifferentialGradedModule.{u, u, u} B} (ρ : V ⟶ V') (x : V.M)
    (y : N.rightModule.M) :
    (tensorModuleHom B C N ρ).toFun ((tensorPure N V).toLinearMap x y) =
      (tensorPure N V').toLinearMap (ρ.toFun x) y :=
  tensorCompFunctor_map_pure N ρ x y

/-! ### The twisted comparison, for an abstract shift of the bimodule -/

section Generic

variable (W : DifferentialGradedModule.{u, u, u} B) (N NS : Bimodule B C) (k : ℤ)

/-- **The balance condition of the universal pure tensors, through the totalized left action.**
This is the field `DifferentialGraded.Bimodule.BalancedBilinearMap.balance` of
`DifferentialGraded.Bimodule.tensorPure`, with the left action written as
`DifferentialGradedModule.leftActionTotal` and with no homogeneity required of the second
variable. -/
theorem tensorPure_balance_leftActionTotal (p m : ℤ) (x : W.grading p) (b : B.grading m)
    (y : N.rightModule.M) :
    (tensorPure N W).toLinearMap (MulOpposite.op (b : B.A) • (x : W.M)) y =
      (tensorPure N W).toLinearMap (x : W.M)
        (leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A) y) := by
  induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | @homogeneous q y =>
    rw [(tensorPure N W).balance p q m x y b, leftAction_val B C N m q b y]

/-- The twisted bilinear map `(x, y) ↦ (-1)^{k·|x|} · (x ⊗ e y)` underlying the comparison. -/
def tensorShiftTwistBilinear
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k) :
    W.M →ₗ[R] NS.rightModule.M →ₗ[R] (tensorObj N W).M :=
  ((tensorPure N W).toLinearMap.comp (gradingSignLinearMap B W k)).compl₂ e.hom.toFun

/-- The twisted bilinear map on a homogeneous element of the module variable. -/
theorem tensorShiftTwistBilinear_apply (p : ℤ)
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (x : W.grading p) (y : NS.rightModule.M) :
    tensorShiftTwistBilinear B C W N NS k e (x : W.M) y =
      (k * p).negOnePow • (tensorPure N W).toLinearMap (x : W.M) (e.hom.toFun y) := by
  simp only [tensorShiftTwistBilinear, LinearMap.compl₂_apply, LinearMap.comp_apply,
    gradingSignLinearMap_apply, map_zsmul_unit, LinearMap.smul_apply]

/-- **The twisted balanced bilinear map.** Given an isomorphism `e` of the underlying right
`C`-modules of two bimodules identifying `NS` with the shift `N[k]`, and satisfying the twisted
left-action condition, the twisted bilinear map is a balanced bilinear map from `W` and `NS` to
the shift `(W ⊗_B N)[k]`. -/
def tensorShiftTwistBalanced
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (he : ∀ (m n : ℤ) (b : B.grading m) (y : NS.rightModule.grading n),
      e.hom.toFun (leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
          (y : NS.rightModule.M)) =
        (m * k).negOnePow • leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A)
          (e.hom.toFun (y : NS.rightModule.M))) :
    BalancedBilinearMap W NS (DifferentialGradedModule.shift (tensorObj N W) k) where
  toLinearMap := tensorShiftTwistBilinear B C W N NS k e
  map_grading p q x y := by
    rw [tensorShiftTwistBilinear_apply]
    change _ ∈ (tensorObj N W).grading (p + q + k)
    rw [Units.smul_def]
    apply Submodule.smul_mem (((tensorObj N W).grading (p + q + k)).restrictScalars ℤ)
    change (tensorPure N W).toLinearMap (x : W.M) (e.hom.toFun (y : NS.rightModule.M)) ∈
      (tensorObj N W).grading (p + q + k)
    simpa only [add_assoc] using (tensorPure N W).map_grading p (q + k) x
      ⟨e.hom.toFun (y : NS.rightModule.M), e.hom.map_grading q (y : NS.rightModule.M) y.property⟩
  map_d p x y := by
    have hd := LinearMap.congr_fun e.hom.map_d y
    change e.hom.toFun (NS.rightModule.d y) =
      k.negOnePow • N.rightModule.d (e.hom.toFun y) at hd
    have hdx := tensorShiftTwistBilinear_apply B C W N NS k (p + 1) e
      ⟨W.d (x : W.M), W.d_mem p (x : W.M) x.property⟩ y
    rw [tensorShiftTwistBilinear_apply, tensorShiftTwistBilinear_apply, hdx]
    change k.negOnePow • (tensorObj N W).d
      ((k * p).negOnePow • (tensorPure N W).toLinearMap (x : W.M) (e.hom.toFun y)) = _
    rw [map_zsmul_unit, (tensorPure N W).map_d p x (e.hom.toFun y), hd]
    simp only [smul_add, mul_add, mul_one, Int.negOnePow_add,
      Units.smul_def, map_zsmul, mul_smul]
    simp only [smul_smul, mul_comm, mul_left_comm]
  balance p q m x y b := by
    have hx := tensorShiftTwistBilinear_apply B C W N NS k (p + m) e
      ⟨MulOpposite.op (b : B.A) • (x : W.M),
        W.smul_mem p m (x : W.M) (b : B.A) x.property b.property⟩ y
    rw [hx, tensorShiftTwistBilinear_apply, leftAction_val B C NS m q b y, he,
      tensorPure_balance_leftActionTotal B C W N p m x b (e.hom.toFun (y : NS.rightModule.M))]
    simp only [map_zsmul_unit, mul_add, Int.negOnePow_add, mul_smul, mul_comm k m]
  map_right x y b := by
    change (tensorPure N W).toLinearMap (gradingSignLinearMap B W k x)
      (e.hom.toFun (MulOpposite.op b • y)) = _
    rw [e.hom.map_smul, (tensorPure N W).map_right]
    rfl

/-- **The twisted comparison `W ⊗_B NS ⟶ (W ⊗_B N)[k]`**: the lift of the twisted balanced
bilinear map along the universal property of the relative tensor product. -/
def tensorShiftTwistHom
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (he : ∀ (m n : ℤ) (b : B.grading m) (y : NS.rightModule.grading n),
      e.hom.toFun (leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
          (y : NS.rightModule.M)) =
        (m * k).negOnePow • leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A)
          (e.hom.toFun (y : NS.rightModule.M))) :
    tensorObj NS W ⟶ DifferentialGradedModule.shift (tensorObj N W) k :=
  ((tensorDGFunctor NS).universal W _ (tensorShiftTwistBalanced B C W N NS k e he)).choose

/-- The twisted comparison on a pure tensor. -/
theorem tensorShiftTwistHom_pure
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (he : ∀ (m n : ℤ) (b : B.grading m) (y : NS.rightModule.grading n),
      e.hom.toFun (leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
          (y : NS.rightModule.M)) =
        (m * k).negOnePow • leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A)
          (e.hom.toFun (y : NS.rightModule.M)))
    (p : ℤ) (x : W.grading p) (y : NS.rightModule.M) :
    (tensorShiftTwistHom B C W N NS k e he).toFun
        ((tensorPure NS W).toLinearMap (x : W.M) y) =
      (k * p).negOnePow • (tensorPure N W).toLinearMap (x : W.M) (e.hom.toFun y) :=
  (((tensorDGFunctor NS).universal W _
    (tensorShiftTwistBalanced B C W N NS k e he)).choose_spec.1 (x : W.M) y).trans
      (tensorShiftTwistBilinear_apply B C W N NS k p e x y)

end Generic

/-! ### Cancelling a shift -/

section Cancel

variable {A : DifferentialGradedAlgebra.{u, u} R}

/-- **Shifting by `k` and then by `-k` changes nothing.** Both sides have the same underlying
module, the same grading and the same differential. -/
def shiftNegCancelIso (M : DifferentialGradedModule.{u, u, u} A) (k : ℤ) :
    DifferentialGradedModule.shift (DifferentialGradedModule.shift M k) (-k) ≅ M :=
  DifferentialGradedModule.Hom.isoOfBijective
    { toFun := LinearMap.id
      map_smul := fun _ _ => rfl
      map_grading := fun n x hx => by
        simpa only [DifferentialGradedModule.shift_grading, neg_add_cancel_right,
          LinearMap.id_apply] using hx
      map_d := by
        ext x
        change (-k).negOnePow • (k.negOnePow • M.d x) = M.d x
        rw [smul_smul, ← Int.negOnePow_add, neg_add_cancel, Int.negOnePow_zero, one_smul] }
    Function.bijective_id

/-- The inverse of `DifferentialGraded.Bimodule.shiftNegCancelIso` is the identity on underlying
elements. -/
theorem shiftNegCancelIso_inv_apply (M : DifferentialGradedModule.{u, u, u} A) (k : ℤ)
    (x : M.M) : (shiftNegCancelIso M k).inv.toFun x = x :=
  congrArg (fun f : M ⟶ M => f.toFun x) (shiftNegCancelIso M k).inv_hom_id

/-- **An identification of a module with a shift, read backwards.** -/
def shiftIsoInverse {M N : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (e : M ≅ DifferentialGradedModule.shift N k) :
    N ≅ DifferentialGradedModule.shift M (-k) :=
  (shiftNegCancelIso N k).symm ≪≫ (DifferentialGradedModule.shiftFunctor A (-k)).mapIso e.symm

/-- The underlying map of `DifferentialGraded.Bimodule.shiftIsoInverse` is the inverse of the
given one. -/
theorem shiftIsoInverse_hom {M N : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (e : M ≅ DifferentialGradedModule.shift N k) :
    (shiftIsoInverse k e).hom.toFun = e.inv.toFun := by
  ext x
  change e.inv.toFun ((shiftNegCancelIso N k).inv.toFun x) = e.inv.toFun x
  rw [shiftNegCancelIso_inv_apply]

end Cancel

/-! ### The twisted comparison is an isomorphism -/

section Iso

variable (W : DifferentialGradedModule.{u, u, u} B) (N NS : Bimodule B C) (k : ℤ)

/-- **The twisted left-action condition for the backwards identification.** The sign of the shift
by `-k` is the inverse of the sign of the shift by `k`. -/
theorem shiftIsoInverse_leftActionTotal
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (he : ∀ (m n : ℤ) (b : B.grading m) (y : NS.rightModule.grading n),
      e.hom.toFun (leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
          (y : NS.rightModule.M)) =
        (m * k).negOnePow • leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A)
          (e.hom.toFun (y : NS.rightModule.M)))
    (m n : ℤ) (b : B.grading m) (y : N.rightModule.grading n) :
    (shiftIsoInverse k e).hom.toFun
        (leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A) (y : N.rightModule.M)) =
      (m * (-k)).negOnePow • leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
        ((shiftIsoInverse k e).hom.toFun (y : N.rightModule.M)) := by
  rw [shiftIsoInverse_hom]
  have hid (x : N.rightModule.M) : e.hom.toFun (e.inv.toFun x) = x :=
    (DifferentialGradedModule.isoToLinearEquiv e).right_inv x
  let z : NS.rightModule.grading (n - k) :=
    ⟨e.inv.toFun (y : N.rightModule.M),
      e.inv.map_grading (n - k) (y : N.rightModule.M)
        (by simpa only [DifferentialGradedModule.shift_grading, sub_add_cancel]
          using y.property)⟩
  have hz : e.hom.toFun (z : NS.rightModule.M) = (y : N.rightModule.M) := hid _
  have hh := he m (n - k) b z
  apply (DifferentialGradedModule.isoToLinearEquiv e).injective
  change e.hom.toFun (e.inv.toFun _) = e.hom.toFun _
  rw [hid, map_zsmul_unit, hh, hz, smul_smul, ← Int.negOnePow_add]
  simp

/-- **The twisted comparison `W ⊗_B NS ≅ (W ⊗_B N)[k]`.** The inverse is the twisted comparison
for the backwards identification and the shift by `-k`; the two signs multiply to
`(-1)^{(k + (-k))·|x|} = 1`. -/
def tensorShiftTwistIso
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (he : ∀ (m n : ℤ) (b : B.grading m) (y : NS.rightModule.grading n),
      e.hom.toFun (leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
          (y : NS.rightModule.M)) =
        (m * k).negOnePow • leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A)
          (e.hom.toFun (y : NS.rightModule.M))) :
    tensorObj NS W ≅ DifferentialGradedModule.shift (tensorObj N W) k := by
  let f := tensorShiftTwistHom B C W N NS k e he
  let g := tensorShiftTwistHom B C W NS N (-k) (shiftIsoInverse k e)
    (shiftIsoInverse_leftActionTotal B C N NS k e he)
  let h : DifferentialGradedModule.shift (tensorObj N W) k ⟶ tensorObj NS W :=
    { toFun := g.toFun
      map_smul := g.map_smul
      map_grading := by
        intro n x hx
        simpa using g.map_grading (n + k) x hx
      map_d := by
        ext x
        have hh := LinearMap.congr_fun g.map_d x
        change g.toFun ((tensorObj N W).d x) =
          (-k).negOnePow • (tensorObj NS W).d (g.toFun x) at hh
        change g.toFun (k.negOnePow • _) = _
        rw [map_zsmul_unit, hh, smul_smul, ← Int.negOnePow_add]
        simp }
  refine ⟨f, h, ?_, ?_⟩
  · refine tensorObj_hom_ext NS W _ _ fun x y => ?_
    change g.toFun (f.toFun ((tensorPure NS W).toLinearMap x y)) =
      (tensorPure NS W).toLinearMap x y
    induction x using DirectSum.Decomposition.inductionOn W.grading with
    | zero => simp
    | add x z hx hz => simp [hx, hz]
    | @homogeneous p x =>
      rw [tensorShiftTwistHom_pure B C W N NS k e he, map_zsmul_unit,
        tensorShiftTwistHom_pure B C W NS N (-k), shiftIsoInverse_hom, smul_smul,
        ← Int.negOnePow_add]
      have hh : e.inv.toFun (e.hom.toFun y) = y :=
        congrArg (fun q : NS.rightModule ⟶ NS.rightModule => q.toFun y) e.hom_inv_id
      simp [neg_mul, hh]
  · apply DifferentialGradedModule.Hom.ext
    have key : g ≫ (DifferentialGradedModule.shiftFunctor C (-k)).map f =
        (shiftNegCancelIso (tensorObj N W) k).inv := by
      refine tensorObj_hom_ext N W _ _ fun x y => ?_
      refine Eq.trans ?_ (shiftNegCancelIso_inv_apply (tensorObj N W) k _).symm
      change f.toFun (g.toFun ((tensorPure N W).toLinearMap x y)) =
        (tensorPure N W).toLinearMap x y
      induction x using DirectSum.Decomposition.inductionOn W.grading with
      | zero => simp
      | add x z hx hz => simp [hx, hz]
      | @homogeneous p x =>
        rw [tensorShiftTwistHom_pure B C W NS N (-k), map_zsmul_unit,
          tensorShiftTwistHom_pure B C W N NS k, shiftIsoInverse_hom, smul_smul,
          ← Int.negOnePow_add]
        have hh2 : e.hom.toFun (e.inv.toFun y) = y :=
          congrArg (fun q : DifferentialGradedModule.shift N.rightModule k ⟶
            DifferentialGradedModule.shift N.rightModule k => q.toFun y) e.inv_hom_id
        simp [neg_mul, hh2]
    ext x
    have hx := congrArg (fun q : tensorObj N W ⟶
      DifferentialGradedModule.shift
        (DifferentialGradedModule.shift (tensorObj N W) k) (-k) => q.toFun x) key
    exact hx.trans (shiftNegCancelIso_inv_apply (tensorObj N W) k x)

/-- **Naturality of the twisted comparison in the module variable.** Both sides are
homomorphisms out of `W ⊗_B NS`, and they agree on pure tensors. -/
theorem tensorShiftTwistIso_naturality
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W') (N NS : Bimodule B C) (k : ℤ)
    (e : NS.rightModule ≅ DifferentialGradedModule.shift N.rightModule k)
    (he : ∀ (m n : ℤ) (b : B.grading m) (y : NS.rightModule.grading n),
      e.hom.toFun (leftActionTotal B C NS.rightModule NS.leftAction.1 (b : B.A)
          (y : NS.rightModule.M)) =
        (m * k).negOnePow • leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A)
          (e.hom.toFun (y : NS.rightModule.M))) :
    tensorModuleHom B C NS ρ ≫ (tensorShiftTwistIso B C W' N NS k e he).hom =
      (tensorShiftTwistIso B C W N NS k e he).hom ≫
        (DifferentialGradedModule.shiftFunctor C k).map (tensorModuleHom B C N ρ) := by
  refine tensorObj_hom_ext NS W _ _ fun x y => ?_
  change (tensorShiftTwistHom B C W' N NS k e he).toFun
      ((tensorModuleHom B C NS ρ).toFun ((tensorPure NS W).toLinearMap x y)) =
    (tensorModuleHom B C N ρ).toFun ((tensorShiftTwistHom B C W N NS k e he).toFun
      ((tensorPure NS W).toLinearMap x y))
  induction x using DirectSum.Decomposition.inductionOn W.grading with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | @homogeneous p x =>
    rw [tensorModuleHom_pure B C NS ρ, tensorShiftTwistHom_pure B C W' N NS k e he p
      ⟨ρ.toFun (x : W.M), ρ.map_grading p (x : W.M) x.property⟩,
      tensorShiftTwistHom_pure B C W N NS k e he, map_zsmul_unit,
      tensorModuleHom_pure B C N ρ]

end Iso

/-! ### The shift of a module over the graded tensor product -/

/-- **The underlying right `C`-module of the bimodule attached to a shift is the shift of the
underlying right `C`-module.** Both are a restriction of scalars along the inclusion of `C` into
`Bᵒᵖ ⊗_R C`, and the comparison is the identity on underlying modules. -/
def ofTensorModuleShiftRightIso (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C))
    (k : ℤ) :
    (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule ≅
      DifferentialGradedModule.shift (ofTensorModule B C Y).rightModule k :=
  DifferentialGradedModule.restrictScalarsShiftIso
    (DifferentialGradedAlgebra.tensorIncludeRightHom (oppAlgebra B) C) Y k

/-- **The twisted left-action condition at a shift of a module over `Bᵒᵖ ⊗_R C`.** The left action
of a homogeneous `b : B^m` on the bimodule attached to a module over `Bᵒᵖ ⊗_R C` carries the
Koszul sign of the degree of the element it acts on, so the two sides differ by the ratio
`(-1)^{m·k}` of the shifted and unshifted signs. -/
theorem ofTensorModuleShiftRightIso_leftActionTotal
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) (k m n : ℤ) (b : B.grading m)
    (y : (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule.grading n) :
    (ofTensorModuleShiftRightIso B C Y k).hom.toFun
        (leftActionTotal B C (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule
          (ofTensorModule B C (DifferentialGradedModule.shift Y k)).leftAction.1 (b : B.A)
          (y : (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule.M)) =
      (m * k).negOnePow • leftActionTotal B C (ofTensorModule B C Y).rightModule
        (ofTensorModule B C Y).leftAction.1 (b : B.A)
        ((ofTensorModuleShiftRightIso B C Y k).hom.toFun
          (y : (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule.M)) := by
  have hy : ((y : (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule.M) : Y.M)
      ∈ (ofTensorModule B C Y).rightModule.grading (n + k) := y.property
  have h1 := ofTensorModule_leftActionTotal_apply B C (DifferentialGradedModule.shift Y k) b y
  have h2 := ofTensorModule_leftActionTotal_apply B C Y b
    (⟨(y : (ofTensorModule B C (DifferentialGradedModule.shift Y k)).rightModule.M), hy⟩ :
      (ofTensorModule B C Y).rightModule.grading (n + k))
  erw [h1, h2, smul_smul, negOnePow_shift_cancel]

/-! ### The comparison in the form the dévissage consumes -/

/-- **Tensoring with a module commutes with the shift of the bimodule variable.** The comparison
`W ⊗_B (Y[k]) ≅ (W ⊗_B Y)[k]`, for `Y` a right differential graded `Bᵒᵖ ⊗_R C`-module: it is the
twisted comparison at the identification of the underlying right `C`-modules of
`DifferentialGraded.Bimodule.ofTensorModuleShiftRightIso`. -/
def tensorBimoduleShiftIso (W : DifferentialGradedModule.{u, u, u} B)
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) (k : ℤ) :
    (tensorBimoduleFunctor B C W).obj (DifferentialGradedModule.shift Y k) ≅
      DifferentialGradedModule.shift ((tensorBimoduleFunctor B C W).obj Y) k :=
  tensorShiftTwistIso B C W (ofTensorModule B C Y)
    (ofTensorModule B C (DifferentialGradedModule.shift Y k)) k
    (ofTensorModuleShiftRightIso B C Y k) (ofTensorModuleShiftRightIso_leftActionTotal B C Y k)

/-- **Naturality of the comparison in the module variable.** -/
theorem tensorBimoduleShiftIso_naturality
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) (k : ℤ) :
    (tensorBimoduleNatTrans B C ρ).app (DifferentialGradedModule.shift Y k) ≫
        (tensorBimoduleShiftIso B C W' Y k).hom =
      (tensorBimoduleShiftIso B C W Y k).hom ≫
        (DifferentialGradedModule.shiftFunctor C k).map ((tensorBimoduleNatTrans B C ρ).app Y) :=
  tensorShiftTwistIso_naturality B C ρ (ofTensorModule B C Y)
    (ofTensorModule B C (DifferentialGradedModule.shift Y k)) k
    (ofTensorModuleShiftRightIso B C Y k)
    (ofTensorModuleShiftRightIso_leftActionTotal B C Y k)

end DifferentialGraded.Bimodule

end
