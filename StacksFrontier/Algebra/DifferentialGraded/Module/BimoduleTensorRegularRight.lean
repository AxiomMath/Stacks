module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeTensorKFlat
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorAlgebraComparison
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLeftPropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents

/-! # Restriction of scalars is tensoring with the regular bimodule

Let `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R` and let
`ψ : C → B` be a homomorphism of differential graded algebras. The algebra `B`, with `B` acting
on the left by multiplication and `C` acting on the right through `ψ`, is a differential graded
`(B, C)`-bimodule; tensoring a right differential graded `B`-module `M` with it over `B` gives
back `M`, read over `C`. In other words, restriction of scalars along `ψ` *is* tensoring with
the regular bimodule, which is the tensor half of Stacks 0BYX, and the same holds after passing
to the derived categories.

## Main definitions

* `DifferentialGraded.Bimodule.regularRight`: the regular `(B, C)`-bimodule of `ψ`.
* `DifferentialGraded.Bimodule.tensorRegularRightIso`: the right unitor
  `M ⊗_B B ≅ M|_C` of right differential graded `C`-modules.
* `DifferentialGraded.Bimodule.tensorRegularRightNatIso`: the right unitor as an isomorphism of
  functors `- ⊗_B B ≅ -|_C`, natural in `M`.
* `DifferentialGraded.Bimodule.derivedTensorRegularRightIso`: its derived form,
  `- ⊗_B^𝐋 B ≅ -|_C` as functors `D(B, d) ⥤ D(C, d)`.

## Main results

* `DifferentialGraded.Bimodule.tensorRegularRightIso_hom_pure`: the right unitor sends the pure
  tensor `x ⊗ b` to `x b`, which determines it.
* `DifferentialGraded.Bimodule.tensorPreservesQuasiIso_regularRight`: tensoring with the regular
  bimodule carries quasi-isomorphisms to quasi-isomorphisms, since it is restriction of scalars.

## Implementation notes

*The unitor comes from the universal property.* The value `M ⊗_B B` is characterized, not named,
by `DifferentialGraded.Bimodule.TensorDGFunctorData`, so the comparison `M ⊗_B B → M|_C` is the
lift of the balanced bilinear map `(x, b) ↦ x b`: the right action of `B` on `M` adds degrees,
satisfies the graded Leibniz rule, is balanced because the right action is associative, and is
right `C`-linear because the right `C`-action on the bimodule is multiplication by `ψ(c)`. Its
inverse is `x ↦ x ⊗ 1`, a homomorphism of differential graded modules because `d 1 = 0`. That
the two composites are the identity is checked on pure tensors through
`DifferentialGraded.Bimodule.tensorObj_hom_ext'`, where `x b ⊗ 1 = x ⊗ b` is an instance of the
balance relation; naturality is checked the same way.

*Why the derived statement is formal.* Restriction of scalars does not change the underlying
complex of `R`-modules, so tensoring with the regular bimodule carries quasi-isomorphisms to
quasi-isomorphisms. By `DifferentialGraded.Bimodule.derivedTensorIsoOfPreservesQuasiIso` — the
construction of the derived tensor product in the proof of Tag 09LS — the comparison from the
derived to the plain tensor product is then invertible, and the plain tensor product descends to
derived restriction of scalars through the localizations.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars
  as tensoring with the regular bimodule.
* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the tensor functor and
  its universal property, and [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), the derived
  tensor functor.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {B C : DifferentialGradedAlgebra.{u, u} R}

/-- **The regular `(B, C)`-bimodule of a homomorphism `ψ : C → B`.** The algebra `B`, with `B`
acting on the left by multiplication and `C` acting on the right through `ψ`. Tensoring with it
is restriction of scalars along `ψ`. -/
@[reducible] def regularRight (ψ : C.Hom B) : Bimodule B C where
  rightModule := restrictScalars ψ (regularModule B)
  leftAction := restrictScalarsBimoduleStructure ψ (regularBimoduleStructure (idHom B))

/-- The regular bimodule of `ψ` is the regular `(B, B)`-bimodule restricted on the right. -/
theorem regularRight_eq (ψ : C.Hom B) :
    regularRight ψ = Bimodule.restrictRight ψ (Bimodule.regular (idHom B)) := rfl

/-! ### The right unitor of the relative tensor product -/

-- NO `rightActionBilinear` AND NO `rightActionBilinear_apply` HERE. They stated exactly
-- `DifferentialGradedModule.rightActionBilinear` and `..._apply`
-- (`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeTensorKFlat.lean`:403 and :414),
-- which are public; `LinearMap.mk₂ R (fun x b => MulOpposite.op b • x) ...` elaborates to the
-- same nested structure as the survivor's explicit `toFun`, and both carry the same `rfl`
-- `_apply` lemma. That module is now imported.

/-- The right action is associative: acting by `y` after `a` is acting by `a y`. -/
private theorem op_smul_op_smul (M : DifferentialGradedModule.{u, u, u} B) (x : M.M)
    (a y : B.A) :
    MulOpposite.op y • (MulOpposite.op a • x) = MulOpposite.op (a * y) • x := by
  rw [MulOpposite.op_mul, mul_smul]

/-- The graded Leibniz rule for the right action, with an arbitrary scalar in the second
variable: both sides are additive in it, so the homogeneous case suffices. -/
private theorem rightAction_leibniz (M : DifferentialGradedModule.{u, u, u} B) (p : ℤ)
    (x : M.grading p) (y : B.A) :
    M.d (MulOpposite.op y • (x : M.M)) =
      MulOpposite.op y • M.d (x : M.M) +
        (p.negOnePow : ℤ) • (MulOpposite.op (B.d y) • (x : M.M)) := by
  induction y using DirectSum.Decomposition.inductionOn B.grading with
  | zero => simp
  | add y z hy hz =>
    simp only [MulOpposite.op_add, add_smul, map_add, hy, hz, smul_add]
    abel
  | @homogeneous q y => exact M.leibniz p q (x : M.M) y.1 x.property y.property

/-- The right action of `B` on `M`, as a balanced bilinear map out of `M` and the regular
bimodule into the restriction `M|_C`. This is the universal source of the unitor `M ⊗_B B ≅ M`.
-/
private def rightUnitorBilinear (ψ : C.Hom B) (M : DifferentialGradedModule.{u, u, u} B) :
    BalancedBilinearMap M (regularRight ψ) ((restrictScalarsFunctor ψ).obj M) where
  toLinearMap := DifferentialGradedModule.rightActionBilinear M
  map_grading p q x y := M.smul_mem p q x.1 y.1 x.property y.property
  map_d p x y := rightAction_leibniz M p x y
  balance p q n x y a :=
    (op_smul_op_smul M x.1 a.1 y.1).trans
      (congrArg (fun w : B.A => MulOpposite.op w • x.1)
        (regularBimoduleStructure_action (idHom B) n q a y).symm)
  map_right x y b := by
    exact (op_smul_op_smul M x y (ψ.toAlgebraHom b)).symm

/-- The right unitor `M ⊗_B B → M|_C`, from the universal property of the relative tensor
product: it sends the pure tensor `x ⊗ b` to `x b`. -/
private def rightUnitorHom (ψ : C.Hom B) (M : DifferentialGradedModule.{u, u, u} B) :
    DifferentialGradedModule.Hom ((tensorDGFunctor (regularRight ψ)).functor.obj M)
      ((restrictScalarsFunctor ψ).obj M) :=
  ((tensorDGFunctor (regularRight ψ)).universal M ((restrictScalarsFunctor ψ).obj M)
    (rightUnitorBilinear ψ M)).choose

private theorem rightUnitorHom_pure (ψ : C.Hom B) (M : DifferentialGradedModule.{u, u, u} B)
    (x : M.M) (y : B.A) :
    (rightUnitorHom ψ M).toFun
        (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x y) =
      MulOpposite.op y • x :=
  ((tensorDGFunctor (regularRight ψ)).universal M ((restrictScalarsFunctor ψ).obj M)
    (rightUnitorBilinear ψ M)).choose_spec.1 x y

/-- Pure tensors absorb the right action: `x b ⊗ 1` is `x ⊗ b`. This is the balance relation of
the universal pure tensor, read with `1` in the second variable. -/
private theorem pure_op_smul_one (ψ : C.Hom B) (M : DifferentialGradedModule.{u, u, u} B)
    (x : M.M) (b : B.A) :
    ((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap (MulOpposite.op b • x)
        (1 : B.A) =
      ((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x b := by
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero =>
    rw [MulOpposite.op_zero, zero_smul, map_zero, LinearMap.zero_apply]
    exact (map_zero (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x)).symm
  | add b b' hb hb' =>
    rw [show MulOpposite.op (b + b') • x =
        MulOpposite.op b • x + MulOpposite.op b' • x from by
      rw [MulOpposite.op_add, add_smul], map_add, LinearMap.add_apply, hb, hb']
    exact (map_add (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x) b b').symm
  | @homogeneous n b =>
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero =>
      rw [smul_zero, map_zero, LinearMap.zero_apply]
      exact (LinearMap.zero_apply _).symm
    | add x x' hx hx' =>
      simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
    | @homogeneous p x =>
      refine (((tensorDGFunctor (regularRight ψ)).pure M).balance p 0 n x
        ⟨(1 : B.A), SetLike.one_mem_graded B.grading⟩ b).trans ?_
      refine congrArg (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap (x : M.M)) ?_
      refine (regularBimoduleStructure_action (idHom B) n 0 b
        ⟨(1 : B.A), SetLike.one_mem_graded B.grading⟩).trans ?_
      simp

/-- The inclusion `x ↦ x ⊗ 1` of `M|_C` into `M ⊗_B B`. -/
private def rightUnitorInv (ψ : C.Hom B) (M : DifferentialGradedModule.{u, u, u} B) :
    DifferentialGradedModule.Hom ((restrictScalarsFunctor ψ).obj M)
      ((tensorDGFunctor (regularRight ψ)).functor.obj M) where
  toFun := LinearMap.flip ((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap (1 : B.A)
  map_smul x c := by
    refine (pure_op_smul_one ψ M x (ψ.toAlgebraHom c)).trans ?_
    refine Eq.trans ?_
      (((tensorDGFunctor (regularRight ψ)).pure M).map_right x (1 : B.A) c)
    refine congrArg (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x) ?_
    exact (one_mul (ψ.toAlgebraHom c)).symm
  map_grading n x hx := by
    have h := ((tensorDGFunctor (regularRight ψ)).pure M).map_grading n 0 ⟨x, hx⟩
      ⟨(1 : B.A), SetLike.one_mem_graded B.grading⟩
    rwa [add_zero] at h
  map_d := by
    have key : ∀ x : M.M,
        ((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap (M.d x) (1 : B.A) =
          ((tensorDGFunctor (regularRight ψ)).functor.obj M).d
            (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x (1 : B.A)) := by
      intro x
      induction x using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
      | @homogeneous p x =>
        have h := ((tensorDGFunctor (regularRight ψ)).pure M).map_d p x (1 : B.A)
        rw [show (regularRight ψ).rightModule.d (1 : B.A) = 0 from d_one B, map_zero,
          smul_zero, add_zero] at h
        exact h.symm
    exact LinearMap.ext key

/-- **The right unitor of the relative tensor product.** Tensoring a right differential graded
`B`-module `M` with the regular `(B, C)`-bimodule of `ψ : C → B` over `B` gives back `M`, read
over `C`: there is an isomorphism `M ⊗_B B ≅ M|_C` of right differential graded `C`-modules
carrying the pure tensor `x ⊗ b` to `x b`.

The isomorphism is specified by its action on pure tensors, which by the universal property of
Tag 09LM determines it uniquely; its inverse is `x ↦ x ⊗ 1`. -/
@[no_expose]
def tensorRegularRightIso (ψ : C.Hom B) (M : DifferentialGradedModule.{u, u, u} B) :
    tensorObj' (regularRight ψ) M ≅ (restrictScalarsFunctor ψ).obj M where
  hom := rightUnitorHom ψ M
  inv := rightUnitorInv ψ M
  hom_inv_id := by
    refine tensorObj_hom_ext' (regularRight ψ) M _ (DifferentialGradedModule.Hom.id _)
      fun x y => ?_
    have key : ∀ z : B.A, (rightUnitorInv ψ M).toFun ((rightUnitorHom ψ M).toFun
        (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x z)) =
          ((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x z := fun z => by
      rw [show (rightUnitorHom ψ M).toFun
          (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x z) =
            MulOpposite.op z • x from rightUnitorHom_pure ψ M x z]
      exact pure_op_smul_one ψ M x z
    exact key y
  inv_hom_id := by
    refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
    have key : ∀ z : M.M, (rightUnitorHom ψ M).toFun
        (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap z (1 : B.A)) = z := fun z =>
      (rightUnitorHom_pure ψ M z (1 : B.A)).trans (by rw [MulOpposite.op_one, one_smul])
    exact key x

/-- The right unitor sends the pure tensor `x ⊗ b` to `x b`, which determines it. -/
theorem tensorRegularRightIso_hom_pure (ψ : C.Hom B)
    (M : DifferentialGradedModule.{u, u, u} B) (x : M.M) (y : B.A) :
    (tensorRegularRightIso ψ M).hom.toFun
        (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x y) =
      MulOpposite.op y • x :=
  rightUnitorHom_pure ψ M x y

/-- **Stacks 0BYX, the tensor half, on differential graded modules.** Restriction of scalars
along `ψ : C → B` is tensoring with the regular `(B, C)`-bimodule, naturally in the module.

Naturality is an equality of two homomorphisms out of a tensor product, so it is checked on pure
tensors, where both sides send `x ⊗ b` to `f(x) b`. -/
@[stacks 0BYX "restriction of scalars is tensoring with the regular bimodule, on differential \
graded modules"]
def tensorRegularRightNatIso (ψ : C.Hom B) :
    tensorCompFunctor (regularRight ψ) ≅ restrictScalarsFunctor ψ :=
  NatIso.ofComponents (fun M => tensorRegularRightIso ψ M) (by
    intro M N f
    refine tensorObj_hom_ext' (regularRight ψ) M _ _ fun x y => ?_
    have key : ∀ z : B.A, (tensorRegularRightIso ψ N).hom.toFun
        (((tensorCompFunctor (regularRight ψ)).map f).toFun
          (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x z)) =
        ((restrictScalarsFunctor ψ).map f).toFun
          ((tensorRegularRightIso ψ M).hom.toFun
            (((tensorDGFunctor (regularRight ψ)).pure M).toLinearMap x z)) := fun z => by
      rw [tensorCompFunctor_map_pure', tensorRegularRightIso_hom_pure,
        tensorRegularRightIso_hom_pure]
      exact (f.map_smul x z).symm
    exact key y)

/-! ### The derived form -/

/-- Tensoring with the regular bimodule carries quasi-isomorphisms to quasi-isomorphisms: it is
restriction of scalars, which does not change the underlying complex of `R`-modules. -/
theorem tensorPreservesQuasiIso_regularRight (ψ : C.Hom B) :
    TensorPreservesQuasiIso (regularRight ψ) := by
  intro M M' f hf
  set e := Functor.isoWhiskerRight (tensorRegularRightNatIso ψ) (forgetToCochainComplex C)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app M) (e.app M') (e.hom.naturality f).symm)).mpr hf

/-- Tensoring with the regular bimodule, read on the homotopy categories, is restriction of
scalars: both are quotient lifts, so the identification on differential graded modules descends.
-/
def tensorHomotopyRegularRightIso (ψ : C.Hom B) :
    tensorHomotopyFunctor (regularRight ψ) ≅ restrictScalarsHomotopyFunctor ψ :=
  CategoryTheory.Quotient.natIsoLift _
    ((tensorCompFunctor_quotient (regularRight ψ)).symm ≪≫
      Functor.isoWhiskerRight (tensorRegularRightNatIso ψ) (toHomotopyCategory C) ≪≫
      (restrictScalarsHomotopyFunctorIso ψ).symm)

/-- **Stacks 0BYX, the tensor half, on derived categories.** Derived restriction of scalars
along `ψ : C → B` is the derived tensor product with the regular `(B, C)`-bimodule.

Tensoring with the regular bimodule already inverts the quasi-isomorphisms, so by the
construction of the derived tensor product in the proof of Tag 09LS it computes the derived
tensor product; and it descends to derived restriction of scalars through the localizations. -/
@[stacks 0BYX "restriction of scalars is tensoring with the regular bimodule, on derived \
categories"]
def derivedTensorRegularRightIso (ψ : C.Hom B) :
    derivedTensorFunctor (regularRight ψ) ≅ derivedRestriction ψ :=
  Localization.liftNatIso (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    ((quasiIsomorphisms' B).Q ⋙ derivedTensorFunctor (regularRight ψ))
    ((quasiIsomorphisms' B).Q ⋙ derivedRestriction ψ)
    (derivedTensorFunctor (regularRight ψ)) (derivedRestriction ψ)
    (derivedTensorIsoOfPreservesQuasiIso (regularRight ψ)
        (tensorPreservesQuasiIso_regularRight ψ) ≪≫
      Functor.isoWhiskerRight (tensorHomotopyRegularRightIso ψ) (quasiIsomorphisms' C).Q ≪≫
      (derivedRestrictionFactorization ψ).symm)

end DifferentialGraded.Bimodule

end
