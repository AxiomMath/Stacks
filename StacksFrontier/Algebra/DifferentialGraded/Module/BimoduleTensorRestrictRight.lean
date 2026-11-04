module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChange
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorAssocIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorBimoduleVariable
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRegularRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBaseChangeSecondVariable

/-! # Restricting the right algebra of a bimodule restricts the tensor product

Let `(A, d)`, `(S, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `ψ : C → S` be a homomorphism of differential graded algebras and let `N` be a differential
graded `(A, S)`-bimodule. Restricting the right action along `ψ`
(`DifferentialGraded.Bimodule.restrictRight`) leaves the relative tensor product alone: for a
differential graded `A`-module `M`,

`M ⊗_A (N|_ψ) = (M ⊗_A N)|_ψ`,

because the relative tensor product only imposes the balancing relations for `A` and carries the
right action along. This file proves that, naturally in `M`, and applies it to the canonical map
`c_M` in the proof of Stacks 0BYZ.

The route is not the universal property of `M ⊗_A (N|_ψ)` directly — a map out of it would have
to be built from a balanced bilinear map into a differential graded `C`-module, and `(M ⊗_A N)|_ψ`
is reached in the other variance. Instead `N|_ψ` is identified with the composite bimodule
`N ⊗_S S` of Tag 0BZ3, where `S` carries the `(S, C)`-bimodule structure of Tag 0BYX whose tensor
product is restriction of scalars; associativity of the relative tensor product then does the
work.

## Main definitions

* `DifferentialGraded.Bimodule.compTensorRegularRightIso`: the composite of `N` with the regular
  `(S, C)`-bimodule of `ψ` is `N|_ψ`.
* `DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso`: **the transfer**,
  `- ⊗_A (N|_ψ) ≅ (- ⊗_A N)|_ψ` as functors `Mod^{dg}_{(A, d)} ⥤ Mod^{dg}_{(C, d)}`.

## Main results

* `DifferentialGraded.Bimodule.baseChangeBimodule_eq_restrictRight`: the bimodule
  `{}_A(A ⊗_R R')_{R'}` of Tag 0BZ4 is the base-change bimodule `{}_A(A ⊗_R R')_{A ⊗_R R'}` of
  Stacks 0BYZ with its right action restricted to `R'`.
* `DifferentialGraded.Bimodule.baseChangeTensorIso`: **the canonical map `c_M` of the proof of
  Stacks 0BYZ, over `R'`** — the differential graded `R'`-module underlying the base change
  `M ⊗_A A'` of a differential graded `A`-module `M` is `M ⊗_R R'`. Its `A'`-linear form is
  `DifferentialGraded.Bimodule.baseChangeTensorAlgebraIso` in
  `StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeAbsoluteTensor.lean`, which is
  downstream of this file.
* `DifferentialGraded.Bimodule.baseChangeTensorNatIso`: its natural half, that base change
  followed by restriction of the action to `R'` is tensoring with the bimodule
  `{}_A(A ⊗_R R')_{R'}` of Tag 0BZ4.

## Implementation notes

*What of Tag 0BYZ is here, and what is not.* Only the canonical map `c_M` of the source's
*proof*, over `R'`; none of the three parts of the statement is proved here. Part (1) is
`DifferentialGraded.Bimodule.derivedBaseChangeFunctor_isLeftDerivedFunctor` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChange.lean`, and `c_M` is exactly what
identifies the functor derived there with the source's `M ↦ M ⊗_R R'`. Part (2) is
`DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRestrictionSquare.lean` and part (3) is
`DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRepresents.lean`.

*Why the identification of the bimodules needs a computation.* The underlying right `C`-modules
of `N ⊗_S S` and of `N|_ψ` are identified by the right unitor
`DifferentialGraded.Bimodule.tensorRegularRightIso` of Tag 0BYX, so by
`DifferentialGraded.Bimodule.isoOfRightIso` only compatibility with the left `A`-action is left to
check. On a pure tensor `x ⊗ b` the left action of `a` is `(a x) ⊗ b`
(`DifferentialGraded.Bimodule.compTensor_leftActionTotal_tensorPure`) and the unitor sends it to
`(a x) b`, so what is needed is that the left `A`-action commutes with the right `S`-action. That
is `DifferentialGraded.leftActionTotal_commutes` once both elements are homogeneous. Neither of
the two reductions to the homogeneous case can be read off a `simp` set: both sides of the
identity are `R`-linear in the element of `A` and in the element of `S`, but the zero and the sum
have to be pushed through maps whose source is the relative tensor product, and there the two
spellings of the next note get in the way. The reduction in the element of `S` is therefore a
`have` inside the proof, stated over `N` alone where only one spelling occurs, and the reduction
in the element of `A` is done on composites of linear maps rather than on their values.

*Why the right module has to be named before the computation.* The two spellings
`(N.compTensor (regularRight ψ)).rightModule` and `(Bimodule.restrictRight ψ N).rightModule` of
the source and target of the unitor are equal only after unfolding definitions that are not
reducible, so a goal stated through one of them and rewritten through the other is type-correct
only at default transparency, where `simp` and `rw` will not look. The unitor is therefore named
once, as `DifferentialGraded.Bimodule.restrictRightUnitor`, at the spelling the bimodule
isomorphism needs, and every statement below is given at that spelling.

*Universes.* The differential graded algebras and their modules live in a single universe,
following the encoding of Tag 09JJ used throughout this chapter.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the relative tensor
  product and its universal property.
* [Stacks Project, Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3), the composite bimodule.
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars
  as tensoring with the regular bimodule.
* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ), whose proof begins with
  the canonical map `c_M : M ⊗_R R' → M ⊗_A A'`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A S C : DifferentialGradedAlgebra.{u, u} R}

/-! ### The composite with the regular bimodule -/

/-- The right unitor `N ⊗_S S ≅ N|_ψ` of Tag 0BYX, on underlying right differential graded
`C`-modules, named at the spelling in which the right module of the composite bimodule
`DifferentialGraded.Bimodule.compTensor` and the right module of the restriction
`DifferentialGraded.Bimodule.restrictRight` appear. -/
def restrictRightUnitor (ψ : C.Hom S) (N : Bimodule A S) :
    (compTensor N (regularRight ψ)).rightModule ≅ (Bimodule.restrictRight ψ N).rightModule :=
  tensorRegularRightIso ψ N.rightModule

/-- The right unitor sends the pure tensor `x ⊗ b` to `x b`, which determines it. -/
theorem restrictRightUnitor_hom_pure (ψ : C.Hom S) (N : Bimodule A S) (x : N.rightModule.M)
    (b : S.A) :
    (restrictRightUnitor ψ N).hom.toFun
        ((tensorPure (regularRight ψ) N.rightModule).toLinearMap x b) =
      (show (Bimodule.restrictRight ψ N).rightModule.M from MulOpposite.op b • x) :=
  tensorRegularRightIso_hom_pure ψ N.rightModule x b

/-- The right unitor commutes with the left action of a homogeneous element of `A` on a pure
tensor: the left action is on the first factor, and it commutes with the right `S`-action which
the unitor performs. -/
private theorem restrictRightUnitor_leftActionTotal_pure (ψ : C.Hom S) (N : Bimodule A S)
    {n : ℤ} (a : A.grading n) (x : N.rightModule.M) (b : S.A) :
    (restrictRightUnitor ψ N).hom.toFun
        (leftActionTotal A C (compTensor N (regularRight ψ)).rightModule
          (compTensor N (regularRight ψ)).leftAction.1 (a : A.A)
          ((tensorPure (regularRight ψ) N.rightModule).toLinearMap x b)) =
      leftActionTotal A C (Bimodule.restrictRight ψ N).rightModule
        (Bimodule.restrictRight ψ N).leftAction.1 (a : A.A)
        ((restrictRightUnitor ψ N).hom.toFun
          ((tensorPure (regularRight ψ) N.rightModule).toLinearMap x b)) := by
  have hcomm : ∀ (c : S.A) (y : N.rightModule.M),
      leftActionTotal A S N.rightModule N.leftAction.1 (a : A.A) (MulOpposite.op c • y) =
        MulOpposite.op c • leftActionTotal A S N.rightModule N.leftAction.1 (a : A.A) y := by
    intro c y
    induction c using DirectSum.Decomposition.inductionOn S.grading with
    | zero => simp
    | add c c' hc hc' => simp only [MulOpposite.op_add, add_smul, map_add, hc, hc']
    | @homogeneous q c =>
      exact leftActionTotal_commutes A S N.rightModule N.leftAction.1 N.leftAction.2 a c y
  rw [compTensor_leftActionTotal_tensorPure N (regularRight ψ) a x b,
    restrictRightUnitor_hom_pure, restrictRightUnitor_hom_pure]
  exact (hcomm b x).symm

/-- The right unitor commutes with the totalized left `A`-action. Both sides are `R`-linear in
the element of `A`, so the homogeneous case suffices, and there it is an equality of maps out of
a relative tensor product, checked on pure tensors through
`DifferentialGraded.Bimodule.tensorObj_linearMap_ext`. -/
theorem restrictRightUnitor_leftActionTotal (ψ : C.Hom S) (N : Bimodule A S) (a : A.A) :
    (restrictRightUnitor ψ N).hom.toFun ∘ₗ
        leftActionTotal A C (compTensor N (regularRight ψ)).rightModule
          (compTensor N (regularRight ψ)).leftAction.1 a =
      leftActionTotal A C (Bimodule.restrictRight ψ N).rightModule
          (Bimodule.restrictRight ψ N).leftAction.1 a ∘ₗ
        (restrictRightUnitor ψ N).hom.toFun := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, ha']
  | @homogeneous n a =>
    exact tensorObj_linearMap_ext (regularRight ψ) N.rightModule _ _
      (restrictRightUnitor_leftActionTotal_pure ψ N a)

/-- **The composite of `N` with the regular `(S, C)`-bimodule of `ψ` is `N` restricted on the
right along `ψ`**: `N ⊗_S S = N|_ψ` as differential graded `(A, C)`-bimodules. -/
def compTensorRegularRightIso (ψ : C.Hom S) (N : Bimodule A S) :
    compTensor N (regularRight ψ) ≅ Bimodule.restrictRight ψ N :=
  isoOfRightIso A C (restrictRightUnitor ψ N)
    (fun a y => LinearMap.congr_fun (restrictRightUnitor_leftActionTotal ψ N a) y)

/-! ### The transfer of the tensor functor -/

/-- **Restricting the right algebra of a bimodule restricts the tensor product**:
`- ⊗_A (N|_ψ) ≅ (- ⊗_A N)|_ψ` as functors `Mod^{dg}_{(A, d)} ⥤ Mod^{dg}_{(C, d)}`.

Tensoring with `N|_ψ = N ⊗_S S` is tensoring with `N` followed by tensoring with the regular
`(S, C)`-bimodule of `ψ`, by associativity of the relative tensor product
(`DifferentialGraded.Bimodule.tensorCompFunctorAssocIso`), and the latter is restriction of
scalars along `ψ` by Tag 0BYX
(`DifferentialGraded.Bimodule.tensorRegularRightNatIso`). -/
def tensorCompFunctorRestrictRightIso (ψ : C.Hom S) (N : Bimodule A S) :
    tensorCompFunctor (Bimodule.restrictRight ψ N) ≅
      tensorCompFunctor N ⋙ restrictScalarsFunctor ψ :=
  (tensorModuleNatIso (compTensorRegularRightIso ψ N)).symm ≪≫
    tensorCompFunctorAssocIso N (regularRight ψ) ≪≫
      Functor.isoWhiskerLeft (tensorCompFunctor N) (tensorRegularRightNatIso ψ)

/-! ### The canonical map of the proof of Stacks 0BYZ -/

variable (A) (R' : Type u) [CommRing R'] [Algebra R R']

/-- The bimodule `{}_A(A ⊗_R R')_{R'}` of Tag 0BZ4 is the base-change bimodule
`{}_A(A ⊗_R R')_{A ⊗_R R'}` of Stacks 0BYZ with its right action restricted to `R'` along
`r' ↦ 1 ⊗ r'`. Both are the regular bimodule of `a ↦ a ⊗ 1`, the first with its right action
restricted. -/
theorem baseChangeBimodule_eq_restrictRight :
    baseChangeBimodule A (degreeZero R R') =
      Bimodule.restrictRight (tensorIncludeRightHom A (degreeZero R R')) (baseChange A R') :=
  rfl

/-- **The canonical map `c_M` in the proof of Stacks 0BYZ, over `R'`.** Let `R → R'` be a ring
map, let `(A, d)` be a differential graded `R`-algebra and let `A' = A ⊗_R R'` be its base change.
For a differential graded `A`-module `M` the differential graded `R'`-module underlying the base
change `M ⊗_A A'` is `M ⊗_R R'`.

The source's `c_M : M ⊗_R R' → M ⊗_A A'` is a map of differential graded `A'`-modules; this is
that map after restricting the right action from `A'` to `R'`, which is where its content lies:
restricting the right action does not change the relative tensor product
(`DifferentialGraded.Bimodule.tensorCompFunctorRestrictRightIso`), and over `R'` the base-change
bimodule is the one for which `M ⊗_A (A ⊗_R R') = M ⊗_R R'` is already proved
(`DifferentialGraded.absBalanceIso`). The `A'`-linear statement, which needs `M ⊗_R R'` built as
a differential graded `A ⊗_R R'`-module and is proved by the universal property rather than by
this transfer, is `DifferentialGraded.Bimodule.baseChangeTensorAlgebraIso` in
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeAbsoluteTensor.lean`. -/
@[stacks 0BYZ "the canonical map c_M of the PROOF, over R' — NOT any of parts (1), (2), (3). It \
is what identifies the functor derived in part (1), derivedBaseChangeFunctor_isLeftDerivedFunctor \
of BaseChange.lean, with the source's M |-> M (x)_R R'. Part (2) is \
derivedBaseChangeRestrictionSquare, part (3) isIso_derivedBaseChangeCounit_app_of_kFlat. The \
A'-linear form of this map, which is what the source states, is baseChangeTensorAlgebraIso"]
def baseChangeTensorIso (M : DifferentialGradedModule.{u, u, u} A) :
    (restrictScalarsFunctor (tensorIncludeRightHom A (degreeZero R R'))).obj
        ((tensorCompFunctor (baseChange A R')).obj M) ≅
      M.absoluteTensor (degreeZero R R') :=
  ((tensorCompFunctorRestrictRightIso (tensorIncludeRightHom A (degreeZero R R'))
    (baseChange A R')).app M).symm ≪≫ absBalanceIso A (degreeZero R R') M

/-- **Base change of differential graded modules, followed by restriction of the action to `R'`,
is tensoring with the bimodule `{}_A(A ⊗_R R')_{R'}` of Tag 0BZ4, naturally in `M`.** This is the
natural half of `DifferentialGraded.Bimodule.baseChangeTensorIso`: the identification of the
value at `M` with `M ⊗_R R'` is then `DifferentialGraded.absBalanceIso`, which is recorded
objectwise. -/
def baseChangeTensorNatIso :
    tensorCompFunctor (baseChange A R') ⋙
        restrictScalarsFunctor (tensorIncludeRightHom A (degreeZero R R')) ≅
      tensorCompFunctor (baseChangeBimodule A (degreeZero R R')) :=
  (tensorCompFunctorRestrictRightIso (tensorIncludeRightHom A (degreeZero R R'))
    (baseChange A R')).symm

end DifferentialGraded.Bimodule

end
