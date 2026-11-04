module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorLeft
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleRestrictLeft
public import StacksFrontier.RingTheory.Koszul.TensorCellFiltration

/-!
# One plain tensor product over two algebras

Let `R` be a commutative ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded
`R`-algebras. For a differential graded `(A, B)`-bimodule `N` the two plain relative tensor
products

* `(A ⊗_R C) ⊗_A N`, of the right differential graded `A`-module `A ⊗_R C` with `N`, and
* `C ⊗_R N`, of the algebra `C` read as a right differential graded module over `R` placed in
  degree zero with `N` read as a differential graded `(R, B)`-bimodule,

are the same right differential graded `B`-module. Both compute
`DifferentialGradedModule.absoluteTensorLeft`, the tensor product of the complex underlying `C`
with the complex underlying `N`: the first by `DifferentialGraded.absLeftBalanceIso`, the second
because over the base ring placed in degree zero both actions are the scalar action, so the
balancing relations are plain `R`-bilinearity and the relative tensor product is the absolute
one.

This is the identification of plain tensor products that Tag 0GZJ feeds to
`DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso`: with `A = K_n`, `C = K_t` and `N` a
differential graded `(K_n, B)`-bimodule it says that the plain tensor products with `N` of the two
modules `K_n ⊗_R K_t` over `K_n` and `K_t` over `R` — both orthogonal on the left to the acyclic
modules, by `Koszul.leftOrthogonal_acyclic_powAlgebra_tensorModule` and
`Koszul.leftOrthogonal_acyclic_powAlgebra_baseModule` — agree.

## Main definitions

* `DifferentialGraded.absBaseSource` and `DifferentialGraded.absBaseBimodule`: the algebra `C`
  and the bimodule `N`, read over `R` placed in degree zero.
* `DifferentialGraded.absBaseUnbalanceBalanced`: the pure tensor `(c, y) ↦ c ⊗ y` as a balanced
  bilinear map, and `DifferentialGraded.absBaseBalanceForward`,
  `DifferentialGraded.absBaseBalanceInverse`: the two homomorphisms of differential graded
  `B`-modules it produces.

## Main results

* `DifferentialGraded.absBaseSource_mul_eq_smul` and `DifferentialGraded.absBaseAct_eq_smul`: over
  `R` placed in degree zero both the right action on `C` and the left action on a bimodule are the
  scalar action.
* `DifferentialGraded.absBaseBalanceIso`: the relative tensor product of `C` with `N` over `R` in
  degree zero is the absolute tensor product `C ⊗_R N`.
* `DifferentialGraded.tensorObjIsoOfBaseChange`: **the comparison of the two plain tensor
  products**, `(A ⊗_R C) ⊗_A N ≅ C ⊗_R N`.
* `Koszul.tensorObjIso_tensorModule_baseModule`: the comparison at the Koszul algebra of a
  functional on `Rʳ`, in the spelling in which the two left-orthogonality statements are
  available.

## Implementation notes

*The general part.* Nothing in the general part below mentions the Koszul complex; the
statements are about arbitrary differential graded algebras, read over `R` placed in degree zero
through the structure map `DifferentialGradedAlgebra.baseHom`. The Koszul specialisation at the
end is the form in which Tag 0GZJ uses the comparison.

*Why the balancing over `R` in degree zero is empty.* The right action of `R` placed in degree
zero on `C` is multiplication by the image of `R` in `C`, which is central and therefore the
`R`-module structure. The left action is the scalar action on *every* differential graded
`(R, B)`-bimodule with `R` placed in degree zero, for a reason that does not mention `A` at all:
a scalar `r` is `r • 1` there, `DifferentialGraded.leftActionTotal` is linear in the scalar, and
the unit acts as the identity. The balancing relation is then `(r • c) ⊗ y = c ⊗ (r • y)`, which
already holds in the tensor product over `R`, so no degree hypothesis on the scalar is needed.

*A variable algebra for the right action.* Instance synthesis for a right action by
`(DifferentialGradedAlgebra.degreeZero R R).A` does not succeed at that concrete term — the field
projection carrying the module structure is not found.
`DifferentialGraded.restrictRegular_op_smul` is therefore stated with the source algebra still a
variable and used in a goal that already carries the instance.

*Two spellings of the Koszul algebra.* The carrier of the Koszul differential graded algebra is
the exterior algebra, but the two are not the same term and a graded tensor product mixing them
is not type correct at the transparency rewriting uses. The specialisation at the end is
therefore given as a term whose type is checked up to definitional equality at default
transparency rather than by rewriting, and everything above it is spelled at the carrier of the
differential graded algebra.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product with a bimodule and [Tag 065W](https://stacks.math.columbia.edu/tag/065W) the tensor
  product of differential graded algebras.
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is where the comparison
  is used.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance] DifferentialGradedModule.absLeftRightModule
  DifferentialGradedModule.absLeftRightScalarTower
  DifferentialGradedModule.absLeftDecomposition

variable {R : Type u} [CommRing R] (A B C : DifferentialGradedAlgebra.{u, u} R)

/-! ### The two actions of the base ring in degree zero -/

/-- `C`, read as a right differential graded module over `R` placed in degree zero. -/
abbrev absBaseSource : DifferentialGradedModule.{u, u, u} (degreeZero R R) :=
  restrictScalars (baseHom C) (regularModule C)

/-- `N`, read as a differential graded `(R, B)`-bimodule with `R` placed in degree zero. -/
abbrev absBaseBimodule (N : Bimodule A B) : Bimodule (degreeZero R R) B :=
  Bimodule.restrictLeft (baseHom A) N

/-- The right action on the regular module of `C`, restricted along a homomorphism `φ : A' → C`
of differential graded algebras, is right multiplication by the image of the scalar. The
algebra `A'` is kept a variable here: instance synthesis for a right action by
`(DifferentialGradedAlgebra.degreeZero R R).A` does not succeed at that concrete term, so the
statement is made where the algebra is still a variable and used below in a goal that already
carries the instance. -/
theorem restrictRegular_op_smul {A' : DifferentialGradedAlgebra.{u, u} R} (φ : A'.Hom C)
    (a : A'.A) (x : (restrictScalars φ (regularModule C)).M) :
    MulOpposite.op a • x = (show C.A from x) * φ.toAlgebraHom a := rfl

/-- The right action of `R` placed in degree zero on `C` is the scalar action. -/
theorem absBaseSource_mul_eq_smul (s : R) (c : C.A) :
    c * (baseHom C).toAlgebraHom s = s • c := by
  rw [baseHom_toAlgebraHom, Algebra.ofId_apply, Algebra.smul_def, Algebra.commutes]

/-- **The left action of `R` placed in degree zero is the scalar action.** On any differential
graded `(R, B)`-bimodule with `R` placed in degree zero, a scalar acts as itself: it is `r • 1`
there, the total action is linear in the scalar, and the unit acts as the identity. -/
theorem absBaseAct_eq_smul (N' : Bimodule (degreeZero R R) B) (s : R)
    (y : N'.rightModule.M) :
    absLeftAct (degreeZero R R) B N' s y = s • y := by
  calc absLeftAct (degreeZero R R) B N' s y
      = absLeftAct (degreeZero R R) B N' (s • (1 : (degreeZero R R).A)) y :=
        congrArg (fun t => absLeftAct (degreeZero R R) B N' t y) (mul_one s).symm
    _ = s • y := by rw [map_smul, LinearMap.smul_apply, leftActionTotal_one, LinearMap.id_apply]

/-- A base-ring scalar moves across a pure tensor. -/
theorem absBaseMk_smul_comm {X Y : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (s : R) (x : X) (y : Y) :
    (TensorProduct.mk R X Y (s • x)) y = (TensorProduct.mk R X Y x) (s • y) := by
  exact TensorProduct.smul_tmul s x y

/-! ### The relative tensor product over the base ring in degree zero -/

/-- The pure tensor `(c, y) ↦ c ⊗ y`, as a balanced bilinear map over `R` in degree zero. -/
def absBaseUnbalanceBalanced (N : Bimodule A B) :
    Bimodule.BalancedBilinearMap (absBaseSource C) (absBaseBimodule A B N)
      (absoluteTensorLeft C N.rightModule) where
  toLinearMap := TensorProduct.mk R C.A N.rightModule.M
  map_grading p q c y :=
    absLeftTmul_mem C N.rightModule p q _ _ c.property y.property
  map_d p c y := absLeftDifferential_tmul C N.rightModule p c y
  balance p q n c y s := by
    rw [restrictRegular_op_smul C (baseHom C), absBaseSource_mul_eq_smul,
      ← absLeftAct_coe (degreeZero R R) B (absBaseBimodule A B N) s y,
      absBaseAct_eq_smul B (absBaseBimodule A B N)]
    exact absBaseMk_smul_comm (s : R) _ _
  map_right c y b := (absLeft_smul_tmul C N.rightModule c y b).symm

/-- The relative tensor product of `C` with `N` over `R` placed in degree zero. -/
abbrev absBaseRelative (N : Bimodule A B) : DifferentialGradedModule.{u, u, u} B :=
  Bimodule.tensorObj (absBaseBimodule A B N) (absBaseSource C)

/-- The universal pure tensors into the relative tensor product over `R` in degree zero. -/
abbrev absBasePure (N : Bimodule A B) :
    Bimodule.BalancedBilinearMap (absBaseSource C) (absBaseBimodule A B N)
      (absBaseRelative A B C N) :=
  Bimodule.tensorPure (absBaseBimodule A B N) (absBaseSource C)

/-- The universal pure tensors, with the first argument read in `C` itself. -/
def absBasePureBilinear (N : Bimodule A B) :
    C.A →ₗ[R] N.rightModule.M →ₗ[R] (absBaseRelative A B C N).M :=
  (absBasePure A B C N).toLinearMap

/-- The identification, as a homomorphism out of the relative tensor product over `R` in degree
zero: the unique homomorphism of differential graded `B`-modules sending `c ⊗ y` to `c ⊗ y`. -/
def absBaseBalanceForward (N : Bimodule A B) :
    absBaseRelative A B C N ⟶ absoluteTensorLeft C N.rightModule :=
  ((Bimodule.tensorDGFunctor (absBaseBimodule A B N)).universal (absBaseSource C)
    (absoluteTensorLeft C N.rightModule) (absBaseUnbalanceBalanced A B C N)).choose

/-- `DifferentialGraded.absBaseBalanceForward` sends the pure tensor `c ⊗ y` of the relative
tensor product to `c ⊗ y`. -/
theorem absBaseBalanceForward_pure (N : Bimodule A B) (c : C.A) (y : N.rightModule.M) :
    (absBaseBalanceForward A B C N).toFun (absBasePureBilinear A B C N c y) =
      (c ⊗ₜ[R] y : C.A ⊗[R] N.rightModule.M) :=
  ((Bimodule.tensorDGFunctor (absBaseBimodule A B N)).universal (absBaseSource C)
    (absoluteTensorLeft C N.rightModule) (absBaseUnbalanceBalanced A B C N)).choose_spec.1 c y

/-- The inverse of the identification, as a homomorphism of differential graded `B`-modules. -/
def absBaseBalanceInverse (N : Bimodule A B) :
    absoluteTensorLeft C N.rightModule ⟶ absBaseRelative A B C N where
  toFun := TensorProduct.lift (absBasePureBilinear A B C N)
  map_smul z b := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul c y =>
      rw [absLeft_smul_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      exact (absBasePure A B C N).map_right c y b
  map_grading n z hz := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, c, y, hc, hy, rfl, rfl⟩ := hz
      rw [TensorProduct.lift.tmul]
      exact (absBasePure A B C N).map_grading p q ⟨c, hc⟩ ⟨y, hy⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih
  map_d := by
    apply LinearMap.ext; intro z
    change TensorProduct.lift (absBasePureBilinear A B C N)
        (absLeftDifferential C N.rightModule z) =
      (absBaseRelative A B C N).d
        (TensorProduct.lift (absBasePureBilinear A B C N) z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c y =>
      induction c using DirectSum.Decomposition.inductionOn C.grading with
      | zero => simp
      | add c c' hc hc' => simp only [TensorProduct.add_tmul, map_add, hc, hc']
      | @homogeneous p c =>
        rw [absLeftDifferential_tmul, map_add, map_zsmul, TensorProduct.lift.tmul,
          TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        exact ((absBasePure A B C N).map_d p c y).symm

/-- **The relative tensor product over `R` in degree zero is the absolute one.** -/
def absBaseBalanceIso (N : Bimodule A B) :
    absBaseRelative A B C N ≅ absoluteTensorLeft C N.rightModule where
  hom := absBaseBalanceForward A B C N
  inv := absBaseBalanceInverse A B C N
  hom_inv_id := by
    refine Bimodule.tensorObj_hom_ext (absBaseBimodule A B N) (absBaseSource C) _ _
      fun c y => ?_
    exact (congrArg (absBaseBalanceInverse A B C N).toFun
      (absBaseBalanceForward_pure A B C N c y)).trans
      (TensorProduct.lift.tmul (f' := absBasePureBilinear A B C N) c y)
  inv_hom_id := DifferentialGradedModule.Hom.ext (TensorProduct.ext' fun c y =>
    (congrArg (absBaseBalanceForward A B C N).toFun
      (TensorProduct.lift.tmul (f' := absBasePureBilinear A B C N) c y)).trans
      (absBaseBalanceForward_pure A B C N c y))

/-- **The two plain tensor products agree.** For a differential graded `(A, B)`-bimodule `N` the
relative tensor product of `A ⊗_R C` with `N` over `A` is the relative tensor product of `C` with
`N` over `R` placed in degree zero. -/
def tensorObjIsoOfBaseChange (N : Bimodule A B) :
    absLeftRelative A B C N ≅ absBaseRelative A B C N :=
  absLeftBalanceIso A B C N ≪≫ (absBaseBalanceIso A B C N).symm

end DifferentialGraded

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ} (A B : DifferentialGradedAlgebra.{u, u} R)
  (φ : Module.Dual R (Fin r → R))

/-- **The two plain tensor products of Tag 0GZJ agree.** For a differential graded
`(A, B)`-bimodule `N`, the relative tensor product over `A` of `A ⊗_R K` — the tensor product of
`A` with the Koszul algebra of a functional on `Rʳ`, read over `A` — with `N` is the relative
tensor product over `R` placed in degree zero of `K` with `N`. At `A = K_n` and `K = K_t` these
are the plain tensor products of the two modules whose left orthogonality to the acyclic modules
is `Koszul.leftOrthogonal_acyclic_powAlgebra_tensorModule` and
`Koszul.leftOrthogonal_acyclic_powAlgebra_baseModule`. -/
def tensorObjIso_tensorModule_baseModule (N : Bimodule A B) :
    Bimodule.tensorObj N (tensorModule A φ) ≅
      Bimodule.tensorObj (absBaseBimodule A B N) (baseModule φ) :=
  tensorObjIsoOfBaseChange A B (cohomologicalDifferentialGradedAlgebra R (Fin r → R) φ) N

end Koszul

end
