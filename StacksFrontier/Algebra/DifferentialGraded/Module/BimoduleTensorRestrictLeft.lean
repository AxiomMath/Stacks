module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleRestrictLeft
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap

/-!
# Comparing plain tensor products over two algebras

Let `(A, d)`, `(A', d)` and `(B, d)` be differential graded algebras over a commutative ring `R`
and let `φ : A ⟶ A'` be a homomorphism of differential graded algebras. Let `P` be a differential
graded `(A, B)`-bimodule and `P'` a differential graded `(A', B)`-bimodule. There is no
homomorphism of bimodules between `P` and `P'`, because they live over different algebras; what
takes its place is a *semilinear* homomorphism, that is a homomorphism
`f : P ⟶ P'|_φ` of differential graded `(A, B)`-bimodules into the restriction
`DifferentialGraded.Bimodule.restrictLeft φ P'` of `P'`, equivalently an `R`-linear map `P → P'`
which preserves the grading and the differential, is right `B`-linear, and satisfies
`f (a · p) = φ(a) · f(p)`.

Such an `f` gives a comparison of the *plain* tensor functors over the two algebras,
`τ : (- |_A) ⊗_A P ⟶ - ⊗_{A'} P'`,
whose component at a differential graded `A'`-module `Y` sends the pure tensor `y ⊗ p` to the
pure tensor `y ⊗ f(p)`. This is exactly the datum
`DifferentialGraded.Bimodule.DerivedTensorTower.plainCmp` of a tower of derived tensor products
over a varying algebra, and the input of
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans`, which turns it into a comparison of the
*derived* tensor functors.

## Main definitions

* `DifferentialGraded.Bimodule.restrictLeftTensorNatTrans`: the comparison
  `Y|_A ⊗_A P'|_φ ⟶ Y ⊗_{A'} P'` attached to `φ` alone, the identity on pure tensors. Over `A`
  the tensor product imposes fewer relations than over `A'`, so this is the passage to the
  further quotient.
* `DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear`: the comparison
  `Y|_A ⊗_A P ⟶ Y ⊗_{A'} P'` attached to a semilinear homomorphism `f : P ⟶ P'|_φ`. It is
  tensoring with `f` over `A`, followed by the previous comparison.

## Main results

* `DifferentialGraded.Bimodule.restrictLeftTensorHom_pure` and
  `DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear_app_pure`: the two comparisons on
  pure tensors, which determine them.

## Implementation notes

*Why the restricted bimodule carries the whole construction.* The only place where the two
algebras genuinely interact is the balancing relation: over `A` the relation imposed on
`Y|_A ⊗ P'` is `y a ⊗ p = y ⊗ a p` for `a` homogeneous in `A`, and under the left action of
`A` on `P'|_φ` the right-hand side is `y ⊗ φ(a) p`, while the left-hand side is the relation for
`φ(a)` on `Y`. So the universal balanced bilinear map of `Y ⊗_{A'} P'` already satisfies the
`A`-balancing of `Y|_A ⊗_A P'|_φ`, with `DifferentialGradedAlgebra.Hom.gradingMap` supplying the
homogeneous element of `A'`; every other field of
`DifferentialGraded.Bimodule.BalancedBilinearMap` is the original one, because restriction of
scalars and restriction of the left action change neither the underlying `R`-module, nor the
grading, nor the differential, nor the right `B`-action. The general semilinear `f` is then
handled by `DifferentialGraded.Bimodule.tensorModuleNatTrans`, which is tensoring with a
homomorphism of bimodules over the single algebra `A`.

*Every map out of a tensor product is a lift.* As in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorBimoduleMap.lean`, the value
`M ⊗_A N` is characterized, not named, by
`DifferentialGraded.Bimodule.TensorDGFunctorData`; the comparison is accordingly the lift of a
balanced bilinear map, and its naturality is proved by
`DifferentialGraded.Bimodule.tensorObj_hom_ext'`, the uniqueness half of that property.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the plain tensor
  functor, [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) restriction of scalars and
  [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) differential graded bimodules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A A' B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The comparison attached to the homomorphism of algebras alone -/

/-- The universal pure tensor of `Y ⊗_{A'} P'`, read as a balanced bilinear map out of the
restriction `Y|_A` and the restricted bimodule `P'|_φ`. Only the balancing relation changes: the
degree-`n` part of `A` acts through `φ`, so the relation over `A` is the relation over `A'` at
`φ(a)`. -/
private def restrictLeftTensorBilinearMap (φ : A.Hom A') (P' : Bimodule A' B)
    (Y : DifferentialGradedModule.{u, u, u} A') :
    BalancedBilinearMap ((restrictScalarsFunctor φ).obj Y) (Bimodule.restrictLeft φ P')
      ((tensorDGFunctor P').functor.obj Y) where
  toLinearMap := ((tensorDGFunctor P').pure Y).toLinearMap
  map_grading p q x y := ((tensorDGFunctor P').pure Y).map_grading p q x y
  map_d p x y := ((tensorDGFunctor P').pure Y).map_d p x y
  balance p q n x y a := ((tensorDGFunctor P').pure Y).balance p q n x y (φ.gradingMap n a)
  map_right x y b := ((tensorDGFunctor P').pure Y).map_right x y b

/-- **The comparison `Y|_A ⊗_A P'|_φ ⟶ Y ⊗_{A'} P'`.** The homomorphism of differential graded
`B`-modules which is the identity on pure tensors; it exists because the tensor product over `A`
imposes fewer relations than the one over `A'`. -/
@[no_expose]
def restrictLeftTensorHom (φ : A.Hom A') (P' : Bimodule A' B)
    (Y : DifferentialGradedModule.{u, u, u} A') :
    DifferentialGradedModule.Hom
      ((tensorDGFunctor (Bimodule.restrictLeft φ P')).functor.obj
        ((restrictScalarsFunctor φ).obj Y))
      ((tensorDGFunctor P').functor.obj Y) :=
  ((tensorDGFunctor (Bimodule.restrictLeft φ P')).universal ((restrictScalarsFunctor φ).obj Y)
    ((tensorDGFunctor P').functor.obj Y) (restrictLeftTensorBilinearMap φ P' Y)).choose

/-- The comparison `Y|_A ⊗_A P'|_φ ⟶ Y ⊗_{A'} P'` is the identity on pure tensors, which
determines it. -/
theorem restrictLeftTensorHom_pure (φ : A.Hom A') (P' : Bimodule A' B)
    (Y : DifferentialGradedModule.{u, u, u} A')
    (x : ((restrictScalarsFunctor φ).obj Y).M)
    (y : (Bimodule.restrictLeft φ P').rightModule.M) :
    (restrictLeftTensorHom φ P' Y).toFun
        (((tensorDGFunctor (Bimodule.restrictLeft φ P')).pure
          ((restrictScalarsFunctor φ).obj Y)).toLinearMap x y) =
      ((tensorDGFunctor P').pure Y).toLinearMap x y :=
  ((tensorDGFunctor (Bimodule.restrictLeft φ P')).universal ((restrictScalarsFunctor φ).obj Y)
    ((tensorDGFunctor P').functor.obj Y)
    (restrictLeftTensorBilinearMap φ P' Y)).choose_spec.1 x y

/-- **The comparison of the plain tensor functors attached to a homomorphism of the left
algebras.** Tensoring the restriction `Y|_A` with the restricted bimodule `P'|_φ` over `A` maps to
tensoring `Y` with `P'` over `A'`, naturally in the differential graded `A'`-module `Y`. -/
def restrictLeftTensorNatTrans (φ : A.Hom A') (P' : Bimodule A' B) :
    restrictScalarsFunctor φ ⋙ tensorCompFunctor (Bimodule.restrictLeft φ P') ⟶
      tensorCompFunctor P' where
  app Y := restrictLeftTensorHom φ P' Y
  naturality Y Z g := by
    refine tensorObj_hom_ext' (Bimodule.restrictLeft φ P') ((restrictScalarsFunctor φ).obj Y)
      _ _ fun x y => ?_
    change (restrictLeftTensorHom φ P' Z).toFun
        (((tensorCompFunctor (Bimodule.restrictLeft φ P')).map
            ((restrictScalarsFunctor φ).map g)).toFun
          (((tensorDGFunctor (Bimodule.restrictLeft φ P')).pure
            ((restrictScalarsFunctor φ).obj Y)).toLinearMap x y)) =
      ((tensorCompFunctor P').map g).toFun
        ((restrictLeftTensorHom φ P' Y).toFun
          (((tensorDGFunctor (Bimodule.restrictLeft φ P')).pure
            ((restrictScalarsFunctor φ).obj Y)).toLinearMap x y))
    rw [tensorCompFunctor_map_pure', restrictLeftTensorHom_pure, restrictLeftTensorHom_pure]
    exact (tensorCompFunctor_map_pure' P' g x y).symm

/-- The component of `DifferentialGraded.Bimodule.restrictLeftTensorNatTrans` at `Y` is the
comparison `Y|_A ⊗_A P'|_φ ⟶ Y ⊗_{A'} P'` given by
`DifferentialGraded.Bimodule.restrictLeftTensorHom`. -/
@[simp] theorem restrictLeftTensorNatTrans_app (φ : A.Hom A') (P' : Bimodule A' B)
    (Y : DifferentialGradedModule.{u, u, u} A') :
    (restrictLeftTensorNatTrans φ P').app Y = restrictLeftTensorHom φ P' Y := rfl

/-! ### The comparison attached to a semilinear homomorphism of bimodules -/

/-- **The comparison of the plain tensor functors over two algebras attached to a semilinear
homomorphism of bimodules.** Let `φ : A ⟶ A'` be a homomorphism of differential graded algebras,
`P` a differential graded `(A, B)`-bimodule, `P'` a differential graded `(A', B)`-bimodule and
`f : P ⟶ P'|_φ` a homomorphism of differential graded `(A, B)`-bimodules into the restriction of
`P'` — that is, a `φ`-semilinear homomorphism `P ⟶ P'`. Then
`τ : (- |_A) ⊗_A P ⟶ - ⊗_{A'} P'`
is the natural transformation whose component at a differential graded `A'`-module `Y` sends the
pure tensor `y ⊗ p` to the pure tensor `y ⊗ f(p)`.

It is tensoring with `f` over the single algebra `A`
(`DifferentialGraded.Bimodule.tensorModuleNatTrans`), followed by the comparison
`DifferentialGraded.Bimodule.restrictLeftTensorNatTrans` attached to `φ`.

This is the datum `DifferentialGraded.Bimodule.DerivedTensorTower.plainCmp` of a tower of derived
tensor products over a varying algebra, and the input of
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans`. -/
def tensorCompNatTransOfSemilinear (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (f : P ⟶ Bimodule.restrictLeft φ P') :
    restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P' :=
  Functor.whiskerLeft (restrictScalarsFunctor φ) (tensorModuleNatTrans f) ≫
    restrictLeftTensorNatTrans φ P'

/-- **The comparison on pure tensors, which determines it.** The component of
`DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear` at `Y` sends the pure tensor `y ⊗ p`
of `Y|_A ⊗_A P` to the pure tensor `y ⊗ f(p)` of `Y ⊗_{A'} P'`. -/
theorem tensorCompNatTransOfSemilinear_app_pure (φ : A.Hom A') (P : Bimodule A B)
    (P' : Bimodule A' B) (f : P ⟶ Bimodule.restrictLeft φ P')
    (Y : DifferentialGradedModule.{u, u, u} A')
    (x : ((restrictScalarsFunctor φ).obj Y).M) (y : P.rightModule.M) :
    ((tensorCompNatTransOfSemilinear φ P P' f).app Y).toFun
        (((tensorDGFunctor P).pure ((restrictScalarsFunctor φ).obj Y)).toLinearMap x y) =
      ((tensorDGFunctor P').pure Y).toLinearMap x (f.rightHom.toFun y) := by
  change (restrictLeftTensorHom φ P' Y).toFun
      ((tensorHomOfBimoduleHom f ((restrictScalarsFunctor φ).obj Y)).toFun
        (((tensorDGFunctor P).pure ((restrictScalarsFunctor φ).obj Y)).toLinearMap x y)) = _
  rw [tensorHomOfBimoduleHom_pure, restrictLeftTensorHom_pure]

/-- The comparison attached to the identity of a restricted bimodule is the comparison attached
to the homomorphism of algebras alone. -/
theorem tensorCompNatTransOfSemilinear_id (φ : A.Hom A') (P' : Bimodule A' B) :
    tensorCompNatTransOfSemilinear φ (Bimodule.restrictLeft φ P') P'
        (𝟙 (Bimodule.restrictLeft φ P')) =
      restrictLeftTensorNatTrans φ P' := by
  rw [tensorCompNatTransOfSemilinear, tensorModuleNatTrans_id, Functor.whiskerLeft_id',
    Category.id_comp]

end DifferentialGraded.Bimodule

end
