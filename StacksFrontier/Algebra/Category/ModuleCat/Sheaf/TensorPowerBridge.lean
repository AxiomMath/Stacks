module

public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# The two integer tensor powers of an invertible sheaf of modules agree

The library carries two developments of the integer tensor power `L^{⊗ n}` of an invertible
sheaf of modules on a ringed site, differing only in the form in which invertibility of `L` is
taken: `Stacks.SheafOfModules.Invertible.tensorPower` assumes
`AlgebraicGeometry.SheafOfModules.IsInvertible`, while
`Stacks.SheafOfModules.TensorPower.tensorPower` assumes that tensoring on the right by `L` is an
equivalence. Both are the image of the structure sheaf under the `n`-th power of the
right-tensor autoequivalence, and this file records that they are the same object.

## Main results

* `Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible` and
  `Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible`: tensoring on
  the right by an invertible sheaf of modules, `(sheafTensor _).flip.obj L`, is an equivalence,
  from each of the library's two invertibility predicates.
* `Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`: the two integer tensor powers
  are the same sheaf of modules.

## Implementation notes

The two developments share the right-tensor functor
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L` but each has its own
`tensorPowerEquivalence` and its own invertibility hypothesis: the second takes the instance
`((sheafTensor _).flip.obj L).IsEquivalence` directly. This file supplies that instance from each
invertibility predicate, and once it is available the two powers are equal by `rfl`;
`CategoryTheory.Functor.IsEquivalence` is a `Prop`, so the equality does not depend on which
proof of it is supplied.

The transfer `Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry` is not an instance, since
two classes with instances in both directions make instance search cycle.
`isEquivalence_tensorRightFunctor_of_stacksIsInvertible` composes the transfer with the first
instance and creates no cycle, because what it produces is an `IsEquivalence` rather than an
invertibility.

Neither instance fires at a goal about a *scheme*, where the structure sheaf is spelled
`T.toRingedSpace.presheaf` and `isSheafStruct T` while the module's own type carries
`T.presheaf` and `T.ringCatSheaf.2`: the two are equal by `rfl` but do not unify at `instance`
transparency. `Stacks.AlgebraicGeometry.ProjRepresentsF1.isEquivalence_tensorRightFunctor_scheme`
is the same instance with its conclusion written at the first spelling and its hypothesis at the
second.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Tensoring on the right by an invertible sheaf of modules is an equivalence.** -/
instance isEquivalence_tensorRightFunctor_of_isInvertible
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence :=
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence O hO L

/-- **Tensoring on the right by an invertible sheaf of modules is an equivalence**, with
invertibility taken as `Stacks.SheafOfModules.IsInvertible`. -/
instance isEquivalence_tensorRightFunctor_of_stacksIsInvertible
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [hL : Stacks.SheafOfModules.IsInvertible O hO L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence :=
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible O hO L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry O hO L hL
  isEquivalence_tensorRightFunctor_of_isInvertible O hO L

/-- **The two integer tensor powers of an invertible sheaf of modules are the same sheaf.** Both
are the image of the structure sheaf under the `n`-th power of the autoequivalence given by
tensoring on the right by `L`. -/
theorem Invertible.tensorPower_eq_tensorPower
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (n : ℤ) :
    Stacks.SheafOfModules.Invertible.tensorPower O hO L n =
      Stacks.SheafOfModules.TensorPower.tensorPower O hO L n :=
  rfl

end Stacks.SheafOfModules

end
