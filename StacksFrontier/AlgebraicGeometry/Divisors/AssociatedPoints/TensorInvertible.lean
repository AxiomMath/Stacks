module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators

/-!
# The associated points of a tensor product with an invertible module are unchanged

Let `X` be a scheme, `F` an `𝒪_X`-module and `L` an invertible `𝒪_X`-module. Then
`Ass(F ⊗ L) = Ass(F)`.

## Main results

* `Stacks.Divisors.associatedPoints_tensorObj_eq`: `Ass(F ⊗ L) = Ass(F)` for `L` invertible.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **`Ass(F ⊗ L) = Ass(F)` for `L` invertible.** -/
theorem associatedPoints_tensorObj_eq (F L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    associatedPoints (AlgebraicGeometry.Scheme.Modules.tensorObj F L) = associatedPoints F := by
  ext x
  obtain ⟨eL⟩ := nonempty_stalk_linearEquiv_of_isInvertible L x
  let e : (AlgebraicGeometry.Scheme.Modules.tensorObj F L).presheaf.stalk x
      ≃ₗ[X.presheaf.stalk x] F.presheaf.stalk x :=
    (AlgebraicGeometry.tensorStalkEquiv F L x).trans
      ((TensorProduct.congr (LinearEquiv.refl (X.presheaf.stalk x) (F.presheaf.stalk x)) eL).trans
        (TensorProduct.rid (X.presheaf.stalk x) (F.presheaf.stalk x)))
  exact ⟨isAssociatedPrimeStacks_of_linearEquiv e, isAssociatedPrimeStacks_of_linearEquiv e.symm⟩

end Stacks.Divisors

end
