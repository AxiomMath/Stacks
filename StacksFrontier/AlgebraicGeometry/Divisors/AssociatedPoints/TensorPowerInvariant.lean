module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwist

/-!
# The associated points of a tensor power twist are unchanged, for every integer degree

Let `X` be a scheme, `F` an `𝒪_X`-module and `L` an invertible `𝒪_X`-module. Twisting `F` by an
integer tensor power of `L` does not change its associated points:

`Ass(F ⊗ L^{⊗ n}) = Ass(F)`, for every `n : ℤ`.

## Main results

* `Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq`: `Ass(F ⊗ L^{⊗ n}) = Ass(F)`,
  for every `n : ℤ`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- Twisting an `𝒪_X`-module by an integer tensor power of an invertible module does not change
its associated points: `Ass(F ⊗ L^{⊗ n}) = Ass(F)`. -/
theorem associatedPoints_tensorObj_tensorPowScheme_eq (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    associatedPoints
        (AlgebraicGeometry.Scheme.Modules.tensorObj F (Stacks.Algebraization.tensorPowScheme X L n))
      = associatedPoints F := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Algebraization.tensorPowScheme X L n) :=
    Stacks.Algebraization.isInvertibleModule_tensorPowScheme X L n
  exact associatedPoints_tensorObj_eq F _

end Stacks.Divisors

end
