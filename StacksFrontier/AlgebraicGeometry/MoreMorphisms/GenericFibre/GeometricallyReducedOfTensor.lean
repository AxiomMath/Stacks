module

import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE

/-!
# Geometric reducedness from a single domain base change

If `K̄` is an algebraic closure of a field `K` and `L ⊗[K] K̄` is a domain, then the `K`-algebra
`L` is geometrically reduced.

## Main results

* `Algebra.isGeometricallyReduced_of_isDomain_tensor_isAlgClosure`: if `K̄` is an algebraic
  closure of `K` and `L ⊗[K] K̄` is a domain, then `L` is geometrically reduced over `K`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 030V](https://stacks.math.columbia.edu/tag/030V)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- If `K̄` is an algebraic closure of `K` and `L ⊗[K] K̄` is a domain, then `L` is geometrically
reduced over `K`. -/
theorem isGeometricallyReduced_of_isDomain_tensor_isAlgClosure (K : Type u) [Field K]
    (L : Type v) [CommRing L] [Algebra K L] (Kbar : Type w) [Field Kbar] [Algebra K Kbar]
    [IsAlgClosure K Kbar] (h : IsDomain (L ⊗[K] Kbar)) :
    Algebra.IsGeometricallyReduced K L := by
  have : IsReduced (L ⊗[K] Kbar) := isReduced_of_noZeroDivisors
  exact ((Algebra.isGeometricallyReduced_tfae K (ringExpChar K) L
    (perfectClosure K (AlgebraicClosure K)) Kbar).out 4 6).mp
      (isReduced_of_injective (Algebra.TensorProduct.comm K Kbar L).toRingHom
        (Algebra.TensorProduct.comm K Kbar L).injective)

end Algebra

end
