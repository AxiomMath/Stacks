module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

/-!
# The rank of the torsion-free quotient is the generic rank

Over an integral domain `A` with fraction field `K`, the rank of the torsion-free quotient of a
module `M` is the dimension over `K` of the localization of `M` at `(0)`. Both sides of the
equation are the number of elements in a maximal `A`-independent family in `M`; the quotient
by the torsion changes neither.

## Main results

* `Stacks.OrderOfVanishing.finrank_quotient_torsion_eq_finrank_localization`: **the rank of
  `M ⧸ tors` equals the dimension of the localization of `M` at `(0)`.**

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public section

namespace Stacks.OrderOfVanishing

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [CommRing K] [Algebra A K]
  [IsFractionRing A K] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [Module K N] [IsScalarTower A K N]

omit [IsDomain A] in
/-- **The rank of the torsion-free quotient is the dimension of the localization at `(0)`.**
If `g : M →ₗ[A] N` exhibits the `K`-module `N` as the localization of `M` at the nonzero divisors
of `A`, then the rank of `M ⧸ Submodule.torsion A M` over `A` equals the dimension of `N`
over `K`. -/
public theorem finrank_quotient_torsion_eq_finrank_localization (g : M →ₗ[A] N)
    [IsLocalizedModule (nonZeroDivisors A) g] :
    Module.finrank A (M ⧸ Submodule.torsion A M) = Module.finrank K N := by
  rw [finrank_quotient_eq_of_le_torsion le_rfl,
    IsLocalization.finrank_eq K (nonZeroDivisors A) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors A) g le_rfl]

end Stacks.OrderOfVanishing

end
