module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerTopBasis
public import StacksFrontier.RingTheory.OrderOfVanishing.ResidualCokernel

/-!
# The exterior-power form of the determinant bound over a discrete valuation ring

`StacksFrontier.RingTheory.OrderOfVanishing.ResidualCokernel` bounds the order of vanishing of the
determinant of the induced map on torsion-free quotients in a right exact sequence
`M → M' → N → 0` with `N ≅ κ^⊕ s`, in terms of a choice of bases. This file restates that bound
with no choice of bases visible, as the length of the cokernel of the `r`-th exterior power of
that induced map — the shape in which the determinant line bundles of [Stacks, Tag 0B3T] are
compared on the stalk at a codimension-one point.

The translation is `Stacks.ExteriorPower.length_quotient_range_map`: for free modules of rank
`r`, the cokernel of `⋀^r g` is `A/(det g)`.

## Main results

* `Stacks.OrderOfVanishing.length_quotient_range_exteriorPower_torsionQuotientMap_le_min`:
  **the bound in exterior-power form**, for a choice of bases of the torsion-free quotients.
* `Stacks.OrderOfVanishing.length_quotient_range_exteriorPower_torsionQuotientMap_le_min_of_finrank`
  : the same under the generic-rank hypothesis, with no basis taken as data — the quotients are
  free because a discrete valuation ring is a principal ideal domain.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public section

namespace Stacks.OrderOfVanishing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {r s : ℕ} {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  (f : M →ₗ[A] M')
  (e : (M' ⧸ LinearMap.range f) ≃ₗ[A] (Fin s → IsLocalRing.ResidueField A))

include e

/-- **The determinant bound in exterior-power form.** For `M → M' → N → 0` exact with
`N ≅ κ^⊕ s` and torsion-free quotients free of rank `r`, the cokernel of the `r`-th exterior
power of the induced map on those quotients has length at most `min s r`. -/
theorem length_quotient_range_exteriorPower_torsionQuotientMap_le_min
    (b : Module.Basis (Fin r) A (M ⧸ Submodule.torsion A M))
    (b' : Module.Basis (Fin r) A (M' ⧸ Submodule.torsion A M')) :
    Module.length A (⋀[A]^r (M' ⧸ Submodule.torsion A M') ⧸
        LinearMap.range (exteriorPower.map r (torsionQuotientMap f))) ≤ (min s r : ℕ) := by
  rw [Stacks.ExteriorPower.length_quotient_range_map b b' (torsionQuotientMap f)]
  exact length_span_det_torsionQuotient_le_min f e b b'

/-- **The determinant bound in exterior-power form at the generic rank.** No basis is taken as
data: over a discrete valuation ring a finite module whose torsion-free quotient has rank `r`
has that quotient free of rank `r`. -/
theorem length_quotient_range_exteriorPower_torsionQuotientMap_le_min_of_finrank
    [Module.Finite A M] [Module.Finite A M']
    (hr : Module.finrank A (M ⧸ Submodule.torsion A M) = r)
    (hr' : Module.finrank A (M' ⧸ Submodule.torsion A M') = r) :
    Module.length A (⋀[A]^r (M' ⧸ Submodule.torsion A M') ⧸
        LinearMap.range (exteriorPower.map r (torsionQuotientMap f))) ≤ (min s r : ℕ) :=
  length_quotient_range_exteriorPower_torsionQuotientMap_le_min f e
    (Module.finBasisOfFinrankEq A _ hr) (Module.finBasisOfFinrankEq A _ hr')

end Stacks.OrderOfVanishing

end
