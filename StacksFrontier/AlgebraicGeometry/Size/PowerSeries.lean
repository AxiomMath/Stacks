module

public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite

/-!
# Power series rings stay below the cutoff of a big site

A power series `f ∈ A⟦t⟧` is its sequence of coefficients, so `#A⟦t⟧ ≤ #A ^ ℵ₀`, which is a
bound of the shape of Stacks 000R (9). A big fppf site containing `Spec A` therefore contains
`Spec A⟦t⟧`: the cutoff is a strong limit cardinal. This is how the spectrum of `k⟦t⟧`, the base
of the smoothings of Stacks 0E7Y, lies in every site containing `Spec k`, with no hypothesis on
the site.

## Main results

* `Cardinal.mk_powerSeries_le`: `#A⟦t⟧ ≤ #A ^ ℵ₀`.
* `AlgebraicGeometry.BigFppfSite.contains_spec_powerSeries`: a big fppf site containing `Spec A`
  contains `Spec A⟦t⟧`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
-/

@[expose] public section

open Cardinal

universe u

/-- A power series ring has at most `#A ^ ℵ₀` elements: a power series is its sequence of
coefficients. -/
theorem Cardinal.mk_powerSeries_le (A : Type u) [CommRing A] :
    Cardinal.mk (PowerSeries A) ≤ Cardinal.mk A ^ ℵ₀ := by
  have hinj : Function.Injective (fun (f : PowerSeries A) (n : ℕ) => PowerSeries.coeff n f) :=
    fun f g h => PowerSeries.ext (congrFun h)
  calc Cardinal.mk (PowerSeries A) ≤ Cardinal.mk (ℕ → A) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk A ^ ℵ₀ := by simp

namespace AlgebraicGeometry.BigFppfSite

/-- **A big fppf site containing `Spec A` contains `Spec A⟦t⟧`.** The power series ring has at
most `#A ^ ℵ₀ ≤ size(Spec A) ^ ℵ₀` elements, and Stacks 000R (9) applies. -/
theorem contains_spec_powerSeries (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) : B.Contains (Spec (.of (PowerSeries A))) := by
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hA ?_
  rw [Scheme.size_Spec]
  exact (Cardinal.mk_powerSeries_le A).trans
    (Cardinal.power_le_power_right (le_max_right _ _))

end AlgebraicGeometry.BigFppfSite

end
