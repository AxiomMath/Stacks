module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Length.HenselizationBaseChange

/-!
# The order of vanishing is unchanged by a henselization

Let `R` be a local ring and let `Rh` be a henselization of `R` with respect to an extension of
its residue field. The structure map `R → Rh` is flat and local with `𝔪_R Rh = 𝔪_{Rh}`, so it
sends nonzerodivisors to nonzerodivisors and `length_R(R/xR) = length_{Rh}(Rh/x Rh)` for every
`x ∈ R`; that is, `ord_{Rh}(x) = ord_R(x)`.

## Main results

* `IsLocalRing.IsHenselization.algebraMap_mem_nonZeroDivisors`: the structure map of a
  henselization carries nonzerodivisors to nonzerodivisors.
* `IsLocalRing.IsHenselization.ord_algebraMap`: the order of vanishing of an element of `R` is
  the order of vanishing of its image in `Rh`.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

namespace IsLocalRing.IsHenselization

/-- The structure map of a henselization is flat, so multiplication by a nonzerodivisor of the
base stays injective after the base change: `R⁰` lands in `Rh⁰`. -/
theorem algebraMap_mem_nonZeroDivisors {R : Type*} [CommRing R] [IsLocalRing R]
    (L : Type*) [Field L] [Algebra (ResidueField R) L]
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsHenselization R L Rh]
    {x : R} (hx : x ∈ R⁰) : algebraMap R Rh x ∈ Rh⁰ := by
  have : Module.Flat R Rh := flat (L := L)
  refine mem_nonZeroDivisors_iff_right.2 fun y hy => ?_
  refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Rh) hx ?_
  simpa [Algebra.smul_def, mul_comm] using hy

/-- **(The order of vanishing is unchanged by a henselization.)** For `Rh` a henselization of a
local ring `R`, the quotient `Rh / x Rh` is the base change of `R / xR`, and the base change
along the structure map preserves lengths, so `ord_{Rh}(x) = ord_R(x)`. -/
theorem ord_algebraMap {R : Type*} [CommRing R] [IsLocalRing R]
    (L : Type*) [Field L] [Algebra (ResidueField R) L]
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsHenselization R L Rh]
    (x : R) : Ring.ord Rh (algebraMap R Rh x) = Ring.ord R x := by
  have hspan : Ideal.span {algebraMap R Rh x} = Ideal.map (algebraMap R Rh) (Ideal.span {x}) := by
    rw [Ideal.map_span, Set.image_singleton]
  calc Ring.ord Rh (algebraMap R Rh x)
      = Module.length Rh (Rh ⧸ Ideal.map (algebraMap R Rh) (Ideal.span {x})) := by
        rw [Ring.ord, hspan]
    _ = Module.length Rh (Rh ⊗[R] (R ⧸ Ideal.span {x})) :=
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Rh
          (Ideal.span {x})).toLinearEquiv.length_eq
    _ = Ring.ord R x := (length_baseChange_eq L (R ⧸ Ideal.span {x})).symm

end IsLocalRing.IsHenselization

end
