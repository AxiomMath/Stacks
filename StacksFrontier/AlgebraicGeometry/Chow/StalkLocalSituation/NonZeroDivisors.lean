module

public import StacksFrontier.AlgebraicGeometry.DenominatorLocalRatio.MulCokernel
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# The germs of a local ratio of a regular meromorphic section are nonzerodivisors

The length formula of [Stacks, Tag 02QH] is applied at `R = 𝒪_{X, ξ}` to the germs of a local
ratio `a / b` of a meromorphic section `s` of an invertible `𝒪_X`-module, and asks for both
germs to be nonzerodivisors in `R`. This file assembles that from the two statements it
needs: the numerator of the ratio of a *regular* meromorphic section is a nonzerodivisor on the
affine open where the ratio lives
(`Stacks.DenominatorCokernel.mem_nonZeroDivisors_of_trivialization`), and a nonzerodivisor on
an affine open has nonzerodivisor germs (`Stacks.Divisors.germ_mem_nonZeroDivisors`).

## Main results

* `Stacks.Chow.StalkLocalSituation.germ_numerator_mem_nonZeroDivisors`: the germ of the
  numerator of a local ratio of a regular meromorphic section is a nonzerodivisor in the local
  ring at any point of the affine open carrying the ratio.

## Implementation notes

The hypotheses are the data that `Stacks.DenominatorLocalRatio.exists_affineOpen_denominator`
produces at the affine open it finds: a trivialization `e` of `L` there, a denominator `b` that
is a nonzerodivisor on the open, a section `t` of `L` with `t = b · s` in `K_X(L)`, and the
numerator `a = e t`. The affine open and the point in it are arbitrary, so this applies to
whichever chart a consumer is handed, provided that chart comes with that data.

For the denominator there is nothing to assemble: `Stacks.Divisors.germ_mem_nonZeroDivisors`
applied to `b` is already the statement, modulo Mathlib's
`isRegular_iff_mem_nonZeroDivisors` between the two spellings of the hypothesis. It is not
restated here.

The scalars of a trivialization are written at `Stacks.DenominatorLocalRatio.oScalar`, which is
the `RingCat` spelling of `Γ(X, V)` and the same carrier type, while the nonzerodivisor
submonoid is written at `Γ(X, V)`; that mixture is the established idiom of the files consumed
here and needs no transport.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorLocalRatio

universe u

namespace Stacks.Chow.StalkLocalSituation

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X))
  (s : MeromorphicSection.{u, u} X.sheaf L)

/-- **The germ of the numerator of a local ratio of a regular meromorphic section is a
nonzerodivisor in the local ring.** The numerator is a nonzerodivisor on the affine open
carrying the ratio because the section is regular, and the local ring is a localization of the
ring of functions on that open. -/
theorem germ_numerator_mem_nonZeroDivisors
    (hs : IsRegularMeromorphicSection X.sheaf L s) {V : Opens X} (hV : IsAffineOpen V)
    (e : (L.val.obj (op V) : Type u) ≃ₗ[oScalar X V] (oScalar X V))
    (b : oScalar X V) (hb : b ∈ nonZeroDivisors Γ(X, V)) (t : (L.val.obj (op V) : Type u))
    (hbt : (toK X L).val.app (op V) t = (sectionMap X L s).val.app (op V) b)
    {a : Γ(X, V)} (ha : e t = a) {x : X} (hx : x ∈ V) :
    X.presheaf.germ V x hx a ∈ nonZeroDivisors (X.presheaf.stalk x) :=
  Stacks.Divisors.germ_mem_nonZeroDivisors hV
    (isRegular_iff_mem_nonZeroDivisors.mpr
      (Stacks.DenominatorCokernel.mem_nonZeroDivisors_of_trivialization X L s hs e b hb t hbt
        a ha))
    x hx

end Stacks.Chow.StalkLocalSituation

end
