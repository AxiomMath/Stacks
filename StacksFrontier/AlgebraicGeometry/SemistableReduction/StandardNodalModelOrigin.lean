module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffinePointBlowup
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelBlowup

/-!
# The origin of the standard nodal model as a closed point, and the blowup there

Let `R` be a commutative ring in which `(π)` is maximal and let `n ≥ 1`. The ideal
`𝔪 = (π, x, y)` of the standard nodal model `X = Spec R[x, y]/(xy - πⁿ)` is then maximal
(`Stacks.isMaximal_nodalModelOrigin`), so it is a closed point of `X`. This file names that
point, records that its singleton is closed, and identifies the blowup of `X` at it — in the
sense of `AlgebraicGeometry.blowUp` applied to the reduced ideal sheaf of the point, which is the
blowup appearing in a chain of blowups at closed points — with
`Stacks.nodalModelBlowup`, the `Proj` of the Rees algebra of `𝔪` that
`StacksFrontier/AlgebraicGeometry/SemistableReduction/StandardNodalModelBlowup.lean` analyses chart
by chart.

## Main definitions

* `Stacks.nodalModelOriginPoint` — the origin `𝔪 = (π, x, y)` of the standard nodal model, as a
  point of the scheme `X`.

## Main results

* `Stacks.isClosed_singleton_nodalModelOriginPoint` — the origin is a closed point.
* `Stacks.nonempty_over_iso_blowUpToBase_nodalModelOriginPoint` — **the blowup of `X` at its
  origin is `Stacks.nodalModelBlowup`**, over `X`.
* `Stacks.isMaximal_span_singleton_of_irreducible` — in a discrete valuation ring an irreducible
  element generates a maximal ideal, the form in which the hypothesis above is met.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-- In a discrete valuation ring an irreducible element generates the maximal ideal. -/
public theorem isMaximal_span_singleton_of_irreducible [IsDomain R] [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) : (Ideal.span {π}).IsMaximal := by
  rw [← hπ.maximalIdeal_eq]
  exact IsLocalRing.maximalIdeal.isMaximal R

/-- The centre of the blowup resolving the standard nodal model of exponent `n` is the ideal of
the origin of that model. -/
public theorem nodalCenter_pow_eq_nodalModelOrigin (π : R) (n : ℕ) :
    nodalCenter R π (π ^ n) = nodalModelOrigin R π n := rfl

/-- **The origin `𝔪 = (π, x, y)` of the standard nodal model, as a point of `X = Spec A`.** -/
public def nodalModelOriginPoint {π : R} (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ} (hn : 1 ≤ n) :
    nodalModel R π n :=
  ⟨nodalModelOrigin R π n, (isMaximal_nodalModelOrigin hπ hn).isPrime⟩

/-- The prime ideal of `Stacks.nodalModelOriginPoint` is `𝔪 = (π, x, y)`. -/
@[simp] public theorem asIdeal_nodalModelOriginPoint {π : R}
    (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ} (hn : 1 ≤ n) :
    (nodalModelOriginPoint hπ hn).asIdeal = nodalModelOrigin R π n := rfl

/-- **The origin of the standard nodal model is a closed point**, its ideal being maximal. -/
public theorem isClosed_singleton_nodalModelOriginPoint {π : R}
    (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ} (hn : 1 ≤ n) :
    IsClosed ({nodalModelOriginPoint hπ hn} : Set (nodalModel R π n)) :=
  PrimeSpectrum.isClosed_singleton_iff_isMaximal _ |>.mpr (isMaximal_nodalModelOrigin hπ hn)

/-- **The blowup of the standard nodal model at its origin is `Stacks.nodalModelBlowup`**, over
the model. The left-hand side is the blowup in the reduced ideal sheaf of the closed point, which
is the blowup a chain of blowups at closed points takes; the right-hand side is the `Proj` of the
Rees algebra of `𝔪`, whose three affine charts are computed in
`StacksFrontier/AlgebraicGeometry/SemistableReduction/StandardNodalModelBlowup.lean`. -/
public theorem nonempty_over_iso_blowUpToBase_nodalModelOriginPoint {π : R}
    (hπ : (Ideal.span {π}).IsMaximal) {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (Over.mk (nodalModelBlowupHom R π n) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨{nodalModelOriginPoint hπ hn},
            isClosed_singleton_nodalModelOriginPoint hπ hn⟩ : Closeds (nodalModel R π n))))) :=
  nonempty_over_iso_blowUpToBase_vanishingIdeal (nodalChartRing R (π ^ n))
    (nodalModelOriginPoint hπ hn) (isClosed_singleton_nodalModelOriginPoint hπ hn)

end Stacks

end
