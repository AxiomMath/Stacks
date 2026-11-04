module

public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Vanishing at the closed point, read on the punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring and `M` an `A`-module. For `n ≥ 1`, the vanishing of
`H^{n+1}` of local cohomology of `M` with support in the closed point implies the vanishing of
`H^n(U, M̃|U)` on the punctured spectrum `U`.

## Main results

* `Stacks.PuncturedSpectrumPicard.isZero_localCohomologyModule_of_isZero_closedPoint`: if local
  cohomology of `M` with support in the closed point vanishes in some degree, so does the local
  cohomology module `H^i_𝔪(M)` in that degree.
* `Stacks.PuncturedSpectrumPicard.isZero_hgroup_complementTilde_of_isZero_closedPoint`: the
  vanishing of `H^{n+1}` with support in the closed point gives the vanishing of `H^n` of
  `M̃` restricted to the punctured spectrum, for `n ≥ 1`.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IsLocalRing

universe u

namespace Stacks.PuncturedSpectrumPicard

attribute [local instance] HasDerivedCategory.standard

open Stacks.LocalCohomology (localCohomologyWithSupportIn localCohomologyModule
  complementZeroLocus complementTilde isIso_compareSectionsWithSupportLocalCohomology_app
  isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule)

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Let `(A, 𝔪)` be a Noetherian local ring and `M` an `A`-module. If the degree-`i` local
cohomology of `M` with support in the closed point vanishes, then so does the local cohomology
module `H^i_𝔪(M)`. -/
theorem isZero_localCohomologyModule_of_isZero_closedPoint
    (M : ModuleCat.{u} A) (i : ℤ)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i)) :
    IsZero (localCohomologyModule A (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) M i) := by
  rw [← zeroLocus_maximalIdeal (R := A)] at h
  have hiso := isIso_compareSectionsWithSupportLocalCohomology_app.{u, u} A (maximalIdeal A)
    (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
  refine h.of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (@asIso _ _ _ _ _ hiso)).symm

/-- For a Noetherian local ring `(A, 𝔪)` and `n ≥ 1`, if local cohomology of `M` with support in
the closed point vanishes in degree `n + 1`, then the degree-`n` cohomology of `M̃` restricted to
the punctured spectrum vanishes. -/
theorem isZero_hgroup_complementTilde_of_isZero_closedPoint
    (M : ModuleCat.{u} A) (n : ℕ) (hn : 1 ≤ n)
    (h : IsZero (localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ((n : ℤ) + 1))) :
    IsZero (Hgroup (complementZeroLocus A (maximalIdeal A) : Scheme).ringCatSheaf ⊤ n
      (complementTilde A (maximalIdeal A) M)) :=
  (isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) M n hn).mpr
    (isZero_localCohomologyModule_of_isZero_closedPoint A M ((n : ℤ) + 1) h)

end Stacks.PuncturedSpectrumPicard

end
