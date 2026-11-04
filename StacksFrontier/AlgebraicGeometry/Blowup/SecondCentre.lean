module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleComposition
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreFactorization
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreLocal
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Capture
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Operations
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf

/-!
# The second-centre factorization

Let `Y` be a quasi-compact and quasi-separated scheme, let `I` be a finitely presented centre on
`Y` with blowup `b : Y' = Bl_I(Y) ⟶ Y` and exceptional ideal `E = I·𝒪_{Y'}`, and let `Z'` be a
finitely presented centre on `Y'`. Then there are `d > 0` and a finite-type ideal sheaf
`J ≤ Iᵈ` on `Y` with

* `J·𝒪_{Y'} = Eᵈ · Z'`, and
* `J` agreeing with `Iᵈ` outside `Supp I ∪ b(Supp Z')`.

This is `Stacks.Blowup.SecondCentreFactorization`, the input that turns two successive blowups
into one: it is what the amalgamation of two successive centres in
`StacksFrontier/AlgebraicGeometry/Blowup/SuccessiveCentre.lean` and of two flattening centres in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/IteratedCentreFlatness.lean` carry as a
hypothesis. It is discharged here by delegation to `Stacks.Blowup.exists_factorization_blowUp`
of `StacksFrontier/AlgebraicGeometry/Blowup/SecondCentreFactorization.lean`, which proves exactly
this existential in the vocabulary of the blowup charts and is also what makes
`Stacks.Blowup.IsAdmissibleBlowup.comp` unconditional. One proof body therefore serves both the
predicate and the composition theorem.

## Main results

* `AlgebraicGeometry.secondCentreFactorization`: the statement above.

## References

* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The second-centre factorization.** For a finitely presented centre `I` on a quasi-compact
quasi-separated scheme `Y` and a finitely presented centre `Z'` on the blowup
`b : Bl_I(Y) ⟶ Y`, there are `d > 0` and a finite-type ideal sheaf `J ≤ Iᵈ` on `Y` whose inverse
image is `Eᵈ · Z'`, for `E` the exceptional ideal, and which agrees with `Iᵈ` away from
`Supp I ∪ b(Supp Z')`.

This discharges `Stacks.Blowup.SecondCentreFactorization`, the input that turns two successive
blowups into one.

As a statement it is what one gets by specialising
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_presentation_supp`, Tag 0803,
to the Rees algebra `⨁ₙ Iⁿ`, whose relative Proj is the blowup: the degree-`d` submodule `ℱ` of
the tag becomes the ideal sheaf `J ≤ Iᵈ` and the quasi-compact open `U` of the base becomes the
complement of `Supp I ∪ b(Supp Z')`. It is not proved that way here. The proof delegates to
`Stacks.Blowup.exists_factorization_blowUp` of
`StacksFrontier/AlgebraicGeometry/Blowup/SecondCentreFactorization.lean`, whose conclusion is this
existential verbatim, so that the predicate and `Stacks.Blowup.IsAdmissibleBlowup.comp` rest on
one proof body. -/
theorem secondCentreFactorization : Stacks.Blowup.SecondCentreFactorization.{u} :=
  fun I hI Z' hZ' ↦ Stacks.Blowup.exists_factorization_blowUp I hI Z' hZ'

end AlgebraicGeometry

end
