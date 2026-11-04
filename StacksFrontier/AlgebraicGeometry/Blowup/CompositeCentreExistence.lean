module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreExistence

/-!
# Stacks Tag 080B: the composite of two blowups is a blowup

Let `X` be a quasi-compact and quasi-separated scheme, let `I` be a finitely presented centre on
`X` with blowup `b : X' ⟶ X`, and let `Z'` be a finitely presented centre on `X'`. Then there is
a finitely presented centre `Y` on `X` with `Supp Y = Supp I ∪ b(Supp Z')` for which the
two-step blowup `Bl_{Z'}(X') ⟶ X' ⟶ X` is the blowup of `X` in `Y`, over `X`. That is
[Stacks, Tag 080B].

The centre is the product `I · J` of `I` with the second-centre ideal that
`Stacks.Blowup.exists_secondCentre` produces from `Z'`, and the two clauses are then
`AlgebraicGeometry.supportSet_mul_eq_union_image` and
`AlgebraicGeometry.nonempty_blowUpCompositionIso`.

## Main results

* `AlgebraicGeometry.exists_centre_supportSet_eq_and_nonempty_blowUpCompositionIso`:
  **[Stacks, Tag 080B].**
* `AlgebraicGeometry.exists_centre_supportSet_eq`: its part (1), the support of the centre.
* `AlgebraicGeometry.exists_centre_nonempty_blowUpCompositionIso`: its part (2), the composite
  blowup.

## Implementation notes

These three statements are here rather than in
`StacksFrontier/AlgebraicGeometry/Blowup/CompositeCentre.lean`, where the two clauses are proved,
only because of the import graph: the second centre is built in
`StacksFrontier/AlgebraicGeometry/Blowup/SecondCentreExistence.lean`, whose chain of imports
passes through `StacksFrontier/AlgebraicGeometry/Blowup/CentreNormalizeChart.lean` and
`StacksFrontier/AlgebraicGeometry/Blowup/CentreInsidePower.lean`, and the latter imports
`CompositeCentre.lean`.

Finite presentation of the product centre is `AlgebraicGeometry.finitePresentation_mul_subschemeι`,
and the two hypotheses of finite type it and `Stacks.Blowup.exists_secondCentre` need are read
off the two finite-presentation hypotheses by `Stacks.finitePresentation_iff_fg_ker` together
with `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`.

## References

* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A centre with finitely presented subscheme is of finite type. -/
private theorem isFiniteType_of_finitePresentation {S : Scheme.{u}}
    {K : S.IdealSheafData} (h : FinitePresentation K.subschemeι) : K.IsFiniteType := by
  rwa [finitePresentation_iff_fg_ker, Scheme.IdealSheafData.ker_subschemeι] at h

/-- **Stacks Project, Tag 080B.** Let `X` be a quasi-compact and quasi-separated scheme, let `I`
be a finitely presented centre on `X` with blowup `b : X' ⟶ X`, and let `Z'` be a finitely
presented centre on `X'`. Then there is a finitely presented centre `Y` on `X` whose support is
`Supp I ∪ b(Supp Z')` and for which the two-step blowup `Bl_{Z'}(X') ⟶ X' ⟶ X` is the blowup of
`X` in `Y`, over `X`.

The centre is the product `I · J` of `I` with the second-centre ideal that
`Stacks.Blowup.exists_secondCentre` produces from `Z'`. -/
@[stacks 080B]
theorem exists_centre_supportSet_eq_and_nonempty_blowUpCompositionIso
    [CompactSpace X] [QuasiSeparatedSpace X] (I : X.IdealSheafData)
    (hI : FinitePresentation I.subschemeι) (Z' : (blowUp I).IdealSheafData)
    (hfp : FinitePresentation Z'.subschemeι) :
    ∃ Y : X.IdealSheafData, FinitePresentation Y.subschemeι ∧
      Y.supportSet = I.supportSet ∪ (blowUpToBase I).base '' Z'.supportSet ∧
        Nonempty (Over.mk (blowUpToBase Z' ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase Y)) := by
  obtain ⟨d, J, -, hJft, -, hcomap⟩ := Stacks.Blowup.exists_secondCentre I
    (isFiniteType_of_finitePresentation hI) Z' (isFiniteType_of_finitePresentation hfp)
  exact ⟨I * J, finitePresentation_mul_subschemeι I J hI hJft,
    supportSet_mul_eq_union_image I Z' d J hcomap,
    nonempty_blowUpCompositionIso I Z' d J hcomap⟩

/-- **The support of the centre of [Stacks, Tag 080B].** There is a finitely presented centre
`Y` on `X` with `Supp Y = Supp I ∪ b(Supp Z')`. -/
@[stacks 080B "part (1), the support of the centre"]
theorem exists_centre_supportSet_eq [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : FinitePresentation I.subschemeι)
    (Z' : (blowUp I).IdealSheafData) (hfp : FinitePresentation Z'.subschemeι) :
    ∃ Y : X.IdealSheafData, FinitePresentation Y.subschemeι ∧
      Y.supportSet = I.supportSet ∪ (blowUpToBase I).base '' Z'.supportSet := by
  obtain ⟨Y, hY, hsupp, -⟩ :=
    exists_centre_supportSet_eq_and_nonempty_blowUpCompositionIso I hI Z' hfp
  exact ⟨Y, hY, hsupp⟩

/-- **The composite of two blowups is a blowup, [Stacks, Tag 080B].** There is a finitely
presented centre `Y` on `X` for which blowing `X` up in `Y` is the two-step blowup
`Bl_{Z'}(X') ⟶ X' ⟶ X`, over `X`. -/
@[stacks 080B "part (2), the composite of the two blowups is the blowup in the centre"]
theorem exists_centre_nonempty_blowUpCompositionIso [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : FinitePresentation I.subschemeι)
    (Z' : (blowUp I).IdealSheafData) (hfp : FinitePresentation Z'.subschemeι) :
    ∃ Y : X.IdealSheafData, FinitePresentation Y.subschemeι ∧
      Nonempty (Over.mk (blowUpToBase Z' ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase Y)) := by
  obtain ⟨Y, hY, -, hiso⟩ :=
    exists_centre_supportSet_eq_and_nonempty_blowUpCompositionIso I hI Z' hfp
  exact ⟨Y, hY, hiso⟩

end AlgebraicGeometry

end
