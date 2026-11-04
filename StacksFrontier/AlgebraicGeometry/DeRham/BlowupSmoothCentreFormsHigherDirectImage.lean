module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDerivedComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (3) of Stacks 0FUU: higher direct images of forms on the blowup of a smooth centre

Let `f : X ⟶ S` be smooth and `i : Z ⟶ X` a closed immersion with `Z` smooth over `S`. Let
`b : X' ⟶ X` be the blowing up of `X` along `Z`, `E` its exceptional divisor and `p : E ⟶ Z` the
structure morphism. Clause (3) of [Stacks, Tag 0FUU] says that for every `a ≥ 0` the comparison
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in degrees `q ≥ 1`.

## Main results

* `Stacks.DeRham.isIso_homology_blowupFormsDerivedComparison`: clause (3), for every closed
  immersion of `S`-smooth schemes. Unlike clauses (1) and (2), it needs no hypothesis on the
  interior of the centre: a centre containing a nonempty open of `X` contributes a chart of
  codimension `0`, where the blowup and its exceptional divisor are empty and both sides vanish.

## The proof

The source's: the étale-local reduction to the coordinate model of [Stacks, Tag 0FUE] is
`Stacks.DeRham.isIso_homology_blowupFormsDerivedComparison_of_coordinate`, and on the coordinate
model `𝐀^{m+n}_S ⊇ 𝐀^m_S` with `n ≥ 1` the clause is clause (3) of [Stacks, Tag 0FUR],
`Stacks.DeRham.isIso_coordinateFormsRestrictionHomology`.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)

/-- **[Stacks, Tag 0FUU], clause (3).** Let `f : X ⟶ S` be smooth and `i : Z ⟶ X` a closed
immersion with `Z` smooth over `S`, let `b : X' ⟶ X` be the blowing up along `Z`, `E` its
exceptional divisor and `p : E ⟶ Z` the structure morphism. For every `a ≥ 0` and every `q ≥ 1`
the comparison `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}`
(`Stacks.DeRham.blowupFormsDerivedComparison`) is an isomorphism on `H^q`. -/
@[stacks 0FUU "clause (3): for f smooth and i a closed immersion of an S-smooth scheme, \
Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S} is an isomorphism on cohomology sheaves in every degree \
q ≥ 1. No interior hypothesis is needed for this clause"]
theorem isIso_homology_blowupFormsDerivedComparison [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (a : ℕ) {q : ℤ} (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
      (blowupFormsDerivedComparison f i (a : ℤ))) :=
  isIso_homology_blowupFormsDerivedComparison_of_coordinate (f := f) (i := i) a hq
    (fun R _ m n hn => isIso_coordinateFormsRestrictionHomology R m n hn a q hq)

end Stacks.DeRham
