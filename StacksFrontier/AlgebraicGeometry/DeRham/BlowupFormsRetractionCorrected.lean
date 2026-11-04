module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsRetractionExistence
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDirectImageCodimensionZero
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsHigherDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The unique retraction of `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}`, in corrected form

Let `f : X ⟶ S` be smooth, let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`, and let
`b : X' ⟶ X` be the blowing up of `X` along `Z`.  [Stacks, Tag 0G5J] asserts that for `a ≥ 0`
the canonical map `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` of `D(𝒪_X)` has exactly one retraction.

## The correction

As stated, the tag is false when `Z` contains a non-empty open subset of `X`.  For
`S = X = Z = Spec k` with `f = i = 𝟙` the ideal of the centre is zero and the blowup is empty
(`Stacks.DeRham.isEmpty_blowUp_bot`), so `Rb_*Ω^0_{X'/S} = 0` while `Ω^0_{X/S} = 𝒪_X ≠ 0`: the
map `𝒪_X ⟶ 0` has no retraction.  The counterexample is the one of [Stacks, Tag 0FUU],
`Stacks.DeRham.exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase`, whose degree-zero
comparison `𝒪_X ⟶ b_*𝒪_{X'} = 0` is the `H^0` of the map here.  The source's proof does not reach
this case: its local model (Section 0FUB) has a centre of codimension `n ≥ 1`.

The corrected statement adds the single hypothesis that the image of `i` has empty interior in
`X`, which is exactly what makes `n ≥ 1` on every étale chart; it is the correction made to
[Stacks, Tag 0FUU] clauses (1) and (2).

## Main results

* `Stacks.DeRham.existsUnique_blowUpFormsRetraction_blowUpToBase`: if the image of `i` has
  empty interior, then `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` has exactly one retraction.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)

/-- **[Stacks, Tag 0G5J], in corrected form.**  Let `f : X ⟶ S` be smooth, let `i : Z ⟶ X` be a
closed immersion with `Z` smooth over `S` and with image of empty interior in `X`, and let
`b : X' ⟶ X` be the blowing up of `X` along `Z`.  For every `a ≥ 0` there is exactly one arrow
`Rb_*Ω^a_{X'/S} ⟶ Ω^a_{X/S}` in `D(𝒪_X)` whose composite with the canonical map
`Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` is the identity.

The hypothesis on the interior corrects the source: for `S = X = Z = Spec k` the blowup is empty
and `𝒪_X ⟶ 0` has no retraction
(`Stacks.DeRham.exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase`,
`Stacks.DeRham.isEmpty_blowUp_bot`).  The proof is the source's.  Existence: the canonical map
followed by `Rb_*` of the second map of [Stacks, Tag 0G5G] is the twist map of
[Stacks, Tag 0G5H] for `𝒟 = Σ_c (c - 1)E_c`, an isomorphism.  Uniqueness: by
[Stacks, Tag 0FUU] (3) the higher direct images are pushed forward from the centre, and
[Stacks, Tags 0E7D and 0G5I] kill every map from the cone to `Ω^a_{X/S}`. -/
@[stacks 0G5J "corrected form: for f smooth and i : Z ⟶ X a closed immersion of a scheme smooth \
over S whose image has EMPTY INTERIOR in X, and b = blowUpToBase i.ker, for every a ≥ 0 there is \
a unique arrow Rb_*Ω^a_{X'/S} ⟶ Ω^a_{X/S} in D(𝒪_X) whose composite with the canonical \
Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S} is the identity. The interior hypothesis is a correction: as stated \
the lemma is false when Z contains a nonempty open of X — for S = X = Z = Spec k the blowup is \
empty (Stacks.DeRham.isEmpty_blowUp_bot) and 𝒪_X ⟶ 0 has no retraction (counterexample of 0FUU: \
Stacks.DeRham.exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase)"]
theorem existsUnique_blowUpFormsRetraction_blowUpToBase [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅) (a : ℕ) :
    ∃! r : blowUpFormsObj f i.ker (a : ℤ) ⟶ formsSingle f (a : ℤ),
      blowUpFormsDerivedDirectImage f i.ker (a : ℤ) ≫ r = 𝟙 (formsSingle f (a : ℤ)) :=
  existsUnique_blowUpFormsRetraction_of_isIso_homology f i hint a fun _ hq =>
    isIso_homology_blowupFormsDerivedComparison f i a hq

end Stacks.DeRham

end
