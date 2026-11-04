module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Finite
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents

/-!
# The special fibre of a regular model when every multiplicity is one

In the situation of Tag 0C61 write `X_k = ∑ mᵢ Cᵢ`. If every multiplicity `mᵢ` is one then the
special fibre is reduced, being cut out by the radical ideal `∏ I_{Cᵢ}`. This is the first step
of the last paragraphs of Sections 0CEG and 0CEI of the Stacks project ("`X_k` is the scheme
theoretic union of the `Cᵢ`"); the geometric reducedness of `X_k` when moreover every `Cᵢ` is
smooth is
`Stacks.Models.RegularProperModelSituation.geometricallyReduced_specialFiberToSpec_of_smooth`.

## Main results

* `Stacks.Models.RegularModelSituation.isReduced_specialFiber_of_multiplicity_eq_one` — the
  special fibre is reduced when every multiplicity is one.

## References

* [Stacks Project, Section 0CEG](https://stacks.math.columbia.edu/tag/0CEG)
* [Stacks Project, Section 0CEI](https://stacks.math.columbia.edu/tag/0CEI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- **The special fibre is reduced when every multiplicity is one.** The ideal of `X_k` in `X`
is `∏ I_{Cᵢ}^{mᵢ}` (Tag 0C5Z) and its radical is `∏ I_{Cᵢ}`, so with all `mᵢ = 1` the ideal is
its own radical and `X_k` is reduced. -/
theorem isReduced_specialFiber_of_multiplicity_eq_one
    (h : ∀ Z, S.specialFiberMultiplicity Z = 1) : IsReduced S.specialFiber := by
  have hI : S.specialFiberIdeal.radical = S.specialFiberIdeal := by
    rw [S.radical_specialFiberIdeal_eq_prod, S.specialFiberIdeal_eq_prod]
    simp [h]
  have := Stacks.AffineClosedUnion.isReduced_subscheme_of_radical_eq hI
  exact isReduced_of_isOpenImmersion (asIso S.specialFiberι.toImage).hom

end RegularModelSituation

end Stacks.Models
