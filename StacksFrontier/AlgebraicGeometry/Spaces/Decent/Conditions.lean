module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Conditions on algebraic spaces

Stacks 03JX lists nine conditions on an algebraic space `X` over a scheme `S` and relates
them by a diagram of implications. The source names them by the Greek letters `(α)` to
`(ι)`; each of them is a finiteness or separation condition already named elsewhere in the
library or named here, and this file is the single place where all nine are available.

The three conditions the library did not already carry are defined here: `(α)`, finiteness
of the fibres of every affine étale chart above every point; `(γ)`, finiteness of the fibres
of every affine étale chart *and* of its self-intersection above every point; and `(ι)`,
representability by a quasi-separated scheme.

## The nine conditions of Stacks 03JX

The conditions, with the declaration expressing each one. The six marked `(elsewhere)` are
pre-existing; the three unmarked ones are defined in this file.

* `(α)` `AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`
* `(β)` `AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint` (elsewhere:
  `StacksFrontier/AlgebraicGeometry/Spaces/Decent.lean`)
* `(γ)` `AlgebraicGeometry.Space.HasFiniteChartAndRelationFibersAtEveryPoint`
* `(δ)` `AlgebraicGeometry.Space.IsReasonableSpace` (elsewhere:
  `StacksFrontier/AlgebraicGeometry/Spaces/Reasonable.lean`)
* `(ε)` `AlgebraicGeometry.Space.IsVeryReasonableSpace` (elsewhere:
  `StacksFrontier/AlgebraicGeometry/Spaces/Reasonable.lean`)
* `(ζ)` `AlgebraicGeometry.Space.IsAbsolutelyZariskiLocallyQuasiSeparated` (elsewhere:
  `StacksFrontier/AlgebraicGeometry/Spaces/Separated.lean`)
* `(η)` `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` (elsewhere:
  `StacksFrontier/AlgebraicGeometry/Spaces/Separated.lean`)
* `(θ)` `CategoryTheory.Functor.IsRepresentable` (elsewhere: Mathlib)
* `(ι)` `AlgebraicGeometry.Space.IsQuasiSeparatedScheme`

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint` is condition `(α)`: above every
  point of `X`, every étale chart of `X` by an affine scheme has a finite fibre.
* `AlgebraicGeometry.Space.HasFiniteChartAndRelationFibersAt` is condition (1) of
  Stacks 03JV at one point: every étale chart of `X` by an affine scheme has a finite fibre
  there, and so does its self-intersection.
* `AlgebraicGeometry.Space.HasFiniteChartAndRelationFibersAtEveryPoint` is condition `(γ)`,
  that condition at every point.
* `AlgebraicGeometry.Space.IsQuasiSeparatedScheme` is condition `(ι)`: `X` is represented by
  an object of the site whose underlying scheme is quasi-separated.

## Main results

* `HasFiniteChartAndRelationFibersAtEveryPoint.hasFiniteChartAndRelationFibersAt`
  reads off the pointwise content of `(γ)`.
* `AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_isEmpty_points` and
  `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_isEmpty_points`:
  `(α)` and `(γ)` are vacuous on a presheaf with no points.

## Implementation notes

Stacks 03JX phrases `(α)`, `(β)` and `(γ)` as "for every `x ∈ |X|` the equivalent conditions
of Lemma 03JS, 03JU, 03JV hold", so each formalization must pick one of the conditions of
the cited lemma. `(α)` is taken as condition (2) of Stacks 03JS, `(β)` as condition (1) of
Stacks 03JU (which is the choice `AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint`
already makes) and `(γ)` as condition (1) of Stacks 03JV. **Stacks 03JU is now proved** — its
three pairwise equivalences are in
`StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative` and
`StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers` — so `(β)` agrees with the other
formulations of its source condition outright. **Stacks 03JS is now proved** as well, as
`AlgebraicGeometry.Space.exists_etaleCover_finite_fibre_iff_forall_affine_etale` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/FinitenessConditions.lean`, so `(α)` likewise
agrees with the other formulation of its source condition outright. Of Stacks 03JV **the
equivalence of conditions (1) and (4) is now proved**, which is the comparison `(γ)` needs;
the tag's full list of six conditions is not yet assembled here.

In particular `(γ)` is the condition Stacks 03I8 uses to define a *decent* algebraic space,
but `AlgebraicGeometry.Space.IsDecentSpace` spells that definition with condition (4) of
Stacks 03JV — a quasi-compact monomorphism from the spectrum of a field — so
`HasFiniteChartAndRelationFibersAtEveryPoint` and `IsDecentSpace` are two different
predicates expressing the same source notion, and their equivalence is exactly the content
of the conditions (1) and (4) part of Stacks 03JV. That `Iff` now exists:
`AlgebraicGeometry.Space.isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/QuasiCompactMonomorphicPoint.lean`. The
corresponding comparisons for `(δ)` and `(ε)` are available too:
`AlgebraicGeometry.Space.isReasonableSpace_iff_exists_boundedEtaleCover` is Stacks 03JT and
`isVeryReasonableSpace_iff_exists_isZariskiCover_quasiCompact_chart` is Stacks 03IH; see
`StacksFrontier/AlgebraicGeometry/Spaces/Reasonable.lean` for how those two conditions are
spelled.

Étaleness of a chart is taken in the representable sense,
`CategoryTheory.MorphismProperty.presheaf` of the inverse image of `AlgebraicGeometry.Etale` —
as in `AlgebraicGeometry.Space.IsReasonableSpace`, and as Stacks 03JS and 03JV put it on
`U → X` — not `AlgebraicGeometry.Space.IsEtale` of Stacks 03FR. The self-intersection
`R = U ×_X U` is the pullback in the presheaf category, and its fibre above a point of `X`
is taken along either projection followed by the chart, the two being equal by
`CategoryTheory.Limits.pullback.condition`. Nothing here assumes the presheaf is an
algebraic space; as in the source that hypothesis is imposed by clients, and it is what
makes each condition equivalent to the other formulations of its source lemma.

The two separation conditions `(ζ)` and `(η)` are absolute, so they take the extra
hypothesis that the chosen big fppf site contains the terminal scheme; `(θ)` and `(ι)` are
conditions on the presheaf alone. `HasFiniteChartAndRelationFibersAt` is a `def`, matching
`AlgebraicGeometry.Space.HasQuasiCompactMonomorphicFieldRepresentative`, so that a proof of
the Stacks 03JV equivalences folds onto it unchanged; the two conditions on a space are
`abbrev`s, as the neighbouring conditions are, so their quantifiers are directly available
to the locality and base-change statements about them.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03IH](https://stacks.math.columbia.edu/tag/03IH)
* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Condition `(α)`: finite chart fibres -/

/-- **Condition `(α)` of Stacks 03JX.** Above every point of `X`, every étale chart of `X`
by an affine scheme has a finite fibre. This is condition (2) of Stacks 03JS at every
point. -/
abbrev HasFiniteChartFibersAtEveryPoint : Prop :=
  ∀ (x : points B S hS X) (U : BigFppfOver B S hS),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ φ : yoneda.obj U ⟶ X,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ →
      (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}).Finite

/-- Condition `(α)` is vacuous on a presheaf with no points. -/
theorem hasFiniteChartFibersAtEveryPoint_of_isEmpty_points
    (h : IsEmpty (points B S hS X)) :
    HasFiniteChartFibersAtEveryPoint B S hS X :=
  fun x ↦ h.elim x

/-! ### Condition `(γ)`: finite chart and relation fibres -/

/-- **Stacks 03JV, condition (1).** Every étale chart `φ : h_U ⟶ X` of `X` by an affine
scheme has a finite fibre above `x`, and so does its self-intersection `h_U ×_X h_U`. -/
def HasFiniteChartAndRelationFibersAt (x : points B S hS X) : Prop :=
  ∀ U : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ φ : yoneda.obj U ⟶ X,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ →
      (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x}).Finite ∧
        (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) ⁻¹' {x}).Finite

/-- **Condition `(γ)` of Stacks 03JX.** Every point of `X` satisfies the equivalent
conditions of Stacks 03JV, taken here in the form of condition (1): every étale chart of `X`
by an affine scheme and its self-intersection both have finite fibres there. -/
abbrev HasFiniteChartAndRelationFibersAtEveryPoint : Prop :=
  ∀ x : points B S hS X, HasFiniteChartAndRelationFibersAt B S hS X x

/-- Condition `(γ)` gives condition (1) of Stacks 03JV at every point. -/
theorem HasFiniteChartAndRelationFibersAtEveryPoint.hasFiniteChartAndRelationFibersAt
    (h : HasFiniteChartAndRelationFibersAtEveryPoint B S hS X) (x : points B S hS X) :
    HasFiniteChartAndRelationFibersAt B S hS X x := h x

/-- Condition `(γ)` is vacuous on a presheaf with no points. -/
theorem hasFiniteChartAndRelationFibersAtEveryPoint_of_isEmpty_points
    (h : IsEmpty (points B S hS X)) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X :=
  fun x ↦ h.elim x

/-! ### Condition `(ι)`: a quasi-separated scheme -/

/-- **Condition `(ι)` of Stacks 03JX.** The algebraic space `X` is a quasi-separated
scheme: it is represented by an object of the big fppf site over `S` whose underlying scheme
has quasi-separated topological space. -/
abbrev IsQuasiSeparatedScheme : Prop :=
  ∃ U : BigFppfOver B S hS,
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      Nonempty (X.RepresentableBy U)

end AlgebraicGeometry.Space

end
