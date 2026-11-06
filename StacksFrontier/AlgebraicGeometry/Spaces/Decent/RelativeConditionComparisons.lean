module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableImpliesFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable

/-!
# Implications between the finiteness conditions on a morphism of algebraic spaces

The conditions of Stacks 03KZ on a morphism `f : X ⟶ Y` of algebraic spaces over `S` —
property `(β)`, decency, reasonableness and very reasonableness — are each the corresponding
absolute condition on every base change of `f` along a morphism from a representable
presheaf. The implications between them are therefore the implications between the absolute
conditions of Stacks 03JX, read on each such base change, which is an algebraic space by
Stacks 02X2.

This file carries three of the five implications of the diagram of Stacks 03M5: the arrow into
very reasonableness from representability, and the two at the decent end.

## Main results

* `AlgebraicGeometry.Space.isVeryReasonable_of_relativelyRepresentable`: a representable
  morphism is very reasonable.
* `AlgebraicGeometry.Space.isDecent_of_isReasonable`: a reasonable morphism is decent.
* `AlgebraicGeometry.Space.hasPropertyBeta_of_isDecent`: a decent morphism has property
  `(β)`.

## Implementation notes

Decency of an algebraic space is spelled with condition (4) of Stacks 03JV and property
`(γ)` with condition (1), so each step passes through
`AlgebraicGeometry.Space.isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint`.

A represented base change of a representable morphism is itself represented, so the arrow from
representability is the composite `(θ) ⇒ (ζ) ⇒ (ε)` of Stacks 03JX read on each base change.
The condition `(ζ)` in between is an absolute separation condition, stated for a big fppf site
containing the terminal scheme; that is no extra assumption, because
`AlgebraicGeometry.BigFppfSite.contains_terminal` discharges it for every big fppf site.

The other two implications of Stacks 03M5 are elsewhere, each beside the absolute statement it
is read off: `quasi-separated ⇒ very reasonable` is
`AlgebraicGeometry.Space.isVeryReasonable_of_isQuasiSeparated` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/QuasiSeparatedVeryReasonable.lean`, and
`very reasonable ⇒ reasonable` is
`AlgebraicGeometry.Space.isReasonable_of_isVeryReasonable` in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/VeryReasonableImpliesReasonable.lean`.

## References

* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03M5](https://stacks.math.columbia.edu/tag/03M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_RelativeConditionComparisons :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_RelativeConditionComparisons
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_RelativeConditionComparisons B S hS).has_limit _

/-- A base change of a morphism of algebraic spaces along a representable presheaf is an
algebraic space. -/
private theorem isAlgebraicSpace_pullback_yoneda (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {T : BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ Y) : IsAlgebraicSpace B S hS (pullback g f) :=
  isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY

/-- **Stacks 03M5, representable implies very reasonable.** A representable morphism of
algebraic spaces over `S` is very reasonable: each of its represented base changes is again a
representable algebraic space, hence Zariski locally quasi-separated by the implication
`(θ) ⇒ (ζ)` of Stacks 03JX and very reasonable by `(ζ) ⇒ (ε)`. -/
@[stacks 03M5 "representable implies very reasonable"]
theorem isVeryReasonable_of_relativelyRepresentable (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) : IsVeryReasonable B S hS f := by
  intro T g
  have halg := isAlgebraicSpace_pullback_yoneda B S hS hX hY f g
  have hrep : (pullback g f).IsRepresentable :=
    (Functor.representableByEquiv.symm (hf.isPullback g).flip.isoPullback).isRepresentable
  exact isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS
    B.contains_terminal _ halg
    (isAbsolutelyZariskiLocallyQuasiSeparated_of_isRepresentable B S hS _
      B.contains_terminal halg hrep)

/-- **Stacks 03M5, reasonable implies decent.** A reasonable morphism of algebraic spaces
over `S` is decent: each of its represented base changes is a reasonable algebraic space,
hence satisfies property `(γ)` of Stacks 03JX by the implication `(δ) ⇒ (γ)`, which is
decency. -/
@[stacks 03M5 "reasonable implies decent"]
theorem isDecent_of_isReasonable (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsReasonable B S hS f) :
    IsDecent B S hS f := by
  intro T g
  have halg := isAlgebraicSpace_pullback_yoneda B S hS hX hY f g
  exact (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS _ halg).mpr
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isReasonableSpace B S hS _ halg (hf T g))

/-- **Stacks 03M5, decent implies property `(β)`.** A decent morphism of algebraic spaces
over `S` has property `(β)`: each of its represented base changes is a decent algebraic
space, hence satisfies property `(β)` of Stacks 03JX by the implication `(γ) ⇒ (β)`. -/
@[stacks 03M5 "decent implies property (beta)"]
theorem hasPropertyBeta_of_isDecent (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsDecent B S hS f) :
    HasPropertyBeta B S hS f := by
  intro T g
  have halg := isAlgebraicSpace_pullback_yoneda B S hS hX hY f g
  exact hasFiniteRelationFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers B S hS _ halg
    ((isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS _ halg).mp (hf T g))

end AlgebraicGeometry.Space

/-! ### Remark 68.17.10

Stacks 03L4 states no proposition of its own. Of its four sentences one compares the
conditions — "being reasonable is a bit stronger" than being decent — and that comparison is
sharp as the implication `reasonable ⇒ decent` of Stacks 03M5, which is the first theorem
above. Its other mathematical sentence, that a morphism has one of the conditions when, in the
source's words "(very) loosely speaking", the fibres do, is sharp as Stacks 03L3 and carries
the tag in `StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria`. -/

add_to_stacks 03L4 "Remark 68.17.10, which states no proposition of its own: its comparative
  sentence, that being reasonable is a bit stronger than being decent, is sharp only as the
  implication `reasonable ⇒ decent` of Stacks 03M5, which is this theorem."
  AlgebraicGeometry.Space.isDecent_of_isReasonable

end
