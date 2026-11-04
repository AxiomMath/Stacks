module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFibresOneChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres

/-!
# Condition (3) of Stacks 03JV implies conditions (1) and (2)

Let `F` be an algebraic space over a scheme `S` and let `x` be a point of `|F|` presented by a
monomorphism `Spec(k) ⟶ F` whose base change along every étale chart of `F` with affine source
is a finite scheme over `k` — condition (3) of Stacks 03JV. This file proves condition (1): for
every affine scheme `U` and every étale `φ : h_U ⟶ F` the fibres of `|U| → |F|` and of
`|R| → |F|` above `x` are both finite, where `R = h_U ×_F h_U`. Condition (2) follows by the
established implication from condition (1).

## Main definitions

No new definitions are introduced.

## Main results

* `HasMonomorphicFieldRepresentativeWithFiniteCharts.hasFiniteFibresOnEveryAffineEtaleChart`,
  in the namespace `AlgebraicGeometry.Space`, is Stacks 03JV, condition (3) implies
  condition (1).
* `HasMonomorphicFieldRepresentativeWithFiniteCharts.hasFiniteFibresOnSomeEtaleCover`, in the
  same namespace, is Stacks 03JV, condition (3) implies condition (2), the composite with the
  established implication from condition (1).

## Implementation notes

**This is the source's argument, with its one gap filled.** Stacks 03JV says only that "the
equivalence of (1) and (3) follows on applying Lemma 040U to every étale morphism `U → X` with
`U` affine". Applied chart by chart in the direction (3) ⟹ (1) that is exactly right, except
that condition (2) of Stacks 040U asks the base change `Spec(k) ×_F U` to be **nonempty** and
its condition (1) concludes that `x` lies in the image of `|U| → |F|`, whereas conditions (1)
and (3) of Stacks 03JV ask for neither. The repository's 040U file settles this by proving the
nonemptiness-free form separately, as
`AlgebraicGeometry.Space.finite_chartFibre_and_relationFibre_of_mono_isFinite`
(`StacksFrontier/AlgebraicGeometry/Spaces/FiniteFibresOneChart.lean`), and that is what is applied
below; no case split on the emptiness of the chart fibre is needed here because that lemma has
already absorbed it.

**Two renderings of finiteness, and why they match on the nose.** The finiteness clause of
condition (3) is `AlgebraicGeometry.Space.IsFinite` of Stacks 03ZP applied to
`pullback.fst (fieldMorphism p) φ`, which is the *weaker* of the two forms in play — the
stronger being relative representability with every represented base change a finite morphism
of schemes. The tagged implication (2) ⟹ (1) of Stacks 040U and the lemma used here both take
the weak form as hypothesis, which is deliberate: the 040U file records that this is "the form
condition (3) of Stacks 03JV can actually feed". So the application is by substitution and not
through the remaining implication of Stacks 03ZQ, which is unavailable.

**No affineness is needed for the chart, and none is dropped.** Stacks 040U places no
affineness hypothesis on `U`, and neither does the lemma applied below; the affineness in
conditions (1) and (3) of Stacks 03JV is carried through unchanged, each quantifier running
over affine `U`, so the two line up argument for argument.

**What this does and does not close.** Composing with
`AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover`
gives condition (3) implies condition (2) as well, so condition (3) implies conditions (1)
and (2), which are already equivalent to each other. Nothing below claims any equivalence of
Stacks 03JV; the tags name single arrows. The converse direction of the adjacent equivalence of
conditions (2) and (3) has to produce a monomorphism out of the spectrum of a field from
finiteness of the fibres, which is the implication (1) ⟹ (2) of Stacks 040U, unconditional
as `AlgebraicGeometry.Space.exists_mono_isFinite_fieldFibre_of_finiteFibres`; assembling it into
condition (2) implies condition (3) of Stacks 03JV is not carried out here.

## References

* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 040U](https://stacks.math.columbia.edu/tag/040U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Condition (3) implies condition (1) -/

/-- **Stacks 03JV, condition (3) implies condition (1).** If a point `x` of an algebraic space
`F` over `S` is presented by a monomorphism `Spec(k) ⟶ F` whose base change along every étale
chart with affine source is finite over `Spec(k)`, then for every affine scheme `U` and every
étale `φ : h_U ⟶ F` the fibres of `|U| → |F|` and of `|R| → |F|` above `x`, where
`R = h_U ×_F h_U`, are both finite.

This is the source's "apply Lemma 040U to every étale morphism `U → X` with `U` affine", in the
nonemptiness-free form
`AlgebraicGeometry.Space.finite_chartFibre_and_relationFibre_of_mono_isFinite`: finiteness of
the field fibre over `Spec(k)` makes its point set finite and Stacks 03H4 maps that set onto
the chart fibre, after which the relation fibre is bounded by Stacks 0AC7 above each pair of
points of the chart fibre, the monomorphism being what 0AC7 needs. -/
@[stacks 03JV "part (3) implies part (1)"]
theorem HasMonomorphicFieldRepresentativeWithFiniteCharts.hasFiniteFibresOnEveryAffineEtaleChart
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasMonomorphicFieldRepresentativeWithFiniteCharts B S hS F x) :
    HasFiniteFibresOnEveryAffineEtaleChart B S hS F x := by
  obtain ⟨p, hpx, hmono, hfin⟩ := h
  intro U hUaff φ hφ
  exact finite_chartFibre_and_relationFibre_of_mono_isFinite B S hS F hF hφ p hpx hmono
    (hfin U hUaff φ hφ)

/-! ### Condition (3) implies condition (2) -/

/-- **Stacks 03JV, condition (3) implies condition (2).** The composite of the implication
above with
`AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover`:
a monomorphic representative with finite charts gives finiteness of the chart and relation
fibres on every affine étale chart, hence on the members of the affine étale covering family of
Stacks 03FX. -/
@[stacks 03JV "part (3) implies part (2)"]
theorem HasMonomorphicFieldRepresentativeWithFiniteCharts.hasFiniteFibresOnSomeEtaleCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasMonomorphicFieldRepresentativeWithFiniteCharts B S hS F x) :
    HasFiniteFibresOnSomeEtaleCover B S hS F x :=
  (h.hasFiniteFibresOnEveryAffineEtaleChart B S hS F hF).hasFiniteFibresOnSomeEtaleCover
    B S hS F hF

end AlgebraicGeometry.Space

end
