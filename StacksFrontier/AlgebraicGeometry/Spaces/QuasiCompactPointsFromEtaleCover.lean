module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsChartFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreTransfer

/-!
# Condition (2) of Stacks 03JV implies condition (1)

Let `F` be an algebraic space over a scheme `S` and let `x` be a point of `|F|` for which there
is a family of étale charts `ψ i : h_{V i} ⟶ F`, with surjective coproduct, such that the fibres
of `|V i| → |F|` and of `|R i| → |F|` above `x` are finite for every `i`, where
`R i = h_{V i} ×_F h_{V i}` — condition (2) of Stacks 03JV. This file proves condition (1): the
same two finiteness statements for *every* étale chart with affine source.

This is the implication that closes the first cycle in Stacks 03JV: condition (1) implies
condition (2) is
`AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover`,
so conditions (1) and (2) become equivalent.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.HasFiniteFibresOnSomeEtaleCover.hasFiniteFibresOnEveryAffineEtaleChart`
  is Stacks 03JV, condition (2) implies condition (1).
* `AlgebraicGeometry.Space.hasFiniteFibresOnEveryAffineEtaleChart_iff_onSomeEtaleCover`
  is Stacks 03JV, conditions (1) and (2) are equivalent: the implication above together with
  its converse from
  `StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactPointsFiniteFibres.lean`.

## Implementation notes

The proof is the source's, and uses exactly the two lemmas the source routes it through.

The chart-fibre half is Stacks 03JS, `AlgebraicGeometry.Space.finite_chartFibre_of_etaleCover`:
the covering family of condition (2) has finite chart fibres above `x`, so every affine étale
chart does.

The relation-fibre half is Stacks 03JU. Condition (2) gives condition (1) of Stacks 03JU at `x`:
some member of the covering family has a point `c` above `x` — surjectivity of the coproduct is
joint surjectivity on points by
`AlgebraicGeometry.Space.exists_pointsMap_eq_of_isSurjective_sigmaDesc` — and the relation fibre
of that member above the pair `(c, c)` is contained in the fibre of `|R i| → |F|` above `x`,
which condition (2) declares finite. Stacks 03JU, part (1) implies part (2)
(`AlgebraicGeometry.Space.HasFiniteRelationFiberAt.hasFiniteRelationFiberAtEveryEtaleChart`)
then bounds the relation fibre of the given affine chart above *every* pair of points over `x`,
and the fibre of `|R| → |F|` above `x` is the union of those over the pairs of points of the
chart fibre, which the first half has just made finite.

Only the two conditions (1) and (2) of Stacks 03JV are related here; no other implication of that
tag is claimed, and in particular the tag's six-fold equivalence is *not* proved.

## References

* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_QuasiCompactPointsFromEtaleCover :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, at high priority. -/
local instance (priority := high) hasPullback_presheaf_QuasiCompactPointsFromEtaleCover
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 03JV, condition (2) implies condition (1).** If some family of étale charts of an
algebraic space `F` over `S` with surjective coproduct has finite chart and relation fibres above
a point `x` of `|F|`, then every étale chart of `F` with affine source has finite chart and
relation fibres above `x`.

The chart half is Stacks 03JS. For the relation half, condition (2) supplies condition (1) of
Stacks 03JU at `x`, so Stacks 03JU, part (1) implies part (2), bounds the relation fibre above
each pair of points of the — now finite — chart fibre, and the fibre of `|R| → |F|` above `x` is
the union of those. -/
@[stacks 03JV "part (2) implies part (1)"]
theorem HasFiniteFibresOnSomeEtaleCover.hasFiniteFibresOnEveryAffineEtaleChart
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (h : HasFiniteFibresOnSomeEtaleCover B S hS F x) :
    HasFiniteFibresOnEveryAffineEtaleChart B S hS F x := by
  obtain ⟨I, V, ψ, hψ, hsurj, hfib⟩ := h
  intro U hUaff φ hφ
  -- The chart fibre, by Stacks 03JS.
  have hchart : (chartFibre B S hS F φ x).Finite :=
    finite_chartFibre_of_etaleCover B S hS F ψ hψ hsurj (fun i => (hfib i).1) U hUaff φ hφ
  refine ⟨hchart, ?_⟩
  -- Condition (1) of Stacks 03JU holds at `x`, on a member of the covering family with a point
  -- above `x`.
  obtain ⟨i, c, hc⟩ := exists_pointsMap_eq_of_isSurjective_sigmaDesc B S hS ψ hsurj x
  have hone : HasFiniteRelationFiberAt B S hS F x := by
    refine ⟨V i, ψ i, c, c, hψ i, hc, hc, Set.Finite.subset (hfib i).2 ?_⟩
    rintro r ⟨hr₁, -⟩
    change pointsMap B S hS (pullback (ψ i) (ψ i))
      (pullback.fst (ψ i) (ψ i) ≫ ψ i) r = x
    rw [pointsMap_comp_apply, hr₁, hc]
  have hevery := HasFiniteRelationFiberAt.hasFiniteRelationFiberAtEveryEtaleChart B S hS F hF hone
  -- The relation fibre above `x` is the union of the relation fibres above the pairs of points
  -- of the chart fibre.
  have hsub : relationFibre B S hS F φ x ⊆
      ⋃ a ∈ chartFibre B S hS F φ x, ⋃ b ∈ chartFibre B S hS F φ x,
        {r : points B S hS (pullback φ φ) |
          pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r = a ∧
          pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r = b} := by
    intro r hr
    have hr' : pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) r = x := hr
    have ha : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r) = x := by
      rw [← pointsMap_comp_apply]; exact hr'
    have hb : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r) = x := by
      rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply]
      exact ha
    exact Set.mem_biUnion ha (Set.mem_biUnion hb ⟨rfl, rfl⟩)
  refine Set.Finite.subset (Set.Finite.biUnion hchart fun a ha =>
    Set.Finite.biUnion hchart fun b hb => hevery U φ a b hφ ha hb) hsub

/-! ### Conditions (1) and (2) are equivalent -/

/-- **Stacks 03JV, conditions (1) and (2) are equivalent.** For a point `x` of an algebraic
space `F` over `S`, finiteness of the chart and relation fibres above `x` on *every* étale
chart with affine source holds if and only if it holds on the members of *some* étale
covering family.

This is the first equivalence of Stacks 03JV to be closed. The forward direction is
`AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteFibresOnSomeEtaleCover`,
which reads the covering family off the affine atlas of Stacks 03FX; the reverse direction is
`AlgebraicGeometry.Space.HasFiniteFibresOnSomeEtaleCover.hasFiniteFibresOnEveryAffineEtaleChart`
above, which is the source's own argument through Stacks 03JS and 03JU. Algebraicity of `F` is
used in both directions and is not removable: the atlas of Stacks 03FX and the transfer of
Stacks 03JU each require it. -/
@[stacks 03JV "conditions (1) and (2)"]
theorem hasFiniteFibresOnEveryAffineEtaleChart_iff_onSomeEtaleCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} :
    HasFiniteFibresOnEveryAffineEtaleChart B S hS F x ↔
      HasFiniteFibresOnSomeEtaleCover B S hS F x :=
  ⟨fun h => h.hasFiniteFibresOnSomeEtaleCover B S hS F hF,
   fun h => h.hasFiniteFibresOnEveryAffineEtaleChart B S hS F hF⟩

end AlgebraicGeometry.Space

end
