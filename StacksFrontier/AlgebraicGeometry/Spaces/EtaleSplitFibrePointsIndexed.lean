module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange

/-!
# The first paragraph of Stacks 082H with the replacement family indexed and quasi-finite

The first paragraph of the proof of Stacks 082H replaces the morphism `f : X ⟶ Y` of algebraic
spaces over `S` by its base change along an étale neighbourhood `(U, u) ⟶ (Y, y)` of the
prescribed point of the target, and replaces the prescribed points `x₁, …, x_n` of `|X|` by the
set of points `w ∈ |U ×_Y X|` lying over `u` and over one of the `xᵢ`. For the replacement to be
a replacement, that set must be presented the way the prescribed points were: as a *finite
indexed family* at whose members the base change is *quasi-finite*.

`AlgebraicGeometry.Space.exists_affine_etale_neighbourhood_finite_fibrePoints` proves the set in
question is finite and says nothing else about it. This file indexes it and proves the base
change quasi-finite at each of its members, which are the two properties the second paragraph
of the source proof consumes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_etale_neighbourhood_fibrePoints_eq` is the first paragraph of
  the proof of Stacks 082H in the form the second paragraph needs: an affine étale neighbourhood
  of the prescribed point of the target, together with a finite family of points of the base
  change, indexed by a `Fin`, which lie over the distinguished point, at which the base change
  is quasi-finite, each of which lies over one of the `xᵢ`, and which exhausts the points with
  those last two properties.
* `AlgebraicGeometry.Space.exists_etale_neighbourhood_fibrePoints_eq_surjective` adds to that
  conclusion the statement that every prescribed point `xᵢ` is hit: it is the image of some
  member of the family. This is what makes the replacement of `x₁, …, x_n` by the family lossless.

## Implementation notes

The indexing is `Finset.equivFin` of the `Set.Finite.toFinset` of the finite set, the idiom
already used for the points of the chart in
`AlgebraicGeometry.Space.exists_affine_chart_isolated_fibre_points`. Nothing weaker would do:
the conclusion asks for a family indexed by a `Fin`, and transporting an indexing of the `xᵢ`
would produce neither an exhaustive family (several `w` can lie over one `xᵢ`) nor a
well-defined one (several `xᵢ` can be equal).

Quasi-finiteness of the base change at each member of the family is part (2) of Tag 0ABM
pointwise, `AlgebraicGeometry.Space.isQuasiFiniteAt_iff_of_isPullback`, applied to the cartesian
square `CategoryTheory.IsPullback.of_hasPullback g f`, in which `pullback.fst g f` is the base
change of `f` and `pullback.snd g f` is the projection to `X`. Each member of the family lies
over some `xᵢ` by construction, and `f` is quasi-finite there by hypothesis.

The exhaustiveness clause is a universally quantified implication, so on its own it would be
consistent with the family being empty. It is not:
`AlgebraicGeometry.Space.exists_etale_neighbourhood_fibrePoints_eq_surjective` exhibits, for
each `i`, a point satisfying its antecedent — the point of the fibre product over `u` and `xᵢ`
produced by Tag 03H4 (`AlgebraicGeometry.Space.exists_points_of_isPullback`) — and so shows
every `xᵢ` is the image of a member of the family. That the stronger form is derivable from the
weaker one *by a consumer*, using only hypotheses the statement already carries, is the reason
the exhaustiveness clause is the right way to state the first paragraph.

Nothing here carries the tag 082H, and nothing here is the tag: Stacks 082H has a single
assertion, whose enumerated items (1)–(4) are its hypotheses, and the étale-local splitting it
asserts is stated nowhere yet.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0AC6](https://stacks.math.columbia.edu/tag/0AC6)
* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasPullback_presheaf_etaleSplitFibrePointsIndexed
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-! ### The first paragraph, with the family indexed and quasi-finite at its members -/

/-- **The replacement family of the first paragraph of Stacks 082H, indexed and quasi-finite.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type, let
`y` be a point of `|Y|` and let `x₁, …, x_n` be points of `|X|` over `y` at which `f` is
quasi-finite. If `f` is quasi-compact or `Y` is decent, then there are an object `Y₀` of the big
fppf site of `S` with affine underlying scheme, an étale morphism `g : h_{Y₀} ⟶ Y`, a point `u`
of `|h_{Y₀}|` over `y`, and a finite family `w₁, …, w_p` of points of `|h_{Y₀} ×_Y X|` such that
each `wⱼ` lies over `u`, the base change of `f` is quasi-finite at each `wⱼ`, each `wⱼ` lies over
one of the `xᵢ`, and every point of `|h_{Y₀} ×_Y X|` lying over `u` and over one of the `xᵢ` is
one of the `wⱼ`.

This is the first paragraph of the proof of Stacks 082H, in the form its second paragraph
consumes. Finiteness of the set in question is
`AlgebraicGeometry.Space.exists_affine_etale_neighbourhood_finite_fibrePoints`, the indexing is
`Finset.equivFin` of its `Set.Finite.toFinset`, and quasi-finiteness of the base change at each
member is part (2) of Tag 0ABM pointwise,
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_of_isPullback`. -/
theorem exists_etale_neighbourhood_fibrePoints_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y) {n : ℕ} (x : Fin n → points B S hS X)
    (hx : ∀ i, pointsMap B S hS X f (x i) = y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqf : ∀ i, IsQuasiFiniteAt B S hS f (x i))
    (hqc : IsQuasiCompact B S hS f ∨ IsDecentSpace B S hS Y) :
    ∃ (Y₀ : BigFppfOver B S hS) (g : yoneda.obj Y₀ ⟶ Y)
      (u : points B S hS (yoneda.obj Y₀)) (p : ℕ)
      (w : Fin p → points B S hS (pullback g f)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀) ∧
      IsEtale B S hS g ∧
      pointsMap B S hS (yoneda.obj Y₀) g u = y ∧
      (∀ j, pointsMap B S hS (pullback g f) (pullback.fst g f) (w j) = u) ∧
      (∀ j, IsQuasiFiniteAt B S hS (pullback.fst g f) (w j)) ∧
      (∀ j, ∃ i, pointsMap B S hS (pullback g f) (pullback.snd g f) (w j) = x i) ∧
      (∀ q : points B S hS (pullback g f),
        pointsMap B S hS (pullback g f) (pullback.fst g f) q = u →
          (∃ i, pointsMap B S hS (pullback g f) (pullback.snd g f) q = x i) →
            q ∈ Set.range w) := by
  classical
  obtain ⟨Y₀, g, u, hY₀, hgE, hgu, hfin⟩ :=
    exists_affine_etale_neighbourhood_finite_fibrePoints B S hS hX hY f y x hx hft hqf hqc
  set T : Set (points B S hS (pullback g f)) :=
    {q | pointsMap B S hS (pullback g f) (pullback.fst g f) q = u ∧
      ∃ i, pointsMap B S hS (pullback g f) (pullback.snd g f) q = x i} with hT
  have hTfin : T.Finite := hfin
  set w : Fin hTfin.toFinset.card → points B S hS (pullback g f) :=
    fun j => ((hTfin.toFinset.equivFin.symm j : { a // a ∈ hTfin.toFinset }) :
      points B S hS (pullback g f)) with hw
  have hrange : Set.range w = T := by
    have h1 : Set.range w = Set.range (Subtype.val :
        { a // a ∈ hTfin.toFinset } → points B S hS (pullback g f)) :=
      hTfin.toFinset.equivFin.symm.surjective.range_comp _
    rw [h1, Subtype.range_coe_subtype]
    ext a
    simp [Set.Finite.mem_toFinset]
  have hmem : ∀ j, w j ∈ T := fun j => hrange.subset (Set.mem_range_self j)
  refine ⟨Y₀, g, u, hTfin.toFinset.card, w, hY₀, hgE, hgu, fun j => (hmem j).1, ?_,
    fun j => (hmem j).2, fun q h1 h2 => by rw [hrange]; exact ⟨h1, h2⟩⟩
  intro j
  obtain ⟨i, hi⟩ := (hmem j).2
  rw [isQuasiFiniteAt_iff_of_isPullback B S hS (IsPullback.of_hasPullback g f) hX hY
    (isAlgebraicSpace_yoneda B S hS Y₀) hft (w j), hi]
  exact hqf i

/-- **The replacement family of the first paragraph of Stacks 082H hits every prescribed
point.** In the situation of
`AlgebraicGeometry.Space.exists_etale_neighbourhood_fibrePoints_eq` the family `w₁, …, w_p` can
moreover be required to satisfy: every prescribed point `xᵢ` is the image of some `wⱼ` under the
projection to `X`. In particular the family is nonempty as soon as there is at least one
prescribed point, so its exhaustiveness clause is not vacuous.

This is the remaining content of "we may replace `x₁, …, x_n` by the set of these `w`": the
replacement loses no prescribed point. It is derived from
`AlgebraicGeometry.Space.exists_etale_neighbourhood_fibrePoints_eq` by Tag 03H4
(`AlgebraicGeometry.Space.exists_points_of_isPullback`), which produces a point of the fibre
product lying over `u` and over `xᵢ`; the exhaustiveness clause then places that point in the
family. -/
theorem exists_etale_neighbourhood_fibrePoints_eq_surjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y) {n : ℕ} (x : Fin n → points B S hS X)
    (hx : ∀ i, pointsMap B S hS X f (x i) = y)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqf : ∀ i, IsQuasiFiniteAt B S hS f (x i))
    (hqc : IsQuasiCompact B S hS f ∨ IsDecentSpace B S hS Y) :
    ∃ (Y₀ : BigFppfOver B S hS) (g : yoneda.obj Y₀ ⟶ Y)
      (u : points B S hS (yoneda.obj Y₀)) (p : ℕ)
      (w : Fin p → points B S hS (pullback g f)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀) ∧
      IsEtale B S hS g ∧
      pointsMap B S hS (yoneda.obj Y₀) g u = y ∧
      (∀ j, pointsMap B S hS (pullback g f) (pullback.fst g f) (w j) = u) ∧
      (∀ j, IsQuasiFiniteAt B S hS (pullback.fst g f) (w j)) ∧
      (∀ j, ∃ i, pointsMap B S hS (pullback g f) (pullback.snd g f) (w j) = x i) ∧
      (∀ q : points B S hS (pullback g f),
        pointsMap B S hS (pullback g f) (pullback.fst g f) q = u →
          (∃ i, pointsMap B S hS (pullback g f) (pullback.snd g f) q = x i) →
            q ∈ Set.range w) ∧
      (∀ i, ∃ j, pointsMap B S hS (pullback g f) (pullback.snd g f) (w j) = x i) := by
  obtain ⟨Y₀, g, u, p, w, hY₀, hgE, hgu, hwu, hwqf, hwx, hwall⟩ :=
    exists_etale_neighbourhood_fibrePoints_eq B S hS hX hY f y x hx hft hqf hqc
  refine ⟨Y₀, g, u, p, w, hY₀, hgE, hgu, hwu, hwqf, hwx, hwall, ?_⟩
  intro i
  obtain ⟨q, hq1, hq2⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g f) u (x i) (hgu.trans (hx i).symm)
  obtain ⟨j, hj⟩ := hwall q hq1 ⟨i, hq2⟩
  exact ⟨j, by rw [hj]; exact hq2⟩

end AlgebraicGeometry.Space

end
