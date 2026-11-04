module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback

/-!
# The affine chart diagrams over a morphism of algebraic spaces are cover-dense

Let `g : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Call an étale scheme chart `W` of `X` *good for `g`* when its underlying scheme is
affine and it admits a morphism to an étale scheme chart of `X'` with affine underlying scheme,
compatibly with `g`; that is exactly the data of a commutative diagram of étale scheme charts
over `g` (`AlgebraicGeometry.Space.ChartDiagram`) whose two charts are affine, with `W` as its
chart of `X`.

This file proves that the good charts are **cover-dense in the small étale site of `X`**: every
sieve of a chart of `X` which contains all the morphisms out of good charts is a covering sieve.
This is the geometric input that turns a statement proved chartwise on affine chart diagrams
into a local statement on the small étale site of `X`.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineChartDiagram`: the property of an étale scheme chart of `X`
  of being good for `g` in the above sense.

## Main results

* `AlgebraicGeometry.Space.exists_hasAffineChartDiagram`: every point of every étale scheme
  chart of `X` is the image of a point of a good chart lying over it.  This is the geometric
  content.
* `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`: consequently a sieve of a
  chart of `X` containing every morphism out of a good chart is a covering sieve of the small
  étale site of `X`.

## Implementation notes

**The three stages.**  Fix a chart `U` of `X` and a point `z` of its underlying scheme.  The
good chart over `z` is produced in three steps, each of which lifts the point.

1. *Down to a chart of `X'`.*  The atlas of `X'`, read as an étale scheme chart `U₀` of `X'`
   whose structure morphism is surjective on points, is base changed to `X`:
   `AlgebraicGeometry.Space.exists_chart_over` produces a chart `V₁` of `X` over `U`, carrying a
   lift of `z`, together with a morphism `V₁ ⟶ U₀` of the site compatible with `g`.  Surjectivity
   of the atlas is what makes this possible for *every* point.
2. *Affine downstairs.*  The image of that lift in `U₀` lies in an affine open of `U₀`, which is
   again an étale chart `U''` of `X'` by `AlgebraicGeometry.Space.exists_affine_chart_at`.
   `AlgebraicGeometry.Space.exists_chart_pullback` base changes `V₁` along the inclusion
   `U'' ⟶ U₀` to a chart `T₂` of `X` lying over `U''`, again carrying a lift of the point.
3. *Affine upstairs.*  An affine open of `T₂` containing that lift is an affine étale chart `T₃`
   of `X` over `T₂`, and the composite `T₃ ⟶ T₂ ⟶ U''` makes `T₃` good for `g`.

The order matters: refining upstairs first would be undone by the base change of step 2, which
is why affineness of the chart of `X'` is arranged before affineness of the chart of `X`.

**Why the conclusion is about sieves and not about `CoversTop`.**  Being good for `g` is not
inherited by a further étale chart over a good chart — an étale scheme over an affine scheme need
not be affine — so the good charts do not form a sieve, and the family of all of them does not
satisfy `CategoryTheory.GrothendieckTopology.CoversTop` in a form that would give goodness of the
source of each arrow of the covering sieve.  What is true, and what consumers need, is the
statement proved here: a sieve that contains the morphisms out of good charts is covering, which
applies in particular to `CategoryTheory.Presheaf.imageSieve` of a morphism of modules that is
surjective on the sections over every affine chart diagram.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-- **An étale chart of `X` carrying an affine chart diagram over `g`.**  An étale scheme chart
`W` of `X` has this property when its underlying scheme is affine and there is an étale scheme
chart `V` of `X'` with affine underlying scheme and a morphism `q : W ⟶ V` of the big fppf site
over `S` making the square with `g` and the two structure morphisms commute.

Such a `W` is precisely the chart of `X` of a commutative diagram of étale scheme charts over
`g` — an `AlgebraicGeometry.Space.ChartDiagram` of [Stacks Project, Tag 03G3] — whose two charts
are affine: the diagram is `⟨W, V, q, _⟩`. -/
def HasAffineChartDiagram (g : X ⟶ X') (W : SmallEtale B S hS X.1) : Prop :=
  IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧
    ∃ (V : SmallEtale B S hS X'.1) (q : W.1.left ⟶ V.1.left),
      yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)

/-- **Every point of a chart of `X` lifts to a chart carrying an affine chart diagram over
`g`.**  For an étale scheme chart `U` of `X` and a point `z` of its underlying scheme there is
an étale scheme chart `W` of `X` with a morphism `a : W ⟶ U`, a point of `W` above `z`, and an
affine chart diagram over `g` with `W` as its chart of `X`.

The three stages of the construction are described in the implementation notes of this file. -/
theorem exists_hasAffineChartDiagram (g : X ⟶ X') (U : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U), HasAffineChartDiagram B S hS g W ∧
      ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) z' = z := by
  obtain ⟨A₀, g₀, hg₀S, hg₀E⟩ := X'.2.exists_atlas
  obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ :=
    exists_chart_over B S hS g U ⟨CostructuredArrow.mk g₀, hg₀E⟩ hg₀S z
  obtain ⟨U'', ι', hU''aff, y'', hy''⟩ := exists_affine_chart_at B S hS X'.1
    (⟨CostructuredArrow.mk g₀, hg₀E⟩ : SmallEtale B S hS X'.1)
    (((BigFppfOver.toScheme B S hS).map q₁) z₁)
  obtain ⟨T₂, π₂, p₂, hp₂, -, w₂, hw₂, -⟩ :=
    exists_chart_pullback B S hS g V₁ q₁ hq₁ ι' z₁ y'' hy''.symm
  obtain ⟨T₃, π₃, hT₃aff, w₃, hw₃⟩ := exists_affine_chart_at B S hS X.1 T₂ w₂
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁,
    ⟨hT₃aff, U'', (SmallEtale.toOver B S hS X.1).map π₃ ≫ p₂, ?_, hU''aff⟩, w₃, ?_⟩
  · rw [Functor.map_comp, Category.assoc, hp₂, ← Category.assoc]
    exact congrArg (fun φ => φ ≫ g.hom) (CostructuredArrow.w (π₃.hom))
  · rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply,
      Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw₃, hw₂, hz₁]

/-- **The charts of `X` carrying an affine chart diagram over `g` are cover-dense.**  A sieve of
an étale scheme chart `U` of `X` which contains every morphism to `U` whose source carries an
affine chart diagram over `g` is a covering sieve of the small étale site of `X`.

A covering sieve of the small étale site is one whose arrows are jointly surjective on the
scheme points of the chart (`AlgebraicGeometry.Space.smallEtale_sieve_of_pointwise_covering`),
and `AlgebraicGeometry.Space.exists_hasAffineChartDiagram` supplies, above each point, an arrow
of the sieve. -/
theorem mem_topology_of_hasAffineChartDiagram (g : X ⟶ X') (U : SmallEtale B S hS X.1)
    (R : Sieve U)
    (hR : ∀ ⦃W : SmallEtale B S hS X.1⦄ (a : W ⟶ U),
      HasAffineChartDiagram B S hS g W → R a) :
    R ∈ SmallEtale.topology B S hS X.1 U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 U R fun z => ?_
  obtain ⟨W, a, hW, z', hz'⟩ := exists_hasAffineChartDiagram B S hS g U z
  exact ⟨W, a, hR a hW, z', hz'⟩

end AlgebraicGeometry.Space

end
