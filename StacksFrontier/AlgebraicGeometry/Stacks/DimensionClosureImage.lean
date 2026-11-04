module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericDominantDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionJacobsonPseudoCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.IrreducibleSchemeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSubstackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageDominant
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackIntersection

/-!
# The dimension of a 1-morphism relative to the closure of the image of its points

Let `f : 𝒯 ⟶ 𝒳` be a 1-morphism locally of finite type of Jacobson, pseudo-catenary, locally
Noetherian algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳` quasi-separated. Those are
exactly the hypotheses **Stacks 0DS4** lists; the registration of that tag in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionSchemeTheoreticImage.lean` adds
quasi-compactness of `f`, which the source's statement omits and its conclusion needs. This file
proves the same dimension formula asking
quasi-compactness only of the restriction of `f` to a nonempty open substack `𝒰` of `𝒯`, with
`𝒵` read as the closure of the image of `|f|` rather than as the scheme theoretic image of `f`:

`dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every `t ∈ |𝒯|`, with equality on a nonempty — hence
dense — open subset of `|𝒯|`.

Every declaration named in this docstring lives in the namespace `AlgebraicGeometry.Stack`.

This is the shape the source's own proof produces before its normalisation step: shrinking `𝒯` to
a quasi-compact open substack leaves the closure of the image of `|f|` unchanged, and replaces
the scheme theoretic image of `f` by the scheme theoretic image of the restriction. For a
quasi-compact `f` one may take `𝒰 = 𝒯`, and then the two readings of `𝒵` coincide by
**Stacks 0CML**, so the statement specializes to Stacks 0DS4 itself, as proved in
`DimensionSchemeTheoreticImage.lean`.

`𝒵` is presented as a closed substack of `𝒳` whose point set is the closure of the image of
`|f|`, since the dimension of **Stacks 0AFP** is defined for an algebraic stack and not for a
subset of `|𝒳|`. The closed substack used is the scheme theoretic image of the restriction,
which is what makes its point set computable: **Stacks 0CML** applies to the restriction.

## Main results

* `irreducibleSpace_points_of_isOpenImmersion`: a nonempty open substack
  of a stack with irreducible point space has irreducible point space.
* `range_pointsMap_eq_closure_range_pointsMap_of_isOpenImmersion`: for a
  nonempty open substack `𝒰` of the irreducible `𝒯`, the points of the scheme theoretic image of
  the restriction `𝒰 ⟶ 𝒳` are the closure of the image of `|f|` itself.
* `exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt_of_quasiCompactRestriction`
  and
  `dimension_le_add_relativeStackDimensionAt_of_quasiCompactRestriction`:
  the generic equality and the inequality, for `𝒵` the scheme theoretic image of a quasi-compact
  restriction of `f`.
* `exists_closedSubstack_range_pointsMap_eq_closure_dimension_le_add_and_exists_isOpen_dense_eq`:
  the three together — a closed substack of `𝒳` supported on the closure of the image of `|f|`
  for which both clauses of Stacks 0DS4 hold.
* `dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_quasiCompactRestriction`:
  the inequality clause for `𝒵` the scheme theoretic image of `f` itself, still asking
  quasi-compactness only of a restriction. The restriction's image is taken inside `𝒵`, so the
  last step is Stacks 0DRY at the inclusion of a closed substack rather than a comparison of two
  nested closed substacks of `𝒳`; the quasi-compact open substack is the only input it needs
  beyond the hypotheses Stacks 0DS4 lists.

## Implementation notes

Everything rests on two localities of the dimension along an open immersion `j : 𝒰 ⟶ 𝒯`, which
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionOpenImmersion.lean` supplies:
`dimensionAtPoint_eq_of_isOpenImmersion` and
`relativeStackDimensionAt_comp_eq_of_isOpenImmersion`. Together with the
constancy of **Stacks 0DRX** on `𝒰` and on `𝒯`
(`isConstant_dimensionAtPoint_of_irreducibleSpace`) they turn the
conclusion of Stacks 0DS4 for `j ≫ f` into the conclusion for `f`: `dim(𝒰) = dim(𝒯)`, and the
relative dimension of `j ≫ f` at `u` is that of `f` at `j(u)`.

That `|𝒰|` is irreducible is the only topology: `|j|` is an open embedding on points, by
**Stacks 0H20** for an open immersion together with the embedding of an immersion, and a nonempty
open subspace of an irreducible space is irreducible.

That the point set of the scheme theoretic image of `j ≫ f` is the closure of the image of `|f|`
is **Stacks 0CML** for the quasi-compact `j ≫ f` together with the density of the image of `|j|`:
that image is a nonempty open subset of the irreducible `|𝒯|`, hence dense, so `|f|` carries it
to a subset whose closure contains the image of `|f|` — a continuous map sends the closure of a
set into the closure of its image — and the two closures therefore agree.

The inequality clause is deduced from the generic equality on `𝒯` itself, by
`dimension_le_add_relativeStackDimensionAt_of_exists_isOpen`, rather than
transported from `𝒰`: the restriction says nothing at the points of `|𝒯|` outside `|𝒰|`, while
that deduction — the upper semi-continuity of **Stacks 0DRQ** (1) on the irreducible `|𝒯|` —
reaches every point.

The quasi-compact nonempty open substack `𝒰` is data of the statements. The library builds no
such substack yet: `StacksFrontier/AlgebraicGeometry/Stacks/OpenSubstackPoints.lean` has the rule
`𝒰 ↦ |𝒰|` of **Stacks 06FJ** and its monotonicity, and records that the inverse rule — an open
substack for each open subset of `|𝒳|` — rests on a form of **Stacks 0507** that is absent, so
the quasi-compact open of the source's own first step has to be given.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 05UP](https://stacks.math.columbia.edu/tag/05UP)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 0CPU](https://stacks.math.columbia.edu/tag/0CPU)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
* [Stacks Project, Tag 0DRY](https://stacks.math.columbia.edu/tag/0DRY)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A nonempty open substack of a stack with irreducible point space has irreducible point
space.** The point map of an open immersion is an open embedding — it is an embedding because an
open immersion is an immersion, and open by **Stacks 0H20** — and a nonempty open subspace of an
irreducible space is irreducible: two nonempty open subsets of `|𝒰|` have nonempty open images in
`|𝒯|`, which meet, and the point of the intersection has one preimage, lying in both. -/
theorem irreducibleSpace_points_of_isOpenImmersion
    {𝒰 𝒯 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒰Nonempty : Nonempty (points B S hS 𝒰.val.val 𝒰.val.property)) :
    @IrreducibleSpace _ (pointTopology B S hS 𝒰.val) := by
  let := pointTopology B S hS 𝒰.val
  let := pointTopology B S hS 𝒯.val
  have := h𝒯Irreducible
  have hemb := AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS j
    (AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS j hj)
  have hopen := AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS j hj
  refine (irreducibleSpace_def _).2 ⟨?_, fun U V hU hV hUne hVne => ?_⟩
  · obtain ⟨u⟩ := h𝒰Nonempty
    exact ⟨u, trivial⟩
  · obtain ⟨a, -, haU⟩ := hUne
    obtain ⟨b, -, hbV⟩ := hVne
    obtain ⟨y, -, hyU, hyV⟩ := (IrreducibleSpace.isIrreducible_univ
        (points B S hS 𝒯.val.val 𝒯.val.property)).2
      (AlgebraicStacks.pointsMap B S hS j '' U) (AlgebraicStacks.pointsMap B S hS j '' V)
      (hopen U hU) (hopen V hV) ⟨_, trivial, a, haU, rfl⟩ ⟨_, trivial, b, hbV, rfl⟩
    obtain ⟨p, hpU, hpy⟩ := hyU
    obtain ⟨q, hqV, hqy⟩ := hyV
    exact ⟨p, trivial, hpU, hemb.injective (hpy.trans hqy.symm) ▸ hqV⟩

/-- **The points of the scheme theoretic image of a quasi-compact restriction of `f` to a
nonempty open substack are the closure of the image of `|f|`.** Let `j : 𝒰 ⟶ 𝒯` be an open
immersion with `|𝒰|` nonempty, let `|𝒯|` be irreducible, let `j ≫ f` be quasi-compact and let `P`
cut out the scheme theoretic image of `j ≫ f`. Then the points of that closed substack are the
closure in `|𝒳|` of the image of `|f|`.

By **Stacks 0CML** they are the closure of the image of `|j ≫ f|`, which is `|f|` of the image of
`|j|`. The image of `|j|` is a nonempty open subset of the irreducible `|𝒯|`, hence dense, and a
continuous map sends the closure of a set into the closure of its image, so the closure of `|f|`
of the image of `|j|` contains the whole image of `|f|`; the reverse containment is monotonicity
of the closure. -/
theorem range_pointsMap_eq_closure_range_pointsMap_of_isOpenImmersion
    {𝒰 𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯) (f : 𝒯 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒰Nonempty : Nonempty (points B S hS 𝒰.val.val 𝒰.val.property))
    (hjfQC : IsQuasiCompactMorphism B S hS (j ≫ f))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage (j ≫ f) P) :
    Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack)) =
      @closure _ (pointTopology B S hS 𝒳.val)
        (Set.range (AlgebraicStacks.pointsMap B S hS f)) := by
  let := pointTopology B S hS 𝒰.val
  let := pointTopology B S hS 𝒯.val
  let := pointTopology B S hS 𝒳.val
  have := h𝒯Irreducible
  have hfcont : Continuous (AlgebraicStacks.pointsMap B S hS f) :=
    continuous_pointsMap B S hS 𝒯.val 𝒳.val f.hom.hom
  have hjdense : Dense (Set.range (AlgebraicStacks.pointsMap B S hS j)) := by
    obtain ⟨u⟩ := h𝒰Nonempty
    exact dense_of_isOpen_of_nonempty_points B S hS 𝒯 h𝒯Irreducible
      (AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS j hj).isOpen_range ⟨_, u, rfl⟩
  have hcomp : Set.range (AlgebraicStacks.pointsMap B S hS (j ≫ f)) =
      AlgebraicStacks.pointsMap B S hS f '' Set.range (AlgebraicStacks.pointsMap B S hS j) := by
    rw [AlgebraicStacks.pointsMap_comp B S hS j f, Set.range_comp]
  rw [range_pointsMap_eq_closure_of_isSchemeTheoreticImage B S hS (j ≫ f) hjfQC hP, hcomp]
  refine le_antisymm (closure_mono (Set.image_subset_range _ _))
    (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨t, rfl⟩
  refine image_closure_subset_closure_image hfcont ⟨t, ?_, rfl⟩
  rw [hjdense.closure_eq]
  trivial

/-- The dimension of a Jacobson pseudo-catenary locally Noetherian stack with irreducible point
space is its dimension at any point. -/
private theorem dimension_eq_dimensionAtPoint_of_irreducibleSpace
    (𝒲 : AlgebraicStacks.{u, w} B S hS) (h𝒲 : IsLocallyNoetherianStack.{u, w} B S hS 𝒲)
    (h𝒲Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒲)
    (h𝒲Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒲)
    (h𝒲Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒲.val))
    (x : points B S hS 𝒲.val.val 𝒲.val.property) :
    dimension B S hS 𝒲 h𝒲 = dimensionAtPoint B S hS 𝒲 h𝒲 x :=
  dimension_eq_dimensionAtPoint_of_isConstant B S hS 𝒲 h𝒲
    (isConstant_dimensionAtPoint_of_irreducibleSpace.{u, w} B S hS 𝒲 h𝒲 h𝒲Jacobson h𝒲Catenary
      h𝒲Irreducible) x

/-- **The generic equality of Stacks 0DS4 against a quasi-compact restriction of `f`.** Let
`f : 𝒯 ⟶ 𝒳` satisfy the hypotheses of Stacks 0DS4, let `j : 𝒰 ⟶ 𝒯` be an open immersion with
`|𝒰|` nonempty and `j ≫ f` quasi-compact, and let `P` cut out the scheme theoretic image `𝒵` of
`j ≫ f`. Then `dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` on a nonempty, equivalently dense, open subset
of `|𝒯|`. Quasi-compactness is asked of `j ≫ f` and not of `f`.

Stacks 0DS4 for the quasi-compact `j ≫ f` gives a nonempty open subset of `|𝒰|` on which
`dim(𝒰) = dim(𝒵) + dim_u(𝒰_{(j ≫ f)(u)})`. Its image under the open map `|j|` is a nonempty open
subset of `|𝒯|`, and over it the two sides are the two sides for `f`: `dim(𝒰) = dim(𝒯)` because
the dimension of Stacks 0AFN is local on open substacks and is constant on each of `|𝒰|` and
`|𝒯|` by Stacks 0DRX, and the relative dimension of `j ≫ f` at `u` is that of `f` at `j(u)`. -/
theorem exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt_of_quasiCompactRestriction
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒰Nonempty : Nonempty (points B S hS 𝒰.val.val 𝒰.val.property))
    (hjfQC : IsQuasiCompactMorphism B S hS (j ≫ f))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage (j ≫ f) P) :
    ∃ W : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) W ∧ W.Nonempty ∧
        @Dense _ (pointTopology B S hS 𝒯.val) W ∧
        ∀ t ∈ W, dimension B S hS 𝒯 h𝒯 =
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
            relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  let := pointTopology B S hS 𝒰.val
  let := pointTopology B S hS 𝒯.val
  have himm : AlgebraicStacks.IsImmersion B S hS j :=
    AlgebraicStacks.isImmersion_of_isOpenImmersion B S hS j hj
  have hjft : AlgebraicStacks.IsLocallyOfFiniteType B S hS j :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isImmersion B S hS j himm
  have hjf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (j ≫ f) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS j f hjft hf
  have h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰 :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS j hjft h𝒯
  have h𝒰Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒰 :=
    AlgebraicStacks.isJacobson_of_isImmersion B S hS j himm h𝒯Jacobson
  have h𝒰Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒰 :=
    AlgebraicStacks.isPseudoCatenary_of_isImmersion B S hS j himm h𝒯Catenary
  have h𝒰Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒰.val) :=
    irreducibleSpace_points_of_isOpenImmersion B S hS j hj h𝒯Irreducible h𝒰Nonempty
  obtain ⟨W, hWopen, hWne, hWeq⟩ :=
    exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism.{u, w}
      B S hS (j ≫ f) hjf hjfQC h𝒰 h𝒳 h𝒰Jacobson h𝒳Jacobson h𝒰Catenary h𝒳Catenary
      h𝒰Irreducible h𝒳QuasiSeparated hP
  have hopen := AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS j hj
  refine ⟨AlgebraicStacks.pointsMap B S hS j '' W, hopen W hWopen, hWne.image _,
    dense_of_isOpen_of_nonempty_points B S hS 𝒯 h𝒯Irreducible (hopen W hWopen)
      (hWne.image _), ?_⟩
  rintro _ ⟨u, huW, rfl⟩
  have hdim : dimension B S hS 𝒯 h𝒯 = dimension B S hS 𝒰 h𝒰 := by
    rw [dimension_eq_dimensionAtPoint_of_irreducibleSpace B S hS 𝒰 h𝒰 h𝒰Jacobson h𝒰Catenary
        h𝒰Irreducible u,
      dimensionAtPoint_eq_of_isOpenImmersion B S hS j hj h𝒰 h𝒯 u]
    exact dimension_eq_dimensionAtPoint_of_irreducibleSpace B S hS 𝒯 h𝒯 h𝒯Jacobson h𝒯Catenary
      h𝒯Irreducible _
  rw [hdim, hWeq u huW,
    relativeStackDimensionAt_comp_eq_of_isOpenImmersion.{u, w} B S hS j f hj hf hjf h𝒰 h𝒯 h𝒳 u]

/-- **The inequality of Stacks 0DS4 against a quasi-compact restriction of `f`.** In the setting
of
`exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt_of_quasiCompactRestriction`,
`dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at *every* `t ∈ |𝒯|`.

The generic equality implies it on `𝒯` itself, by
`dimension_le_add_relativeStackDimensionAt_of_exists_isOpen` — the upper
semi-continuity of Stacks 0DRQ (1) together with the constancy of Stacks 0DRX — so the points of
`|𝒯|` outside the open substack are reached as well. -/
theorem dimension_le_add_relativeStackDimensionAt_of_quasiCompactRestriction
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒰Nonempty : Nonempty (points B S hS 𝒰.val.val 𝒰.val.property))
    (hjfQC : IsQuasiCompactMorphism B S hS (j ≫ f))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage (j ≫ f) P)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    dimension B S hS 𝒯 h𝒯 ≤
      closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
        relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  obtain ⟨W, hWopen, hWne, -, hWeq⟩ :=
    exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt_of_quasiCompactRestriction.{u, w}
      B S hS f hf h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated j hj h𝒰Nonempty hjfQC hP
  refine dimension_le_add_relativeStackDimensionAt_of_exists_isOpen.{u, w} B S hS f hf h𝒯 h𝒳
    h𝒯Jacobson h𝒯Catenary h𝒯Irreducible _ ⟨W, hWopen, hWne, fun y hy => ?_⟩ t
  rw [← hWeq y hy]
  exact (dimension_eq_dimensionAtPoint_of_irreducibleSpace B S hS 𝒯 h𝒯 h𝒯Jacobson h𝒯Catenary
    h𝒯Irreducible y).symm

/-- **The dimension formula of Stacks 0DS4 with `𝒵` the closure of the image of `|f|`.** Let
`f : 𝒯 ⟶ 𝒳` be locally of finite type between Jacobson,
pseudo-catenary, locally Noetherian algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳`
quasi-separated, and let `j : 𝒰 ⟶ 𝒯` be an open immersion with `|𝒰|` nonempty along which `f`
becomes quasi-compact. Then there is a closed substack `𝒵` of `𝒳` whose points are the closure
of the image of `|f|` and for which `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every `t ∈ |𝒯|`, with
equality on a nonempty, equivalently dense, open subset of `|𝒯|`.

Quasi-compactness is asked only of `j ≫ f`, not of `f`. For a quasi-compact `f` one may take
`j = 𝟙 𝒯`, and the substack produced is then the scheme theoretic image of `f` itself by
**Stacks 0CML**, so the statement specializes to Stacks 0DS4 as proved in
`DimensionSchemeTheoreticImage.lean`.
In general the scheme theoretic image of `f` can be strictly larger than the closure of the image
of `|f|`, and it is the closure that the formula here is about.

`𝒵` is the scheme theoretic image of `j ≫ f`; its point set is computed by
`range_pointsMap_eq_closure_range_pointsMap_of_isOpenImmersion`, and the
two clauses are
`dimension_le_add_relativeStackDimensionAt_of_quasiCompactRestriction` and
`exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt_of_quasiCompactRestriction`.

The `@[stacks 0DS4]` attribute sits on the statement of the tag itself, in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionSchemeTheoreticImage.lean`, where `𝒵` is
the scheme theoretic image of `f` as Stacks 0CMI defines it and `f` is quasi-compact. -/
theorem exists_closedSubstack_range_pointsMap_eq_closure_dimension_le_add_and_exists_isOpen_dense_eq
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒰Nonempty : Nonempty (points B S hS 𝒰.val.val 𝒰.val.property))
    (hjfQC : IsQuasiCompactMorphism B S hS (j ≫ f))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage (j ≫ f) P) :
    Set.range (AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack)) =
        @closure _ (pointTopology B S hS 𝒳.val)
          (Set.range (AlgebraicStacks.pointsMap B S hS f)) ∧
      (∀ t : points B S hS 𝒯.val.val 𝒯.val.property,
          dimension B S hS 𝒯 h𝒯 ≤
            closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
              relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t) ∧
        ∃ W : Set (points B S hS 𝒯.val.val 𝒯.val.property),
          @IsOpen _ (pointTopology B S hS 𝒯.val) W ∧ W.Nonempty ∧
            @Dense _ (pointTopology B S hS 𝒯.val) W ∧
            ∀ t ∈ W, dimension B S hS 𝒯 h𝒯 =
              closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
                relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t :=
  ⟨range_pointsMap_eq_closure_range_pointsMap_of_isOpenImmersion B S hS j f hj h𝒯Irreducible
      h𝒰Nonempty hjfQC hP,
    fun t => dimension_le_add_relativeStackDimensionAt_of_quasiCompactRestriction.{u, w} B S hS f
      hf h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible h𝒳QuasiSeparated j hj
      h𝒰Nonempty hjfQC hP t,
    exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt_of_quasiCompactRestriction.{u, w}
      B S hS f hf h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated j hj h𝒰Nonempty hjfQC hP⟩

/-- **The inequality clause of Stacks 0DS4 for the scheme theoretic image of `f` itself, asking
quasi-compactness only of a restriction.** Let `f : 𝒯 ⟶ 𝒳` satisfy the hypotheses of
Stacks 0DS4, let `j : 𝒰 ⟶ 𝒯` be an open immersion with `|𝒰|` nonempty along which `f` becomes
quasi-compact, and let `P` cut out the scheme theoretic image `𝒵` of `f`. Then
`dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at *every* `t ∈ |𝒯|`, with `𝒵` as Stacks 0CMI defines it
for `f` and nothing asked of `f` beyond local finite type.

This is
`AlgebraicGeometry.Stack.dimension_le_add_relativeStackDimensionAt_of_quasiCompactRestriction`
read for the factorization `g : 𝒯 ⟶ 𝒵` in place of `f`, so that the image of the restriction
`j ≫ g` is a closed substack **of `𝒵`** rather than of `𝒳`. That is what makes the last step
cheap: bounding its dimension by `dim(𝒵)` is Stacks 0DRY at the inclusion of a closed substack,
`AlgebraicGeometry.Stack.dimension_le_of_isClosedImmersion`, rather than a comparison of two
nested closed substacks of `𝒳`, for which this library has no closed immersion. That image
exists by **Stacks 0CPU**, `AlgebraicGeometry.Stack.hasSchemeTheoreticImage`, so it is not data.
The relative dimension of `g` is that of `f` by
`AlgebraicGeometry.Stack.relativeStackDimensionAt_substackFactorizationHom`; `𝒵` inherits the
Jacobson, pseudo-catenary and quasi-separated hypotheses from `𝒳`, its inclusion being an
immersion and a monomorphism, the last through part (8) of **Stacks 050L**; and `j ≫ g` is
quasi-compact because `j ≫ f` is and the inclusion of `𝒵` is a quasi-separated monomorphism
(**Stacks 050Y**).

A nonempty quasi-compact open substack `𝒰` with `j ≫ f` quasi-compact exists for every `f`,
by **Stacks 05UP** and **Stacks 075S**, part (1); this is how
`AlgebraicGeometry.Stack.forall_dimension_le_closedSubstackDimension_add_relativeStackDimensionAt`
obtains the inequality clause of Stacks 0DS4 with no hypothesis on `f` beyond local finite
type. -/
theorem dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_quasiCompactRestriction
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒰Nonempty : Nonempty (points B S hS 𝒰.val.val 𝒰.val.property))
    (hjfQC : IsQuasiCompactMorphism B S hS (j ≫ f))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    dimension B S hS 𝒯 h𝒯 ≤
      closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
        relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  obtain ⟨P', hP'⟩ :=
    hasSchemeTheoreticImage (j ≫ factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1)
  have hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1) :=
    isLocallyOfFiniteType_substackFactorizationHom.{u, w} B S hS f hf hP.isAlgebraicStack hP.2.1
  have h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack) :=
    isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳
  have himm : AlgebraicStacks.IsImmersion B S hS
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack) :=
    AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS _ hP.1.2.choose_spec
  have hmono : AlgebraicStacks.IsMonomorphism B S hS
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack) :=
    AlgebraicStacks.isMonomorphism_of_isImmersion B S hS _ himm
  have h𝒵QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack) :=
    isQuasiSeparatedAbs_of_isQuasiSeparated B S hS _ h𝒳QuasiSeparated
      (AlgebraicStacks.isQuasiSeparated_changeBase B S _ hS (contains_specULiftZ B)
        (toIntObject B S hS) _
        (AlgebraicStacks.isQuasiSeparated_of_isMonomorphism B S hS _ hmono))
  have hjgQC : IsQuasiCompactMorphism B S hS
      (j ≫ factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1) := by
    refine isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS _
      (fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack) ?_
      (AlgebraicStacks.isQuasiSeparated_of_isMonomorphism B S hS _ hmono)
    refine isQuasiCompactMorphism_of_comp_of_isSurjective B S hS (𝟙 𝒰) (j ≫ f) _ ?_
      (isSurjective_id.{u, w} B S hS 𝒰) hjfQC
    exact (@eqToIso _ (Bicategory.homCategory _ _) _ _
        (show 𝟙 𝒰 ≫ (j ≫ factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1) ≫
              fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack =
            j ≫ factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1 ≫
              fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack by
          rw [Category.id_comp, Category.assoc])).trans
      (Bicategory.whiskerLeftIso j (factorsThroughSubstackIso f hP.isAlgebraicStack hP.2.1))
  refine (dimension_le_add_relativeStackDimensionAt_of_quasiCompactRestriction.{u, w} B S hS
    (factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1) hg h𝒯 h𝒵 h𝒯Jacobson
    (AlgebraicStacks.isJacobson_of_isImmersion B S hS _ himm h𝒳Jacobson) h𝒯Catenary
    (AlgebraicStacks.isPseudoCatenary_of_isImmersion B S hS _ himm h𝒳Catenary) h𝒯Irreducible
    h𝒵QuasiSeparated j hj h𝒰Nonempty hjgQC hP' t).trans ?_
  rw [relativeStackDimensionAt_substackFactorizationHom.{u, w} B S hS f hf hP.isAlgebraicStack
    hP.2.1 hmono h𝒯 h𝒵 h𝒳]
  exact add_le_add (dimension_le_of_isClosedImmersion B S hS
    (fullSubcategoryInclusion _ P' hP'.isAlgebraicStack) hP'.1.2.choose_spec _ h𝒵) le_rfl

end AlgebraicGeometry.Stack

end
