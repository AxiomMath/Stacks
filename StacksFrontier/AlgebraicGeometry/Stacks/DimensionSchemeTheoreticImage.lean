module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericDominantDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Stacks.ConstancyOfStackDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionQuasiDM
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionJacobsonPseudoCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.IrreducibleSchemeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.JacobsonAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenaryAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackLocalConstancy
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDimensionFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImagePointsClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute

/-!
# The dimension of a 1-morphism relative to its scheme theoretic image

Let `f : 𝒯 ⟶ 𝒳` be a 1-morphism locally of finite type of Jacobson, pseudo-catenary, locally
Noetherian algebraic stacks over `S`, with `𝒯` irreducible and `𝒳` quasi-separated, and let
`𝒵 ↪ 𝒳` be the scheme theoretic image of `f` (Stacks 0CMI). **Stacks 0DS4** says that
`dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every `t ∈ |𝒯|` and that equality holds on a nonempty,
hence dense, open subset of `|𝒯|`. **Stacks 0DS6** says, for `f` moreover quasi-DM, that
`dim(𝒵) ≤ dim(𝒯)` and that exactly one of the following two conditions holds: either
`dim_t(𝒯_{f(t)}) > 0` at every finite type point `t ∈ |𝒯|`, in which case `dim(𝒵) < dim(𝒯)`, or
`𝒯` and `𝒵` have the same dimension.

## Main definitions

* `AlgebraicGeometry.Stack.closedSubstackDimension` is the dimension of Stacks 0AFP of the closed
  substack cut out by a property of the objects of a locally Noetherian algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_of_isClosedImmersion`: a closed immersion
  of algebraic stacks is an immersion.
* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_of_isClosedSubstack`: a closed substack of a
  locally Noetherian algebraic stack is locally Noetherian, so it has a dimension.
* `AlgebraicGeometry.Stack.dimension_eq_dimensionAtPoint_of_isConstant`: a stack whose dimension
  at a point does not depend on the point has that value as its dimension.
* `AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension` and
  `AlgebraicGeometry.Stack.xor_relativeDimension_pos_and_lt_dimension_eq`: the order-theoretic
  steps of the two conclusions of **Stacks 0DS6**, from the two conclusions of Stacks 0DS4 and the
  non-negativity of Stacks 0DS5 as inputs.
* `exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism` and
  `dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_isQuasiCompactMorphism`:
  the content of **Stacks 0DS4** for a quasi-compact `f`.
* `AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism`:
  **Stacks 0DS6**, the inequality `dim(𝒵) ≤ dim(𝒯)`, under the hypotheses of the source.
* `closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos_of_ne_top`:
  **Stacks 0DS6**, the exactly-one clause, for `dim(𝒯)` finite (erratum: false as written when
  `dim(𝒯) = dim(𝒵) = ∞`, by
  `AlgebraicGeometry.Stack.not_forall_xor_relativeDimension_pos`).
* `AlgebraicGeometry.Stack.dimension_le_closedSubstackDimension_add_relativeStackDimensionAt` and
  `AlgebraicGeometry.Stack.exists_isOpen_dimension_eq_add_relativeStackDimensionAt`:
  **Stacks 0DS4**, the inequality and the generic equality.

## Implementation notes

What Stacks 0DS4 contributes to the two statements of Stacks 0DS6 is the passage from the
dimension `dim(𝒯)` of Stacks 0AFP to the dimension `dim_t(𝒯)` of Stacks 0AFN at a point: on an
irreducible stack the latter does not depend on the point, by Stacks 0DRX, and so the supremum
defining the former is attained at every point. That passage is
`AlgebraicGeometry.Stack.dimension_eq_dimensionAtPoint_of_isConstant`, and it is all that the two
statements of Stacks 0DS4 below prove: the constancy of Stacks 0DRX and the form that the
inequality and the generic equality take at the points of `𝒯` are their hypotheses. The
pointwise form is what the source's own argument produces, by comparing a smooth chart of `f`
with a smooth chart of a scheme theoretically dominant open of `𝒳` and reducing to the statement
for a dominant morphism of irreducible locally Noetherian schemes; none of that reduction is
available.

The statements of Stacks 0DS6 are earlier than those of Stacks 0DS4 and keep their own
hypotheses. There the relative dimension of Stacks 0DRL is an abstract function `|𝒯| → EInt`, and
the two conclusions of Stacks 0DS4 and the non-negativity of Stacks 0DS5 (which rests on
Stacks 0AFM) are hypotheses on it, named for the tag that supplies each; the conclusions are
those of Stacks 0DS6 itself, unweakened. The hypothesis of generic equality is used only through
the existence of a single point at which the equality of Stacks 0DS4 holds, and is stated in that
weaker form. The statements of Stacks 0DS4 instead use the relative dimension
`AlgebraicGeometry.Stack.relativeStackDimensionAt` of Stacks 0DRL itself.

All the geometric hypotheses of Stacks 0DS6 and of Stacks 0DS4 are carried, the Jacobson
condition on each of `𝒯` and `𝒳` as
`AlgebraicGeometry.Stack.AlgebraicStacks.IsJacobson` and quasi-separatedness of `𝒳` as
`AlgebraicGeometry.Stack.IsQuasiSeparatedAbs`. They are unused for the same reason that
Stacks 0DS4 and Stacks 0DS5 are hypotheses rather than citations: what the conclusions need of
them has been isolated into the pointwise hypotheses. Stacks 0DS4 as printed asks nothing of `f`
beyond local finite type, but its proof derives quasi-compactness only of `T → 𝒳` for a
quasi-compact open `T` of a chart, after shrinking `𝒯`, and shrinking changes the scheme theoretic
image. Quasi-separatedness of `𝒳` does not make `f` quasi-compact, and the equality clause of
Stacks 0DS4 is false without it: for the affine line `T` with infinitely many origins, the `n`-th
thickened by `ε` with `ε^(n+1) = xε = 0`, and `f : T → 𝔸¹` given by `t ↦ ε`, the target is affine,
the scheme theoretic image is `𝔸¹` of dimension `1`, `f(|T|)` is a point and every fibre has
dimension `1`. Stacks 0DS6 inherits the error (see the errata ledger). The statements of the first
part of this file take the scheme theoretic image and carry the conclusions of Stacks 0DS4 as
hypotheses, so no quasi-compactness hypothesis appears; the later sections prove those
conclusions for a quasi-compact `f` and assemble the registered forms of Stacks 0DS6.

The scheme theoretic image is a property of the objects of `𝒳` cutting out a closed substack
(Stacks 04YM), so `𝒵` is the full subcategory it selects and the hypothesis that `P` is the image
is `AlgebraicGeometry.Stack.IsSchemeTheoreticImage`. Its local Noetherianity is Stacks 0CPM for
the closed immersion `𝒵 ⟶ 𝒳`, which is what gives `dim(𝒵)` a meaning. The proof that the full
subcategory is an algebraic stack is quantified over rather than chosen; proof irrelevance makes
the resulting algebraic stack independent of it.

Dimensions take values in `EInt`, Mathlib's extended integers `[-∞, ∞]`, as for Stacks 0AFP, and
the subtraction of Stacks 0DS4 is written as an addition because `EInt` has no total subtraction.

## References

* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRU](https://stacks.math.columbia.edu/tag/0DRU)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
* [Stacks Project, Tag 0DS6](https://stacks.math.columbia.edu/tag/0DS6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A closed immersion of algebraic stacks over `S` is an immersion, a closed immersion of
algebraic spaces being one. -/
theorem AlgebraicStacks.isImmersion_of_isClosedImmersion
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i) :
    AlgebraicStacks.IsImmersion B S hS i :=
  ⟨hi.1, fun U y hy F hF he =>
    Space.isImmersion_of_isClosedImmersion B S hS (hi.2 U y hy F hF he)⟩

/-- The inclusion of a closed substack of an algebraic stack is an immersion. -/
private theorem isImmersion_fullSubcategoryInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    AlgebraicStacks.IsImmersion B S hS (fullSubcategoryInclusion 𝒳 P hA) :=
  AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS _ hP.2.choose_spec

/-- **Stacks 0CPM** at a closed substack: the full subcategory cut out by a closed substack of a
locally Noetherian algebraic stack is locally Noetherian, its inclusion being an immersion. -/
theorem isLocallyNoetherianStack_of_isClosedSubstack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) :
    IsLocallyNoetherianStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA) :=
  AlgebraicStacks.isLocallyNoetherian_of_isImmersion B S hS (fullSubcategoryInclusion 𝒳 P hA)
    (isImmersion_fullSubcategoryInclusion B S hS 𝒳 P hP hA) h𝒳

/-- The dimension of Stacks 0AFP of the closed substack of a locally Noetherian algebraic stack
cut out by a property of its objects. -/
noncomputable abbrev closedSubstackDimension (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) : EInt :=
  dimension B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA)
    (isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 P hP hA h𝒳)

/-- The dimension of Stacks 0AFP of a locally Noetherian algebraic stack whose dimension of
Stacks 0AFN is the same at all of its points is that common value, being the supremum over the
points of a constant function on a nonempty index type. -/
theorem dimension_eq_dimensionAtPoint_of_isConstant (𝒲 : AlgebraicStacks.{u, w} B S hS)
    (h𝒲 : IsLocallyNoetherianStack.{u, w} B S hS 𝒲)
    (hconst : ∀ x y : points B S hS 𝒲.val.val 𝒲.val.property,
      dimensionAtPoint B S hS 𝒲 h𝒲 x = dimensionAtPoint B S hS 𝒲 h𝒲 y)
    (x : points B S hS 𝒲.val.val 𝒲.val.property) :
    dimension B S hS 𝒲 h𝒲 = dimensionAtPoint B S hS 𝒲 h𝒲 x :=
  le_antisymm (iSup_le fun y => (hconst y x).le) (le_iSup _ x)

variable (𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒯 ⟶ 𝒳)
  (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
  (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
  (P : ObjectProperty 𝒳.val.val.obj) (hP : IsSchemeTheoreticImage f P)
  (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
  (relativeDimension : points B S hS 𝒯.val.val 𝒯.val.property → EInt)

/-- The order-theoretic step of the inequality `dim(𝒵) ≤ dim(𝒯)` of Stacks 0DS6, for an abstract
function `relativeDimension` on `|𝒯|`: if it is non-negative and
`dim(𝒯) = dim(𝒵) + relativeDimension t` at some `t`, then `dim(𝒵) ≤ dim(𝒯)`. The inequality of
Stacks 0DS6 itself, with both inputs proved, is
`AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism` below,
which carries the registration. -/
theorem closedSubstackDimension_le_dimension
    (_hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (_hDM : AlgebraicStacks.IsQuasiDM B S hS f)
    (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    (hNonneg : ∀ t, 0 ≤ relativeDimension t)
    (hGeneric : ∃ t, dimension B S hS 𝒯 h𝒯 =
      closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 + relativeDimension t) :
    closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 ≤ dimension B S hS 𝒯 h𝒯 := by
  obtain ⟨t, ht⟩ := hGeneric
  exact ht ▸ le_add_of_nonneg_right (hNonneg t)

/-- The order-theoretic step of the exclusive alternative of Stacks 0DS6, for an abstract function
`relativeDimension` on `|𝒯|` that is non-negative, bounds `dim(𝒯) - dim(𝒵)` from above everywhere
and attains it somewhere: exactly one of "`relativeDimension t > 0` at every finite type point and
`dim(𝒵) < dim(𝒯)`" and `dim(𝒯) = dim(𝒵)` holds. Stacks 0DS6 itself, with these inputs proved, is
`closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos_of_ne_top`. -/
theorem xor_relativeDimension_pos_and_lt_dimension_eq
    (_hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (_hDM : AlgebraicStacks.IsQuasiDM B S hS f)
    (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    (hNonneg : ∀ t, 0 ≤ relativeDimension t)
    (hBound : ∀ t, dimension B S hS 𝒯 h𝒯 ≤
      closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 + relativeDimension t)
    (hGeneric : ∃ t, dimension B S hS 𝒯 h𝒯 =
      closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 + relativeDimension t) :
    Xor ((∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t → 0 < relativeDimension t) ∧
        closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 < dimension B S hS 𝒯 h𝒯)
      (dimension B S hS 𝒯 h𝒯 = closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳) := by
  classical
  have hle : closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 ≤ dimension B S hS 𝒯 h𝒯 :=
    closedSubstackDimension_le_dimension B S hS 𝒯 𝒳 f h𝒯 h𝒳 P hP hA relativeDimension
      _hf _hDM _h𝒯Jacobson _h𝒳Jacobson _h𝒯Catenary _h𝒳Catenary _h𝒯Irreducible
      _h𝒳QuasiSeparated hNonneg hGeneric
  by_cases heq : dimension B S hS 𝒯 h𝒯 = closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳
  · exact Or.inr ⟨heq, fun h => absurd heq.symm (ne_of_lt h.2)⟩
  · have hlt : closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 < dimension B S hS 𝒯 h𝒯 :=
      lt_of_le_of_ne hle (Ne.symm heq)
    refine Or.inl ⟨⟨fun t _ => ?_, hlt⟩, heq⟩
    rcases (hNonneg t).lt_or_eq with h0 | h0
    · exact h0
    · exact absurd (hBound t) (by rw [← h0, add_zero]; exact not_le_of_gt hlt)

/-- **Stacks 0DS4**, the inequality `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every `t ∈ |𝒯|` for a
1-morphism `f` locally of finite type from an irreducible Jacobson, pseudo-catenary, locally
Noetherian algebraic stack to a quasi-separated one with the same properties, with scheme
theoretic image `𝒵`.

Since `|𝒯|` is irreducible, Stacks 0DRX makes `dim_t(𝒯)` independent of `t`, so it equals
`dim(𝒯)`; the inequality is then the one holding at `t` itself. -/
theorem dimension_le_closedSubstackDimension_add_relativeStackDimensionAt
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    (h0DRX : ∀ x y : points B S hS 𝒯.val.val 𝒯.val.property,
      dimensionAtPoint B S hS 𝒯 h𝒯 x = dimensionAtPoint B S hS 𝒯 h𝒯 y)
    (hpointwise : ∀ t : points B S hS 𝒯.val.val 𝒯.val.property,
      dimensionAtPoint B S hS 𝒯 h𝒯 t ≤
        closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 +
          relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    dimension B S hS 𝒯 h𝒯 ≤
      closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 +
        relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t := by
  rw [dimension_eq_dimensionAtPoint_of_isConstant B S hS 𝒯 h𝒯 h0DRX t]
  exact hpointwise t

/-- **Stacks 0DS4**, the generic equality: for a 1-morphism `f` locally of finite type from an
irreducible Jacobson, pseudo-catenary, locally Noetherian algebraic stack to a quasi-separated one
with the same properties, with scheme theoretic image `𝒵`, there is a nonempty open subset of
`|𝒯|` on which `dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})`.

Stacks 0DRX turns the equality `dim_t(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` holding on such an open
subset into the same equality for `dim(𝒯)`. -/
theorem exists_isOpen_dimension_eq_add_relativeStackDimensionAt
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (_h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (_h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (_h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (_h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (_h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    (h0DRX : ∀ x y : points B S hS 𝒯.val.val 𝒯.val.property,
      dimensionAtPoint B S hS 𝒯 h𝒯 x = dimensionAtPoint B S hS 𝒯 h𝒯 y)
    (hpointwise : ∃ V : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) V ∧ V.Nonempty ∧
        ∀ t ∈ V, dimensionAtPoint B S hS 𝒯 h𝒯 t =
          closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 +
            relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) :
    ∃ V : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) V ∧ V.Nonempty ∧
        ∀ t ∈ V, dimension B S hS 𝒯 h𝒯 =
          closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 +
            relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t := by
  obtain ⟨V, hVopen, hVne, hVeq⟩ := hpointwise
  refine ⟨V, hVopen, hVne, fun t ht => ?_⟩
  rw [dimension_eq_dimensionAtPoint_of_isConstant B S hS 𝒯 h𝒯 h0DRX t]
  exact hVeq t ht

end AlgebraicGeometry.Stack

/-!
### From generic equality to the two conclusions of Stacks 0DS4

Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact 1-morphism locally of finite type of algebraic stacks over
`S` with `|𝒯|` irreducible, and let `𝒵 ↪ 𝒳` be its scheme theoretic image (Stacks 0CMI). This
file collects the passages that surround the generic dimension equality of **Stacks 0DS4**: the
derivation of its inequality clause from its equality clause, and the irreducibility of `|𝒵|`.

#### Main results

* `AlgebraicGeometry.Stack.le_add_of_exists_isOpen_eq_of_irreducibleSpace`: on an irreducible
  space, a constant that is realized as `D + g` on a nonempty open subset is a lower bound for
  `D + g` everywhere, as soon as the sublevel sets of `g` are open. This is the step by which the
  source deduces the inequality of Stacks 0DS4 at every point from the generic equality, using
  the upper semi-continuity of the fibre dimension of Stacks 0DRQ (1).
* `AlgebraicGeometry.Stack.dimension_le_add_relativeStackDimensionAt_of_exists_isOpen`: that
  step carried out, with both of its inputs supplied: the inequality clause of Stacks 0DS4 at
  every point of `|𝒯|` follows from its generic equality clause alone.
* `AlgebraicGeometry.Stack.irreducibleSpace_points_schemeTheoreticImage`: the points of the
  scheme theoretic image of a quasi-compact 1-morphism out of a stack with irreducible point
  space form an irreducible space.

#### Implementation notes

The first result is stated for an abstract `g : α → EInt` on an abstract irreducible space rather
than for `AlgebraicGeometry.Stack.relativeStackDimensionAt` on `|𝒯|`, because that is all its
proof uses: two nonempty open subsets of an irreducible space meet, and addition on `EInt` is
monotone. Its hypothesis `hg` is exactly the conclusion of
`AlgebraicGeometry.Stack.isOpen_setOf_relativeStackDimensionAt_le`, Stacks 0DRQ (1).

The second result is the first one with its two hypotheses discharged: the openness of the
sublevel sets is Stacks 0DRQ (1),
`AlgebraicGeometry.Stack.isOpen_setOf_relativeStackDimensionAt_le`, and the constant value of
`dim_t(𝒯)` is `dim(𝒯)` by Stacks 0DRX,
`AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducibleSpace`, through
`AlgebraicGeometry.Stack.dimension_eq_dimensionAtPoint_of_isConstant`. The summand `dim(𝒵)` is
left an abstract element of `EInt`, since nothing about the scheme theoretic image is used; at
`AlgebraicGeometry.Stack.closedSubstackDimension` it is the inequality clause of Stacks 0DS4.

The third rests on **Stacks 0CML**,
`AlgebraicGeometry.Stack.range_pointsMap_eq_closure_of_isSchemeTheoreticImage`, which identifies
the points of `𝒵` inside `|𝒳|` with the closure of the image of `|f|`, together with the fact
that the inclusion of a closed substack is a topological embedding on points
(`AlgebraicGeometry.Stack.AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion`). The closure of
the image of an irreducible space under a continuous map is irreducible, and an embedding carries
that irreducibility back to `|𝒵|`.

#### References

* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- On an irreducible space, a value realized as `D + g x` at every point of a nonempty open
subset bounds `D + g` from below everywhere, provided every sublevel set of `g` is open.

The sublevel set at `g x` is an open subset containing `x`, so it meets the given open subset at
some `y`; there `E = D + g y ≤ D + g x`. This is the source's use of the upper semi-continuity of
Stacks 0DRQ (1) in the proof of Stacks 0DS4. -/
theorem le_add_of_exists_isOpen_eq_of_irreducibleSpace {α : Type*} [TopologicalSpace α]
    [IrreducibleSpace α] {g : α → EInt} (hg : ∀ c : EInt, IsOpen {y : α | g y ≤ c})
    {D E : EInt} {V : Set α} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVeq : ∀ y ∈ V, E = D + g y) (x : α) : E ≤ D + g x := by
  obtain ⟨y, hyx, hyV⟩ := (hVopen.dense hVne).inter_open_nonempty {y : α | g y ≤ g x}
    (hg (g x)) ⟨x, show g x ≤ g x from le_rfl⟩
  exact (hVeq y hyV).trans_le (add_le_add_right hyx D)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Stacks 0DRX: the dimension of an irreducible Jacobson pseudo-catenary locally Noetherian
algebraic stack is its dimension at any point. -/
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

/-- **The inequality clause of Stacks 0DS4 follows from its generic equality clause.** Let
`f : 𝒯 ⟶ 𝒳` be locally of finite type between locally Noetherian algebraic stacks over `S` with
`𝒯` Jacobson, pseudo-catenary and irreducible, and let `D : EInt`. If `dim_t(𝒯) = D + dim_t(𝒯_x)`
on some nonempty open subset of `|𝒯|`, then `dim(𝒯) ≤ D + dim_t(𝒯_x)` at *every* `t ∈ |𝒯|`.

The fibre dimension of Stacks 0DRL has open sublevel sets by Stacks 0DRQ (1), and `dim_t(𝒯)` is
the constant `dim(𝒯)` by Stacks 0DRX; so this is
`AlgebraicGeometry.Stack.le_add_of_exists_isOpen_eq_of_irreducibleSpace`. At
`D = AlgebraicGeometry.Stack.closedSubstackDimension` of the scheme theoretic image it is the
inequality of Stacks 0DS4, which is therefore not an independent statement: the generic equality
at the points of `𝒯` carries it. -/
theorem dimension_le_add_relativeStackDimensionAt_of_exists_isOpen
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (D : EInt)
    (hgeneric : ∃ V : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) V ∧ V.Nonempty ∧
        ∀ t ∈ V, dimensionAtPoint B S hS 𝒯 h𝒯 t =
          D + relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    dimension B S hS 𝒯 h𝒯 ≤ D + relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  let := pointTopology B S hS 𝒯.val
  have := h𝒯Irreducible
  obtain ⟨V, hVopen, hVne, hVeq⟩ := hgeneric
  refine le_add_of_exists_isOpen_eq_of_irreducibleSpace
    (g := relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳)
    (isOpen_setOf_relativeStackDimensionAt_le.{u, w} B S hS f hf h𝒯 h𝒳) hVopen hVne
    (fun y hy => ?_) t
  rw [dimension_eq_dimensionAtPoint_of_irreducibleSpace B S hS 𝒯 h𝒯 h𝒯Jacobson h𝒯Catenary
    h𝒯Irreducible y]
  exact hVeq y hy

/-- **The scheme theoretic image of an irreducible stack is irreducible.** For a quasi-compact
1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks over `S` with `|𝒯|` irreducible and `P` cutting out
the scheme theoretic image `𝒵`, the point space `|𝒵|` is irreducible.

By Stacks 0CML the image of `|𝒵|` in `|𝒳|` is the closure of the image of `|f|`, which is
irreducible as the closure of the image of an irreducible space under a continuous map; and the
inclusion of `𝒵` is a closed immersion, hence an immersion, hence a topological embedding on
points, so `|𝒵|` is irreducible as well. -/
theorem irreducibleSpace_points_schemeTheoreticImage
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    @IrreducibleSpace _
      (pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack).val) := by
  let := pointTopology B S hS 𝒯.val
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack).val
  have := h𝒯Irreducible
  set i := fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack with hi
  have hemb := AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS i
    (isImmersion_fullSubcategoryInclusion B S hS 𝒳 P hP.1 hP.isAlgebraicStack)
  have hrange := range_pointsMap_eq_closure_of_isSchemeTheoreticImage B S hS f hfQC hP
  have hirrT : IsIrreducible (Set.univ : Set (points B S hS 𝒯.val.val 𝒯.val.property)) :=
    IrreducibleSpace.isIrreducible_univ _
  have hcont : Continuous (AlgebraicStacks.pointsMap B S hS f) :=
    continuous_pointsMap B S hS 𝒯.val 𝒳.val f.hom.hom
  have himg : IsIrreducible (Set.range (AlgebraicStacks.pointsMap B S hS f)) := by
    simpa using hirrT.image _ hcont.continuousOn
  have hclo : IsIrreducible (Set.range (AlgebraicStacks.pointsMap B S hS i)) := by
    rw [hrange]
    exact himg.closure
  exact hemb.toHomeomorph.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace hclo)

end AlgebraicGeometry.Stack

/-!
### Dominance of the charts of a 1-morphism over its scheme theoretic image

Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact 1-morphism of algebraic stacks over `S` and let `𝒵 ↪ 𝒳` be
its scheme theoretic image (**Stacks 0CMI**). The proof of **Stacks 0DS4** compares `𝒯` with a
smooth chart `𝒱 ⟶ 𝒵` through a chart of the 2-fibre product `𝒯 ×_𝒵 𝒱`, and the dimension
formula it ends on — for a dominant morphism of schemes — needs that chart to be *dominant* over
`𝒱`. This file supplies that dominance, in three steps:

1. the factorization `𝒯 ⟶ 𝒵` has dense image on points, which is **Stacks 0CML** read through the
   topological embedding of the closed immersion `𝒵 ⟶ 𝒳`;
2. hence the first projection of a 2-fibre product `𝒯 ×_𝒵 𝒱` has dense image on `|𝒱|`, as soon
   as `𝒱 ⟶ 𝒵` is open on points — which a smooth chart is;
3. hence, for charts that are algebraic stacks of schemes of the site, the underlying morphism of
   schemes is dominant.

#### Main results

* `AlgebraicGeometry.Stack.dense_range_pointsMap_substackLift`: step 1.
* `AlgebraicGeometry.Stack.dense_range_pointsMap_fst_of_isTwoFibreProduct`: step 2.
* `AlgebraicGeometry.Stack.isDominant_siteMap_of_dense_range`: step 3.

#### Implementation notes

Step 1 is where quasi-compactness of `f` is used, through **Stacks 0CML**
`AlgebraicGeometry.Stack.range_pointsMap_eq_closure_of_isSchemeTheoreticImage`: without it the
points of the scheme theoretic image need not be the closure of the image of `|f|`. The inclusion
of the image is a closed immersion, so it is a closed map and a topological embedding on points
(**Stacks 0H20**); a closed continuous map commutes with closures of images, and an injective one
may then be cancelled.

Step 2 is **Stacks 04XH**, the surjectivity of `|𝒯 ×_𝒵 𝒱| ⟶ |𝒯| ×_{|𝒵|} |𝒱|`: a nonempty open
subset of `|𝒱|` has open nonempty image in `|𝒵|`, which meets the dense image of `|𝒯|`, and a
point of `|𝒯|` and one of the open subset with the same image in `|𝒵|` lift to the 2-fibre
product. Openness of `|𝒱| ⟶ |𝒵|` is all that is asked of the chart; for a smooth one it is
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_of_isSmooth`.

Step 3 is the homeomorphism `AlgebraicGeometry.Stack.pointsHomeomorphScheme` between the points
of `schemeStack U` and the scheme `U`, which carries a 1-morphism to the morphism of the site
underlying it by `AlgebraicGeometry.Stack.pointsHomeomorphScheme_pointsMap`.

#### References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The factorization of a quasi-compact 1-morphism through its scheme theoretic image is
dominant on points.** For `f : 𝒯 ⟶ 𝒳` quasi-compact and `P` cutting out the scheme theoretic
image `𝒵` of Stacks 0CMI, the image of `|𝒯| ⟶ |𝒵|` is dense.

By Stacks 0CML the image of `|𝒵|` in `|𝒳|` is the closure of the image of `|f|`, and `|f|` is the
composite of `|𝒯| ⟶ |𝒵|` with that inclusion. The inclusion is a closed immersion, so it is a
continuous closed map and commutes with closures of images, and it is injective, being a
topological embedding by Stacks 0H20; cancelling it leaves the closure of the image of
`|𝒯| ⟶ |𝒵|` equal to all of `|𝒵|`. -/
theorem dense_range_pointsMap_substackLift
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    @Dense _
      (pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack).val)
      (Set.range (AlgebraicStacks.pointsMap B S hS
        (substackLift B S hS f hP.isAlgebraicStack hP.prop_obj))) := by
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS 𝒯.val
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack).val
  set i := fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack with hi
  set g := substackLift B S hS f hP.isAlgebraicStack hP.prop_obj with hg
  have hci : AlgebraicStacks.IsClosedImmersion B S hS i := hP.1.2.choose_spec
  have hinj : Function.Injective (AlgebraicStacks.pointsMap B S hS i) :=
    (AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS i
      (isImmersion_fullSubcategoryInclusion B S hS 𝒳 P hP.1 hP.isAlgebraicStack)).injective
  have hclosed : IsClosedMap (AlgebraicStacks.pointsMap B S hS i) :=
    AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion B S hS i hci
  have hcont : Continuous (AlgebraicStacks.pointsMap B S hS i) :=
    continuous_pointsMap B S hS _ 𝒳.val i.hom.hom
  have hcomp : AlgebraicStacks.pointsMap B S hS f =
      AlgebraicStacks.pointsMap B S hS i ∘ AlgebraicStacks.pointsMap B S hS g :=
    AlgebraicStacks.pointsMap_comp B S hS g i
  have hrange := range_pointsMap_eq_closure_of_isSchemeTheoreticImage B S hS f hfQC hP
  rw [hcomp, Set.range_comp, hclosed.closure_image_eq_of_continuous hcont,
    ← Set.image_univ] at hrange
  exact dense_iff_closure_eq.2 (Set.image_injective.2 hinj hrange).symm

/-- **A 2-fibre product over a dominant 1-morphism is dominant over an open chart.** Let
`a : 𝒱 ⟶ 𝒵` and `g : 𝒯 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`, let `Q` be a 2-fibre
product of that cospan, let `|a|` be an open map and let the image of `|g|` be dense. Then the
image of the first projection `|Q| ⟶ |𝒱|` is dense.

A nonempty open subset of `|𝒱|` has open nonempty image in `|𝒵|`, which therefore meets the image
of `|g|`; a point of the open subset and a point of `|𝒯|` with the same image in `|𝒵|` lift to
`|Q|` by Stacks 04XH, and the lift maps into the given open subset. -/
theorem dense_range_pointsMap_fst_of_isTwoFibreProduct
    {𝒯 𝒱 𝒵 : AlgebraicStacks.{u, w} B S hS} {a : 𝒱 ⟶ 𝒵} {g : 𝒯 ⟶ 𝒵}
    (Q : Bicategory.TwoCommSq a g) (hQ : Bicategory.IsTwoFibreProduct Q)
    (haopen : @IsOpenMap _ _ (pointTopology B S hS 𝒱.val) (pointTopology B S hS 𝒵.val)
      (AlgebraicStacks.pointsMap B S hS a))
    (hgdense : @Dense _ (pointTopology B S hS 𝒵.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS g))) :
    @Dense _ (pointTopology B S hS 𝒱.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS Q.fst)) := by
  let := pointTopology B S hS 𝒱.val
  let := pointTopology B S hS 𝒵.val
  let := pointTopology B S hS 𝒯.val
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨v₀, hv₀⟩ := hOne
  obtain ⟨z, hzimg, t, hzt⟩ := hgdense.inter_open_nonempty
    (AlgebraicStacks.pointsMap B S hS a '' O) (haopen O hO) ⟨_, v₀, hv₀, rfl⟩
  obtain ⟨v, hvO, hv⟩ := hzimg
  obtain ⟨p, hp₁, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Q hQ v t
    (hv.trans hzt.symm)
  exact ⟨v, hvO, p, hp₁⟩

/-- **A 1-morphism of the algebraic stacks of two schemes of the site with dense image on points
has dominant underlying morphism of schemes.** The points of `schemeStack U` are the points of
`U` by Stacks 04XL, and that identification carries the 1-morphism to the morphism of the site
underlying it, so density of the image transports. -/
theorem isDominant_siteMap_of_dense_range {A V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS A ⟶ schemeStack.{u, w} B S hS V)
    (hc : @Dense _ (pointTopology B S hS (schemeStack.{u, w} B S hS V).val)
      (Set.range (AlgebraicStacks.pointsMap B S hS c))) :
    IsDominant ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) := by
  let := pointTopology B S hS (schemeStack.{u, w} B S hS A).val
  let := pointTopology B S hS (schemeStack.{u, w} B S hS V).val
  refine ⟨?_⟩
  have hfun : (pointsHomeomorphScheme B S hS V) ∘ (AlgebraicStacks.pointsMap B S hS c) =
      ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) ∘
        (pointsHomeomorphScheme B S hS A) :=
    funext fun x => pointsHomeomorphScheme_pointsMap B S hS c x
  have hd : DenseRange
      ((pointsHomeomorphScheme B S hS V) ∘ (AlgebraicStacks.pointsMap B S hS c)) :=
    (pointsHomeomorphScheme B S hS V).surjective.denseRange.comp hc
      (pointsHomeomorphScheme B S hS V).continuous
  rw [hfun, DenseRange, Set.range_comp,
    (pointsHomeomorphScheme B S hS A).surjective.range_eq, Set.image_univ] at hd
  exact hd

end AlgebraicGeometry.Stack

/-!
### The dimension formula for the scheme theoretic image of a quasi-compact 1-morphism

Let `f : 𝒯 ⟶ 𝒳` be a **quasi-compact** 1-morphism locally of finite type of Jacobson,
pseudo-catenary, locally Noetherian algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳`
quasi-separated, and let `𝒵 ↪ 𝒳` be its scheme theoretic image (**Stacks 0CMI**). This file proves
that `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every `t ∈ |𝒯|`, with equality on a nonempty —
equivalently dense — open subset of `|𝒯|`. That is the content of **Stacks 0DS4** with
quasi-compactness of `f` added to its hypotheses.

The route is the source's. Its pointwise form,
`dim_t(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` on a nonempty open subset, is proved first; the inequality
follows from it by
`AlgebraicGeometry.Stack.dimension_le_add_relativeStackDimensionAt_of_exists_isOpen`, and the
passage from `dim_t(𝒯)` to `dim(𝒯)` is
`AlgebraicGeometry.Stack.dimension_eq_dimensionAtPoint_of_isConstant` with the constancy of
**Stacks 0DRX**.

Quasi-compactness of `f` is used in an essential way: it is what makes the points of `𝒵` the
closure of the image of `|f|` (**Stacks 0CML**,
`AlgebraicGeometry.Stack.range_pointsMap_eq_closure_of_isSchemeTheoreticImage`). Without it the
equality fails: for the affine line `T` with infinitely many origins, the `n`-th thickened to
`Spec k[x, ε]/(ε^(n+1), x·ε)`, the global section `ε` defines `f : T ⟶ 𝔸¹` whose scheme theoretic
image is all of `𝔸¹` while every fibre dimension is `1`.

#### Main results

* `AlgebraicGeometry.Stack.pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm`:
  the two names of the point of `|schemeStack U|` belonging to a point of `U` agree.
* `exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism` and
  `dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_isQuasiCompactMorphism`:
  the two clauses of Stacks 0DS4 separately, the first deduced from the generic equality
  `dim_t(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` at the points of a nonempty open subset of `|𝒯|`. Both
  clauses are also stated together with the density of the locus of equality.

#### Implementation notes

The proof is the source's:

1. **Replace `𝒳` by `𝒵`.** The factorization `g : 𝒯 ⟶ 𝒵` is locally of finite type and has the
   same relative dimension of Stacks 0DRL as `f` at every point, by
   `AlgebraicGeometry.Stack.isLocallyOfFiniteType_substackLift` and
   `AlgebraicGeometry.Stack.relativeStackDimensionAt_substackLift`; `𝒵` is locally
   Noetherian (**Stacks 0CPM**), Jacobson and pseudo-catenary (the parenthetical of
   **Stacks 0DS2**) because `𝒵 ⟶ 𝒳` is an immersion, and `|𝒵|` is irreducible by
   `AlgebraicGeometry.Stack.irreducibleSpace_points_schemeTheoreticImage`. Quasi-compactness
   passes from `f = g ≫ i` to `g` by **Stacks 050Y**, the inclusion `i` of `𝒵` being a
   monomorphism and hence quasi-separated.
2. **An irreducible affine chart `V` of `𝒵`.**
   `AlgebraicGeometry.Stack.exists_irreducible_affine_smooth_chart`.
3. **An affine chart `A` of `𝒯 ×_𝒵 V`.** That 2-fibre product is quasi-compact because `g` is
   quasi-compact and `V` is affine, so it has an affine smooth surjective chart (**Stacks 04YC**);
   `A` is locally Noetherian, being a smooth chart of a locally Noetherian stack, hence Noetherian,
   hence every morphism out of it is quasi-compact (**Stacks 01P0**). This is the step at which
   the quasi-compactness hypothesis is used, and it is a genuine use: the scheme-level input of
   step 5 fails for a dominant morphism that is not quasi-compact, as the disjoint union of the
   closed points of `𝔸¹` over `𝔸¹` shows. An unconditional argument has to reach this step with
   a quasi-compact morphism in hand rather than pass it with a weaker hypothesis.
4. **`A ⟶ V` is dominant.** `AlgebraicGeometry.Stack.dense_range_pointsMap_substackLift`
   (**Stacks 0CML**), `AlgebraicGeometry.Stack.dense_range_pointsMap_fst_of_isTwoFibreProduct`
   (**Stacks 04XH**) and `AlgebraicGeometry.Stack.isDominant_siteMap_of_dense_range`.
5. **The dimension formula for `A ⟶ V`.**
   `exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace`.
6. **Back to the stacks.**
   `AlgebraicGeometry.Stack.dimensionAtPoint_schemeStack_eq_dimensionSubNat` and
   `AlgebraicGeometry.Stack.relativeStackDimensionAt_schemeStack_eq_dimensionSubNat` turn the
   formula into the hypothesis of the chart comparison
   `AlgebraicGeometry.Stack.dimensionAtPoint_eq_add_relativeStackDimensionAt_of_chartComparison`,
   whose conclusion is the equality at the image of the open subset of `A` — an open subset of
   `|𝒯|`, the chart being smooth and hence open on points.
7. **`dim_{g(t)}(𝒵) = dim(𝒵)`.** Stacks 0DRX on the irreducible `𝒵`, through
   `AlgebraicGeometry.Stack.dimension_eq_dimensionAtPoint_of_isConstant`.

#### References

* [Stacks Project, Tag 01P0](https://stacks.math.columbia.edu/tag/01P0)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04Y9](https://stacks.math.columbia.edu/tag/04Y9)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 05UP](https://stacks.math.columbia.edu/tag/05UP)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
* [Stacks Project, Tag 0CPU](https://stacks.math.columbia.edu/tag/0CPU)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
* [Stacks Project, Tag 0DRY](https://stacks.math.columbia.edu/tag/0DRY)
* [Stacks Project, Tag 0DS2](https://stacks.math.columbia.edu/tag/0DS2)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of `|schemeStack U|` named by a point `x` of the scheme `U` through the chart of
Stacks 04SW is the one named by `x` through the homeomorphism of Stacks 04XL. -/
theorem pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm
    (U : BigFppfOver B S hS) (x : (BigFppfOver.toScheme B S hS).obj U) :
    letI := pointTopology B S hS (schemeFibredCategory B S hS U)
    pointsHomeomorphScheme B S hS U
        (representedChartPointMap B S hS U ((Space.pointsEquivScheme B S hS U).symm x)) = x := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  rw [pointsHomeomorphScheme_representedChartPointMap B S hS U]
  exact (Space.pointsEquivScheme B S hS U).apply_symm_apply x

/-- **The generic dimension equality of Stacks 0DS4, at the points of `|𝒯|`, for a quasi-compact
1-morphism.** Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact 1-morphism locally of finite type of locally
Noetherian algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳` Jacobson and pseudo-catenary,
and let `P` cut out the scheme theoretic image `𝒵` of Stacks 0CMI. Then there is a nonempty open
subset of `|𝒯|` on which `dim_t(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})`.

See the implementation notes of this file for the seven steps and for where quasi-compactness of
`f` is used. -/
theorem
  exists_isOpen_nonempty_dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    ∃ W : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) W ∧ W.Nonempty ∧
        ∀ t ∈ W, dimensionAtPoint B S hS 𝒯 h𝒯 t =
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
            relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  classical
  let := pointTopology B S hS 𝒯.val
  let := pointTopology B S hS 𝒳.val
  have := h𝒯Irreducible
  -- Step 1: replace `𝒳` by the scheme theoretic image `𝒵`.
  set hA := hP.isAlgebraicStack with hAdef
  set 𝒵 := fullSubcategoryAlgebraicStack 𝒳 P hA with h𝒵def
  set i := fullSubcategoryInclusion 𝒳 P hA with hidef
  set g := substackLift B S hS f hA hP.prop_obj with hgdef
  have hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS g :=
    isLocallyOfFiniteType_substackLift.{u, w} B S hS f hf hA hP.prop_obj
  have h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵 :=
    isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 P hP.1 hA h𝒳
  have himm : AlgebraicStacks.IsImmersion B S hS i :=
    isImmersion_fullSubcategoryInclusion B S hS 𝒳 P hP.1 hA
  have hmono : AlgebraicStacks.IsMonomorphism B S hS i :=
    AlgebraicStacks.isMonomorphism_of_isImmersion B S hS i himm
  have h𝒵Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒵 :=
    AlgebraicStacks.isJacobson_of_isImmersion B S hS i himm h𝒳Jacobson
  have h𝒵Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒵 :=
    AlgebraicStacks.isPseudoCatenary_of_isImmersion B S hS i himm h𝒳Catenary
  have h𝒵Irr : @IrreducibleSpace _ (pointTopology B S hS 𝒵.val) :=
    irreducibleSpace_points_schemeTheoreticImage B S hS f hfQC h𝒯Irreducible hP
  let := pointTopology B S hS 𝒵.val
  have := h𝒵Irr
  have hgQC : IsQuasiCompactMorphism B S hS g :=
    isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS g i
      (by rwa [hgdef, hidef, substackLift_comp])
      (AlgebraicStacks.isQuasiSeparated_of_isMonomorphism B S hS i hmono)
  -- Step 2: an irreducible affine smooth chart `V` of `𝒵`.
  obtain ⟨V, a, hasm, hVaff, hVirr, hVN⟩ :=
    exists_irreducible_affine_smooth_chart.{u, w} B S hS 𝒵 h𝒵 h𝒵Irr.toNonempty
  have haft : AlgebraicStacks.IsLocallyOfFiniteType B S hS a :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hasm
  have := hVaff
  have := hVirr
  have := hVN
  have h𝒱 : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS V) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS a haft h𝒵
  -- Step 3: an affine smooth surjective chart `A` of `𝒯 ×_𝒵 V`.
  set Q := twoFibreProductSquareAlgebraicStacks B S hS a g with hQdef
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a g
  have hQqc : IsQuasiCompactStack.{u, w} B S hS Q.pt.val Q.pt.property :=
    hgQC (schemeStack.{u, w} B S hS V) a
      (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S hS V inferInstance)
  have hsnd : AlgebraicStacks.IsLocallyOfFiniteType B S hS Q.snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS a g Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) haft
  have hsndsm : AlgebraicStacks.IsSmooth B S hS Q.snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS a g Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hasm
  have h𝒫 : IsLocallyNoetherianStack.{u, w} B S hS Q.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Q.snd hsnd h𝒯
  obtain ⟨A, hAaff, ρ, hρsurj, hρsm⟩ := exists_affineAtlas_of_isQuasiCompactStack B S hS Q.pt hQqc
  have hρft : AlgebraicStacks.IsLocallyOfFiniteType B S hS ρ :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS ρ hρsm
  have := hAaff
  have hAN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A) :=
    AlgebraicStacks.isLocallyNoetherian_of_isSmooth B S hS A Q.pt h𝒫 ρ hρsm
  have := hAN
  have : IsNoetherian ((BigFppfOver.toScheme B S hS).obj A) := ⟨⟩
  have h𝒲 : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS A) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS ρ hρft h𝒫
  -- the composite chart over `V`, and the morphism of schemes it induces
  set h := ρ ≫ Q.fst with hhdef
  have hhft : AlgebraicStacks.IsLocallyOfFiniteType B S hS h :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS ρ Q.fst hρft
      (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS g a Q hQ hg)
  set γ := siteMap B S hS h with hγdef
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map γ) :=
    locallyOfFiniteType_siteMap B S hS h hhft
  -- Step 4: `A ⟶ V` is dominant.
  have : IsDominant ((BigFppfOver.toScheme B S hS).map γ) := by
    refine isDominant_siteMap_of_dense_range B S hS h ?_
    rw [hhdef, AlgebraicStacks.pointsMap_comp B S hS ρ Q.fst, Set.range_comp,
      hρsurj.range_eq, Set.image_univ]
    exact dense_range_pointsMap_fst_of_isTwoFibreProduct B S hS Q hQ
      (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS a hasm)
      (dense_range_pointsMap_substackLift B S hS f hfQC hP)
  -- Step 5: the dimension formula for the morphism of schemes `A ⟶ V`.
  obtain ⟨O, hOopen, hOne, hOeq⟩ :=
    exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace
      ((BigFppfOver.toScheme B S hS).map γ)
  -- Step 6: transport the formula to the stacks along the chart comparison.
  let := pointTopology B S hS (schemeFibredCategory B S hS A)
  set e : (BigFppfOver.toScheme B S hS).obj A →
      points B S hS 𝒯.val.val 𝒯.val.property := fun x =>
    AlgebraicStacks.pointsMap B S hS (ρ ≫ Q.snd)
      ((pointsHomeomorphScheme B S hS A).symm x) with hedef
  have hechart : ∀ x, e x = AlgebraicStacks.pointsMap B S hS (ρ ≫ Q.snd)
      (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm x)) := by
    intro x
    rw [hedef]
    refine congrArg (AlgebraicStacks.pointsMap B S hS (ρ ≫ Q.snd)) ?_
    exact ((pointsHomeomorphScheme B S hS A).eq_symm_apply.2
      (pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm B S hS A x)).symm
  have heopen : @IsOpenMap _ _ _ (pointTopology B S hS 𝒯.val) e := by
    refine IsOpenMap.comp (g := AlgebraicStacks.pointsMap B S hS (ρ ≫ Q.snd))
      (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS (ρ ≫ Q.snd)
        (AlgebraicStacks.isSmooth_comp B S hS ρ Q.snd hρsm hsndsm))
      (pointsHomeomorphScheme B S hS A).symm.isOpenMap
  refine ⟨e '' O, heopen O hOopen, hOne.image e, ?_⟩
  rintro _ ⟨x, hxO, rfl⟩
  -- the chart comparison at the point of `|A|` named by `x`
  have hchart : dimensionAtPoint B S hS (schemeStack.{u, w} B S hS A) h𝒲
        (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm x)) =
      dimensionAtPoint B S hS (schemeStack.{u, w} B S hS V) h𝒱
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (schemeStack.{u, w} B S hS V).val.property Q.fst.hom.hom
            (pointsMap B S hS (schemeStack.{u, w} B S hS A).val.val
              (schemeStack.{u, w} B S hS A).val.property Q.pt.val.property ρ.hom.hom
              (representedChartPointMap B S hS A
                ((Space.pointsEquivScheme B S hS A).symm x)))) +
        relativeStackDimensionAt.{u, w} B S hS h hhft h𝒲 h𝒱
          (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm x)) := by
    have hpt : pointsMap B S hS Q.pt.val.val Q.pt.val.property
          (schemeStack.{u, w} B S hS V).val.property Q.fst.hom.hom
          (pointsMap B S hS (schemeStack.{u, w} B S hS A).val.val
            (schemeStack.{u, w} B S hS A).val.property Q.pt.val.property ρ.hom.hom
            (representedChartPointMap B S hS A
              ((Space.pointsEquivScheme B S hS A).symm x))) =
        representedChartPointMap B S hS V ((Space.pointsEquivScheme B S hS V).symm
          ((BigFppfOver.toScheme B S hS).map γ x)) := by
      let := pointTopology B S hS (schemeFibredCategory B S hS V)
      refine (pointsHomeomorphScheme B S hS V).injective ?_
      rw [pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm B S hS V]
      have := pointsHomeomorphScheme_pointsMap B S hS h
        (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm x))
      rw [pointsHomeomorphScheme_representedChartPointMap_pointsEquivScheme_symm B S hS A] at this
      rw [← this, hhdef, AlgebraicStacks.pointsMap_comp B S hS ρ Q.fst]
      rfl
    rw [hpt, dimensionAtPoint_schemeStack_eq_dimensionSubNat B S hS A h𝒲,
      dimensionAtPoint_schemeStack_eq_dimensionSubNat B S hS V h𝒱,
      relativeStackDimensionAt_schemeStack_eq_dimensionSubNat B S hS h hhft h𝒲 h𝒱 x,
      Space.pointsToScheme_pointsEquivScheme_symm B S hS A,
      Space.pointsToScheme_pointsEquivScheme_symm B S hS V,
      ← dimensionSubNat_add_zero, hOeq x hxO]
  have hcomp := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_chartComparison.{u, w}
    B S hS g a hg haft hasm h𝒯 h𝒵 h𝒱 h𝒲 Q hQ ρ hρft hρsm hhft
    (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm x)) hchart
  -- Step 7: `dim_{g(t)}(𝒵) = dim(𝒵)` by Stacks 0DRX, and the relative dimension of `f` is that
  -- of `g`.
  rw [hechart x, AlgebraicStacks.pointsMap_comp B S hS ρ Q.snd]
  refine hcomp.trans ?_
  rw [relativeStackDimensionAt_substackLift.{u, w} B S hS f hf hA hP.prop_obj hmono
    h𝒯 h𝒵 h𝒳]
  refine congrArg (fun z => z + relativeStackDimensionAt.{u, w} B S hS g hg h𝒯 h𝒵 _) ?_
  exact (dimension_eq_dimensionAtPoint_of_irreducibleSpace B S hS 𝒵 h𝒵 h𝒵Jacobson h𝒵Catenary
    h𝒵Irr _).symm


/-- **The generic equality of Stacks 0DS4 for a quasi-compact 1-morphism.** For a quasi-compact
1-morphism `f : 𝒯 ⟶ 𝒳` locally of finite type of Jacobson, pseudo-catenary, locally Noetherian
algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳` quasi-separated, and `P` cutting out
the scheme theoretic image `𝒵` of Stacks 0CMI, there is a nonempty open subset of `|𝒯|` on which
`dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})`.

This is
`exists_isOpen_nonempty_dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism`
followed by the passage from `dim_t(𝒯)` to `dim(𝒯)`,
`AlgebraicGeometry.Stack.exists_isOpen_dimension_eq_add_relativeStackDimensionAt`, whose
constancy hypothesis is Stacks 0DRX on the irreducible `𝒯`. -/
theorem exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    ∃ W : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) W ∧ W.Nonempty ∧
        ∀ t ∈ W, dimension B S hS 𝒯 h𝒯 =
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
            relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t :=
  exists_isOpen_dimension_eq_add_relativeStackDimensionAt B S hS 𝒯 𝒳 f h𝒯 h𝒳 P hP
    hP.isAlgebraicStack hf h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
    h𝒳QuasiSeparated
    (isConstant_dimensionAtPoint_of_irreducibleSpace.{u, w} B S hS 𝒯 h𝒯 h𝒯Jacobson h𝒯Catenary
      h𝒯Irreducible) <|
  exists_isOpen_nonempty_dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
    B S hS f hf hfQC h𝒯 h𝒳 h𝒳Jacobson h𝒳Catenary h𝒯Irreducible hP

/-- **The inequality of Stacks 0DS4 for a quasi-compact 1-morphism.** Under the hypotheses of
`exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism`,
`dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at *every* `t ∈ |𝒯|`.

The generic equality implies it, by
`AlgebraicGeometry.Stack.dimension_le_add_relativeStackDimensionAt_of_exists_isOpen` — the upper
semi-continuity of Stacks 0DRQ (1) together with the constancy of Stacks 0DRX. -/
@[stacks 0DS4 "the inequality at every point of 𝒯, for f quasi-compact as in the statement"]
theorem dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (_h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    dimension B S hS 𝒯 h𝒯 ≤
      closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
        relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t :=
  dimension_le_add_relativeStackDimensionAt_of_exists_isOpen.{u, w} B S hS f hf h𝒯 h𝒳
    h𝒯Jacobson h𝒯Catenary h𝒯Irreducible _ (t := t) <|
  exists_isOpen_nonempty_dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
    B S hS f hf hfQC h𝒯 h𝒳 h𝒳Jacobson h𝒳Catenary h𝒯Irreducible hP

/-- **The content of Stacks 0DS4 for a quasi-compact 1-morphism.** Let `f : 𝒯 ⟶ 𝒳` be a
quasi-compact 1-morphism locally of finite type of Jacobson, pseudo-catenary, locally Noetherian
algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳` quasi-separated, and let `P` cut out the
scheme theoretic image `𝒵` of Stacks 0CMI. Then `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every
`t ∈ |𝒯|`, and equality holds on an open subset of `|𝒯|` that is nonempty, equivalently dense,
`|𝒯|` being irreducible. -/
@[stacks 0DS4 "both clauses: the inequality at every point and the equality on a dense open \
subset, for f quasi-compact as in the statement"]
theorem
  dimension_le_add_and_exists_isOpen_dense_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    (∀ t : points B S hS 𝒯.val.val 𝒯.val.property,
        dimension B S hS 𝒯 h𝒯 ≤
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
            relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t) ∧
      ∃ W : Set (points B S hS 𝒯.val.val 𝒯.val.property),
        @IsOpen _ (pointTopology B S hS 𝒯.val) W ∧ W.Nonempty ∧
          @Dense _ (pointTopology B S hS 𝒯.val) W ∧
          ∀ t ∈ W, dimension B S hS 𝒯 h𝒯 =
            closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
              relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  let := pointTopology B S hS 𝒯.val
  have := h𝒯Irreducible
  refine ⟨fun t =>
    dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
      B S hS f hf hfQC h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated hP t, ?_⟩
  obtain ⟨W, hWopen, hWne, hWeq⟩ :=
    exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism.{u, w}
      B S hS f hf hfQC h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated hP
  exact ⟨W, hWopen, hWne, hWopen.dense hWne, hWeq⟩

end AlgebraicGeometry.Stack

/-!
### Stacks 0DS6: the dimension of the scheme theoretic image of a quasi-DM 1-morphism

Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact, locally of finite type, quasi-DM 1-morphism of Jacobson,
pseudo-catenary, locally Noetherian algebraic stacks over `S`, with `|𝒯|` irreducible and `𝒳`
quasi-separated, and let `𝒵 ↪ 𝒳` be the scheme theoretic image of `f` (Stacks 0CMI).
**Stacks 0DS6** says that `dim(𝒵) ≤ dim(𝒯)`, and that exactly one of the following holds: either
`dim_t(𝒯_{f(t)}) > 0` at every finite type point `t ∈ |𝒯|`, in which case `dim(𝒵) < dim(𝒯)`, or
`𝒯` and `𝒵` have the same dimension.

#### Main results

* `AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism`: the
  inequality `dim(𝒵) ≤ dim(𝒯)`.
* `AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos`:
  with no finiteness hypothesis, either `𝒯` and `𝒵` have the same dimension, or the fibre
  dimension is positive at every finite type point and `dim(𝒵) < dim(𝒯)`, and not both.
* `closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos_of_ne_top`:
  **Stacks 0DS6**, for `dim(𝒯)` finite: `dim(𝒵) ≤ dim(𝒯)`, exactly one of the two alternatives
  holds, and the first forces `dim(𝒵) < dim(𝒯)`.
* `AlgebraicGeometry.Stack.exists_isFiniteTypePoint_mem_of_isOpen`: a nonempty open subset of the
  points of a Jacobson algebraic stack contains a finite type point.
* `AlgebraicGeometry.Stack.dimensionAtPoint_ne_bot`: the dimension of Stacks 0AFN at a point is
  never `-∞`.

#### Implementation notes

The source's proof combines two facts. The fibre dimension `dim_t(𝒯_{f(t)})` is non-negative
because `f` is quasi-DM (Remark Stacks 0DS5), which is
`AlgebraicGeometry.Stack.zero_le_relativeStackDimensionAt`. And Stacks 0DS4 gives
`dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at every point with equality on a nonempty open subset of
`|𝒯|`; under the hypotheses here, quasi-compactness of `f` included, that is
`dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_isQuasiCompactMorphism`
together with `exists_isOpen_dimension_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism`.
The order-theoretic deduction of the two conclusions from these is
`AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension` and
`AlgebraicGeometry.Stack.xor_relativeDimension_pos_and_lt_dimension_eq`.

Quasi-compactness of `f` cannot be dropped. Let `T` be the affine line over a field `k` with
infinitely many origins, the `n`-th origin chart being `Spec k[x, ε, δ]/(xε, xδ, (ε, δ)^(n+1))`,
and let `f : T ⟶ 𝔸²` be given by `(ε, δ)`. Every other hypothesis holds, `f` being a morphism of
schemes and hence quasi-DM, but the scheme theoretic image of `f` is all of `𝔸²`, so
`dim(𝒵) = 2 > 1 = dim(T)`.

The registered statement asks moreover that `dim(𝒯)` be finite. The source's subtractions
`dim 𝒯 - dim 𝒵` presuppose it, and when `dim(𝒯) = dim(𝒵) = ∞` the two alternatives can hold at
once (see the docstring of the registered declaration); the statement holding with no finiteness
hypothesis is the weaker exclusive alternative above.

The scheme theoretic image is a property `P` of the objects of `𝒳` cutting out a closed substack,
and `hP : AlgebraicGeometry.Stack.IsSchemeTheoreticImage f P` says that it is the image; its
dimension is `AlgebraicGeometry.Stack.closedSubstackDimension`, at the proof
`hP.isAlgebraicStack` that the substack it cuts out is algebraic.

#### References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
* [Stacks Project, Tag 0DS6](https://stacks.math.columbia.edu/tag/0DS6)
-/

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- If `E = D + c` for a positive integer `c` and `E` is finite, then `D < E`. -/
theorem lt_of_eq_add_intCast_of_ne_top_of_ne_bot {D E : EInt} {c : ℤ} (hc : 0 < c)
    (h : E = D + ((c : ℤ) : EInt)) (hEtop : E ≠ ⊤) (hEbot : E ≠ ⊥) : D < E := by
  have hc' : ((c : ℤ) : EInt) = ((((c : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) := rfl
  subst h
  rw [hc'] at hEtop hEbot ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd (WithBot.bot_add _) hEbot
  | coe D' =>
    induction D' using WithTop.recTopCoe with
    | top =>
      refine absurd ?_ hEtop
      rw [← WithBot.coe_add, WithTop.top_add]
      rfl
    | coe d =>
      rw [← WithBot.coe_add, ← WithTop.coe_add, WithBot.coe_lt_coe, WithTop.coe_lt_coe]
      omega

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The dimension of Stacks 0AFN of a locally Noetherian algebraic stack at a point is never
`-∞`: by the formula of Stacks 0DRJ along a smooth chart by an algebraic space through the point,
it is `dim_u(U) - d` for a natural number `d`, and `dim_u(U)` is an infimum of local Krull
dimensions of schemes at points, each at least `0`. -/
theorem dimensionAtPoint_ne_bot (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x ≠ ⊥ := by
  obtain ⟨U, hU, a, hsm, u, hu⟩ := exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w}
    B S hS 𝒳 x
  obtain ⟨d, -, heq⟩ := exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳
    h𝒳 x hU a hsm (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hsm) u hu
  have h0 : (0 : WithBot ℕ∞) ≤ Space.dimensionAtPoint B S hS U hU u :=
    le_sInf (by
      rintro _ ⟨_, _, _, _, _, rfl⟩
      exact topologicalKrullDimAt_nonneg _)
  rw [heq]
  generalize Space.dimensionAtPoint B S hS U hU u = δ at h0 ⊢
  induction δ using WithBot.recBotCoe with
  | bot => exact absurd h0 (not_le.2 (WithBot.bot_lt_coe 0))
  | coe δ' =>
    induction δ' using WithTop.recTopCoe with
    | top => exact WithBotTop.top_ne_bot
    | coe m =>
      change (((m : ℤ) - (d : ℤ) : ℤ) : EInt) ≠ ⊥
      exact WithBotTop.coe_ne_bot _

/-- **A nonempty open subset of the points of a Jacobson algebraic stack contains a finite type
point.** Pull the open subset back along a smooth surjective chart by a Jacobson scheme: it is a
nonempty open subset there, so it contains a closed point of the chart, whose image is a finite
type point by Stacks 06FX. -/
theorem exists_isFiniteTypePoint_mem_of_isOpen (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    {W : Set (points B S hS 𝒳.val.val 𝒳.val.property)}
    (hWopen : @IsOpen _ (pointTopology B S hS 𝒳.val) W) (hWne : W.Nonempty) :
    ∃ t ∈ W, IsFiniteTypePoint.{u, w} B S hS 𝒳 t := by
  obtain ⟨U, φ, hφsurj, hφsm, hUjac⟩ := h𝒳Jacobson
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  have := hUjac
  set e := pointsHomeomorphScheme B S hS U with he
  have hcont : Continuous (AlgebraicStacks.pointsMap B S hS φ) :=
    continuous_pointsMap B S hS _ 𝒳.val φ.hom.hom
  set O : Set ((BigFppfOver.toScheme B S hS).obj U) :=
    e.symm ⁻¹' (AlgebraicStacks.pointsMap B S hS φ ⁻¹' W) with hO
  have hOopen : IsOpen O := (hWopen.preimage hcont).preimage e.symm.continuous
  obtain ⟨t₀, ht₀⟩ := hWne
  obtain ⟨z, hz⟩ := hφsurj t₀
  have hOne : O.Nonempty := ⟨e z, by
    change AlgebraicStacks.pointsMap B S hS φ (e.symm (e z)) ∈ W
    rw [e.symm_apply_apply, hz]
    exact ht₀⟩
  obtain ⟨y, hyO, hycl⟩ := nonempty_inter_closedPoints hOne hOopen.isLocallyClosed
  refine ⟨AlgebraicStacks.pointsMap B S hS φ (e.symm y), hyO, ?_⟩
  refine isFiniteTypePoint_of_exists_isClosed_smoothChart.{u, w} B S hS 𝒳 _
    ⟨U, φ, e.symm y, hφsm, ?_, rfl⟩
  rw [e.apply_symm_apply]
  exact hycl

/-- **The inequality of Stacks 0DS6.** For a quasi-compact, locally of finite type, quasi-DM
1-morphism `f : 𝒯 ⟶ 𝒳` of Jacobson, pseudo-catenary, locally Noetherian algebraic stacks over
`S`, with `|𝒯|` irreducible and `𝒳` quasi-separated, and `P` cutting out the scheme theoretic
image `𝒵` of `f`, one has `dim(𝒵) ≤ dim(𝒯)`.

At a point of the nonempty open subset of `|𝒯|` on which
`dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` (Stacks 0DS4 for a quasi-compact `f`), the fibre dimension
is non-negative because `f` is quasi-DM. -/
@[stacks 0DS6 "the first clause, dim Z ≤ dim T, under exactly the hypotheses of the source",
  ega "IV 4.1.2" "(i)"]
theorem closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hDM : AlgebraicStacks.IsQuasiDM B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 ≤ dimension B S hS 𝒯 h𝒯 := by
  obtain ⟨-, W, -, ⟨t, ht⟩, -, hWeq⟩ :=
  dimension_le_add_and_exists_isOpen_dense_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
      B S hS f hf hfQC h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated hP
  exact closedSubstackDimension_le_dimension B S hS 𝒯 𝒳 f h𝒯 h𝒳 P hP hP.isAlgebraicStack
    (relativeStackDimensionAt B S hS f hf h𝒯 h𝒳) hf hDM h𝒯Jacobson h𝒳Jacobson h𝒯Catenary
    h𝒳Catenary h𝒯Irreducible h𝒳QuasiSeparated
    (fun t => zero_le_relativeStackDimensionAt.{u, w} B S hS f hDM hf h𝒯 h𝒳 t) ⟨t, hWeq t ht⟩

/-- **The exclusive alternative of Stacks 0DS6, with no finiteness hypothesis.** Let
`f : 𝒯 ⟶ 𝒳` be a quasi-compact, locally of finite type 1-morphism of
Jacobson, pseudo-catenary, locally Noetherian algebraic stacks over `S` which is quasi-DM, whose
source is irreducible and whose target is quasi-separated, and let `𝒵 ↪ 𝒳`, cut out by `P`, be the
scheme theoretic image of `f`. Then `dim(𝒵) ≤ dim(𝒯)`, and exactly one of the following holds:
`dim_t(𝒯_{f(t)}) > 0` at every finite type point `t ∈ |𝒯|` and `dim(𝒵) < dim(𝒯)`; or `𝒯` and
`𝒵` have the same dimension. That the first condition alone already excludes the second is
proved for `dim(𝒯)` finite, in
`closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos_of_ne_top`.

The fibre dimension `dim_t(𝒯_{f(t)})` is the relative dimension
`AlgebraicGeometry.Stack.relativeStackDimensionAt` of Stacks 0DRL. It is non-negative because `f`
is quasi-DM (`AlgebraicGeometry.Stack.zero_le_relativeStackDimensionAt`), and Stacks 0DS4 for a
quasi-compact `f` bounds `dim(𝒯)` by `dim(𝒵) + dim_t(𝒯_{f(t)})` everywhere with equality on a
dense open subset; the two conclusions follow. -/
theorem closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hDM : AlgebraicStacks.IsQuasiDM B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 ≤ dimension B S hS 𝒯 h𝒯 ∧
      Xor ((∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t →
            0 < relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) ∧
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 <
            dimension B S hS 𝒯 h𝒯)
        (dimension B S hS 𝒯 h𝒯 =
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳) := by
  obtain ⟨hbound, W, -, ⟨t, ht⟩, -, hWeq⟩ :=
  dimension_le_add_and_exists_isOpen_dense_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
      B S hS f hf hfQC h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated hP
  have hnonneg := fun t => zero_le_relativeStackDimensionAt.{u, w} B S hS f hDM hf h𝒯 h𝒳 t
  exact ⟨closedSubstackDimension_le_dimension_of_isQuasiCompactMorphism B S hS f hfQC hf hDM h𝒯
      h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible h𝒳QuasiSeparated hP,
    xor_relativeDimension_pos_and_lt_dimension_eq B S hS 𝒯 𝒳 f h𝒯 h𝒳 P hP hP.isAlgebraicStack
      (relativeStackDimensionAt B S hS f hf h𝒯 h𝒳) hf hDM h𝒯Jacobson h𝒳Jacobson h𝒯Catenary
      h𝒳Catenary h𝒯Irreducible h𝒳QuasiSeparated hnonneg hbound ⟨t, hWeq t ht⟩⟩

/-- **Stacks 0DS6**, for `𝒯` of finite dimension. Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact, locally of
finite type 1-morphism of Jacobson, pseudo-catenary, locally Noetherian algebraic stacks over `S`
which is quasi-DM, whose source is irreducible and whose target is quasi-separated, and let
`𝒵 ↪ 𝒳`, cut out by `P`, be the scheme theoretic image of `f`. Suppose `dim(𝒯) ≠ ∞`. Then
`dim(𝒵) ≤ dim(𝒯)`, and exactly one of the following holds: (1) `dim_t(𝒯_{f(t)}) > 0` at every
finite type point `t ∈ |𝒯|`, in which case `dim(𝒵) < dim(𝒯)`; or (2) `dim(𝒯) = dim(𝒵)`.

**Erratum.** The source states the lemma without the hypothesis `dim(𝒯) ≠ ∞`, and as written
it is false when `dim(𝒯) = dim(𝒵) = ∞`. Let `N` be Nagata's Noetherian ring of infinite dimension
(Stacks, Examples, Tag 02JC), let `D = N⟨X⟩` be the localization of `N[X]` at the monic
polynomials, and let `f : 𝔸¹_D ⟶ Spec D` be the projection.
* Every hypothesis holds. `N` is regular, its local rings being localizations of polynomial rings,
  so `D` is a Noetherian regular domain, hence Cohen–Macaulay and universally catenary
  (Stacks 00NM), and `D[s]` is as well. `D` is Jacobson by J. W. Brewer and W. J. Heinzer,
  *R Noetherian implies R⟨X⟩ is a Hilbert ring*, J. Algebra 67 (1980) 204–209,
  doi:10.1016/0021-8693(80)90317-8; so is `D[s]`, being of finite type over `D`. `𝔸¹_D` is
  irreducible, `f` is affine, hence quasi-compact and representable, hence quasi-DM, and of finite
  type, and `Spec D` is affine, hence quasi-separated.
* Both alternatives hold. `f` is faithfully flat, so its scheme theoretic image is `Spec D`. Every
  fibre is an affine line over a field, so `dim_t(𝒯_{f(t)}) = 1 > 0` everywhere. The primes
  `p_i N[X]` contain no monic polynomial and have unbounded height, so
  `dim(𝒯) = dim(𝒵) = ∞`. Thus (1) and (2) hold together, and (1) does not force
  `dim(𝒵) < dim(𝒯)`.

This counterexample is machine-checked:
`AlgebraicGeometry.Stack.not_forall_xor_relativeDimension_pos`, in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionSchemeTheoreticImageCounterexample0DS6.lean`,
proves that the statement below without `h𝒯Finite` is false, every hypothesis of the source
(quasi-compactness of `f` included) being proved for this `f`.

Infinite-dimensional Noetherian Hilbert domains were first constructed by K. Fujita, *Infinite
dimensional Noetherian Hilbert domains*, Hiroshima Math. J. 5 (1975) 181–185,
doi:10.32917/hmj/1206136627. The source's arithmetic presupposes finiteness: Stacks 0DS4, from
which it derives this lemma, is stated as `dim_t(𝒯_{f(t)}) ≥ dim 𝒯 - dim 𝒵`, and the proof as
`dim_t(𝒯_{f(t)}) = dim_t 𝒯 - dim_{f(t)} 𝒵`, differences that are undefined when both dimensions
are infinite; Stacks 0DRT, on which Stacks 0DRX rests, assumes finite dimension explicitly. With
no finiteness hypothesis, what holds is
`AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos`:
`dim(𝒵) ≤ dim(𝒯)` and `Xor ((1) ∧ dim(𝒵) < dim(𝒯)) (2)`.

The proof: Stacks 0DS4 for a quasi-compact `f` gives `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` at
every point, with equality on a nonempty open subset `W` of `|𝒯|`; the fibre dimensions are
non-negative integers because `f` is quasi-DM. The open `W` contains a finite type point `t`,
`𝒯` being Jacobson (`AlgebraicGeometry.Stack.exists_isFiniteTypePoint_mem_of_isOpen`). Under (1)
the fibre dimension at `t` is a positive integer, so `dim(𝒵) < dim(𝒯)` because `dim(𝒯)` is finite
— it is neither `∞`, by hypothesis, nor `-∞`, by
`AlgebraicGeometry.Stack.dimensionAtPoint_ne_bot`; hence (1) excludes (2). If (2) fails, then
(1) holds by
`AlgebraicGeometry.Stack.closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos`. -/
@[stacks 0DS6 "the exactly-one form under the added hypothesis that dim T is finite; erratum: \
false as written when dim T = dim Z = infinity, machine-checked as \
AlgebraicGeometry.Stack.not_forall_xor_relativeDimension_pos (the affine line over N<X>, N \
Nagata's ring; Fujita 1975, Brewer-Heinzer 1980), see the docstring"]
theorem closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos_of_ne_top
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hDM : AlgebraicStacks.IsQuasiDM B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P)
    (h𝒯Finite : dimension B S hS 𝒯 h𝒯 ≠ ⊤) :
    closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 ≤ dimension B S hS 𝒯 h𝒯 ∧
      Xor (∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t →
            0 < relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t)
        (dimension B S hS 𝒯 h𝒯 =
          closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳) ∧
      ((∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t →
            0 < relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) →
        closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 <
          dimension B S hS 𝒯 h𝒯) := by
  obtain ⟨hle, hxor⟩ := closedSubstackDimension_le_dimension_and_xor_relativeDimension_pos B S hS
    f hfQC hf hDM h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
    h𝒳QuasiSeparated hP
  obtain ⟨-, W, hWopen, hWne, -, hWeq⟩ :=
  dimension_le_add_and_exists_isOpen_dense_eq_add_relativeStackDimensionAt_of_isQuasiCompactMorphism
      B S hS f hf hfQC h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
      h𝒳QuasiSeparated hP
  obtain ⟨t, htW, htft⟩ := exists_isFiniteTypePoint_mem_of_isOpen.{u, w} B S hS 𝒯 h𝒯Jacobson
    hWopen hWne
  have hbot : dimension B S hS 𝒯 h𝒯 ≠ ⊥ := fun h =>
    dimensionAtPoint_ne_bot.{u, w} B S hS 𝒯 h𝒯 t
      (le_bot_iff.1 (h ▸ le_iSup (fun x => dimensionAtPoint B S hS 𝒯 h𝒯 x) t))
  have hlt : (∀ t, IsFiniteTypePoint.{u, w} B S hS 𝒯 t →
        0 < relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) →
      closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 <
        dimension B S hS 𝒯 h𝒯 := by
    intro hA
    obtain ⟨c, hc⟩ := exists_relativeStackDimensionAt_eq_intCast.{u, w} B S hS f hf h𝒯 h𝒳 t
    have hpos := hA t htft
    rw [hc, show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_lt_coe] at hpos
    exact lt_of_eq_add_intCast_of_ne_top_of_ne_bot hpos ((hWeq t htW).trans (by rw [hc]))
      h𝒯Finite hbot
  refine ⟨hle, ?_, hlt⟩
  by_cases heq : dimension B S hS 𝒯 h𝒯 =
      closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳
  · exact Or.inr ⟨heq, fun hA => (hlt hA).ne' heq⟩
  · rcases hxor with ⟨hA, -⟩ | ⟨h, -⟩
    · exact Or.inl ⟨hA.1, heq⟩
    · exact absurd h heq

end AlgebraicGeometry.Stack

end
