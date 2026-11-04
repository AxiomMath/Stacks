module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSite

/-!
# The chart diagram of a square-zero extension, valued in the big fppf site

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`.  The chart
diagram `AlgebraicGeometry.Space.SquareZeroExtension.chartSpec` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartDiagram` sends a chart
`U` of the small étale site of `X` to the **scheme** `Spec(𝒜(U))`.  An algebraic space over `S`
is a sheaf on the big fppf site of `S`, so every construction of the ambient space of
[Stacks Project, Tag 05ZT] out of these charts needs them as **objects of that site**, which a
scheme is only once it is small enough and is given over `S`.  This file lifts the diagram
across that difference.

## What an object of the site costs, and which half is not free

`AlgebraicGeometry.BigFppfOver` is the slice `Over (B.obj hS)`, so `Spec(𝒜(U))` is an object of
it exactly when

* `B.Contains (Spec(𝒜(U)))`, the site's size cutoff, which is
  `AlgebraicGeometry.Space.SquareZeroExtension.contains_chartSpec_obj_of_mk_ideal_lt_cutoff`
  for an affine chart, under the named hypothesis `hI` on the sections of `ℐ` there; and
* a structure morphism `Spec(𝒜(U)) ⟶ S`.

**The structure morphism is not derivable from the datum, and is an argument below.**  The datum
of a square-zero extension supplies the `f^{-1}𝒪_Y`-algebra structure of `𝒜` as a map
`toBase : f^{-1}𝒪_Y ⟶ 𝒜` of sheaves of rings on `X_étale`, whose chart-level `Spec` is
`AlgebraicGeometry.Space.SquareZeroExtension.chartSpecToBase :
Spec(𝒜(U)) ⟶ Spec((f^{-1}𝒪_Y)(U))`.  Neither that arrow nor any other in the datum has `S` as
its target: `Y` is an algebraic space and not the base *scheme*, and `(f^{-1}𝒪_Y)(U)` is a ring
of sections, not a scheme over `S`.  Nor is the arrow formal, because
`AlgebraicGeometry.Space.SquareZeroExtension.chartThickeningOfIsAffine` exhibits `U` as a
*first-order thickening* inside `Spec(𝒜(U))`, and extending the structure morphism `U ⟶ S` across a
square-zero thickening is the deformation problem for `S`, which has no solution in general.

The scheme-level datum of [Stacks Project, Tag 05YV] in this development resolves exactly this by
**carrying the morphism as a field**: `Stacks.Thickenings.SquareZeroExtension` has
`toBase : thickenedSpace X A ⟶ S.toSheafedSpace`, a morphism of sheafed spaces *out of the
thickened space*, from which `Stacks.Thickenings.Realization` reads off its `ambient ⟶ S`.  The
spaces-level `AlgebraicGeometry.Space.SquareZeroExtension` carries no such field; its `toBase` is
the mate of one on the small étale site of `X` and over an algebraic space.  So for a general
base scheme either that datum gains a field — which is a change to an existing definition, and
nothing here makes it — or the arrow is supplied by whoever builds the charts, which is what the
explicit argument `g` below records.

**Over a terminal base scheme the arrow is free**, by terminality alone, and
`AlgebraicGeometry.Space.SquareZeroExtension.chartSiteDiagram` is the whole diagram in the site
there.  That is no accident of this formalisation: the implementation note on
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_specULiftZ` records that the source of Tag
05ZT builds the ambient space over `Spec ℤ` and only then transports the `f^{-1}𝒪_Y`-algebra
structure to obtain the morphism to the base.  The hypothesis is satisfiable:
`AlgebraicGeometry.specULiftZIsTerminal` is the terminality of `Spec (ULift ℤ)` and
`AlgebraicGeometry.Stack.contains_specULiftZ` proves that every big fppf site contains it.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartSiteObject`: **the chart `Spec(𝒜(U))` as an
  object of the big fppf site of `S`**, given its containment and a structure morphism.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartSiteObjectHom`: an arrow of the small étale
  site, as a morphism of those objects, given that it lies over `S`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartSiteDiagram`: **the chart diagram as a functor
  from the small étale site of `X` to the big fppf site of `S`**, over a terminal base scheme and
  granted the containment of every chart.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.etale_toScheme_map_chartSiteObjectHom` and
  `…etale_toScheme_map_chartSiteDiagram_map`: **the arrows between affine charts are étale
  morphisms of the site**, with no hypothesis beyond the affineness of the two charts.  This is
  `AlgebraicGeometry.Space.SquareZeroExtension.etale_chartSpec_map_of_isAffine`, which applies
  because the underlying morphism of schemes is unchanged.

## Implementation notes

**One containment hypothesis per chart, and it is a cutoff artefact.**  Each object of the
diagram carries its own `B.Contains`, discharged over an affine chart by
`…contains_chartSpec_obj_of_mk_ideal_lt_cutoff` from a bound on the sections of `ℐ` *over that
chart*.  A route through an étale equivalence relation `R₀ ⇉ U₀` therefore needs the bound at the
relation chart `R₀` as much as at the covering chart `U₀`; `chartSiteDiagram` asks for it at every
chart at once.  As the docstring of that lemma and of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSite` both record, the
bound is **an artefact of this development's cutoff-bounded big fppf site and not a hypothesis of
[Stacks Project, Tag 05ZT]**, whose algebraic spaces are sheaves on a site containing every
scheme.

**What is still owed before these objects form an étale equivalence relation.**  For
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional` the pair of arrows
`Spec(𝒜(R₀)) ⇉ Spec(𝒜(U₀))` coming from the two projections of `R₀ = U₀ ×_X U₀` must satisfy
`Stacks.Groupoids.IsEtaleEquivalenceRelation`.  Its étaleness fields are the two results above;
its `CategoryTheory.IsEquivalenceRelation` field is not, and that field splits into two
unrelated demands.

Transitivity asks for a limiting pullback cone of the two projections together with a
composition arrow out of it, hence for `𝒜` to turn a fibre product of charts into a tensor
product of sections, `𝒜(R₀ ×_{U₀} R₀) = 𝒜(R₀) ⊗_{𝒜(U₀)} 𝒜(R₀)` — a square with `𝒜` at all four
corners, indexed by a cospan of the site.  That square **is** available, for affine charts:
`AlgebraicGeometry.Space.SquareZeroExtension.isPushout_A_map_of_isPullback_of_isAffine`, with its
`Spec` as
`AlgebraicGeometry.Space.SquareZeroExtension.isPullback_chartSpec_map_of_isPullback_of_isAffine`.

What is **not proved** is `CategoryTheory.JointlyMono₂`, which all three fields of an
equivalence relation extend: it asks that `Spec(𝒜(R₀))` be a subobject of
`Spec(𝒜(U₀)) × Spec(𝒜(U₀))`, a product over the *base* and not a fibre product over a chart, so
no square of the chart diagram over a cospan of the site bears on it.  That rules out the
transfer lemmas of `StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer`, but it is **not**
an obstruction: between affine charts the pair is a morphism of affine *schemes*, and for a
morphism of schemes `AlgebraicGeometry.universallyInjective_unramified_tfae` —
[Stacks Project, Tag 05VH] — gives monicity from unramifiedness together with universal
injectivity.  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartRelation` set out that
route and the facts that would feed it; no declaration carries it out.  Granted joint
monicity, reflexivity and symmetry are the functoriality of the diagram at the diagonal
`U₀ ⟶ R₀` and at the flip of `R₀`.

The statement
`AlgebraicGeometry.Space.SquareZeroExtension.isPullback_reductionChartSpec_app_of_isAffine` is a
third square again: it has `𝒪_X` at two of its four corners, it is indexed by a single arrow of
the site rather than by a cospan, and it says that the thickening of a chart is the base change
of the thickening of a chart above it.

**No `@[stacks]` attribute.**  Tag 05ZT concludes that the datum is realized by a first-order
thickening `X ⊂ X'` over `Y` with `𝒪_{X'} ≅ 𝒜`.  This file makes the charts of the diagram whose
colimit is `X'` in the proof of the source into objects of the site; it constructs no algebraic
space, identifies no structure sheaf, and over a general base scheme it does not even produce the
charts without an extra argument.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV), the scheme-level
  statement, whose datum carries the structure morphism as a field.
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW), the quotient of an étale
  equivalence relation, the shape the ambient space is to be built in.
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S), the big fppf site over a
  scheme.
* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH), monicity of a morphism
  of schemes from unramifiedness and universal injectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **The chart `Spec(𝒜(U))` of a square-zero extension, as an object of the big fppf site of
`S`.**

The two things an object of the site is more than a scheme are both arguments: `hcon` is the
size cutoff, which
`AlgebraicGeometry.Space.SquareZeroExtension.contains_chartSpec_obj_of_mk_ideal_lt_cutoff`
discharges over an affine chart from a bound on the sections of `ℐ`, and `g` is the structure
morphism to `S`, which the datum of a square-zero extension does not determine — see the
implementation notes of this file.  Over a terminal base scheme `g` is free, and
`AlgebraicGeometry.Space.SquareZeroExtension.chartSiteDiagram` is the resulting diagram. -/
def chartSiteObject (U : SmallEtale B S hS X.1)
    (hcon : B.Contains ((chartSpec B S hS E).obj U))
    (g : (chartSpec B S hS E).obj U ⟶ S) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hcon g

/-- The scheme underlying the chart of the extension as an object of the site is `Spec(𝒜(U))`. -/
theorem toScheme_obj_chartSiteObject (U : SmallEtale B S hS X.1)
    (hcon : B.Contains ((chartSpec B S hS E).obj U))
    (g : (chartSpec B S hS E).obj U ⟶ S) :
    (BigFppfOver.toScheme B S hS).obj (chartSiteObject B S hS E U hcon g) =
      (chartSpec B S hS E).obj U :=
  rfl

/-- **An arrow of the small étale site of `X`, as a morphism of the charts of the extension in
the big fppf site of `S`.**  The hypothesis `w` is that `Spec` of the restriction map of `𝒜`
lies over `S`; it is what makes the two chosen structure morphisms compatible, and over a
terminal base scheme it holds by terminality. -/
def chartSiteObjectHom {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hconU : B.Contains ((chartSpec B S hS E).obj U))
    (hconV : B.Contains ((chartSpec B S hS E).obj V))
    (gU : (chartSpec B S hS E).obj U ⟶ S) (gV : (chartSpec B S hS E).obj V ⟶ S)
    (w : (chartSpec B S hS E).map h ≫ gV = gU) :
    chartSiteObject B S hS E U hconU gU ⟶ chartSiteObject B S hS E V hconV gV :=
  BigFppfOver.homMk B S hS hconV gV ((chartSpec B S hS E).map h) w

/-- The morphism of schemes underlying `…chartSiteObjectHom` is the arrow of the chart diagram,
which is `Spec` of the restriction map of `𝒜`. -/
theorem toScheme_map_chartSiteObjectHom {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hconU : B.Contains ((chartSpec B S hS E).obj U))
    (hconV : B.Contains ((chartSpec B S hS E).obj V))
    (gU : (chartSpec B S hS E).obj U ⟶ S) (gV : (chartSpec B S hS E).obj V ⟶ S)
    (w : (chartSpec B S hS E).map h ≫ gV = gU) :
    (BigFppfOver.toScheme B S hS).map
        (chartSiteObjectHom B S hS E h hconU hconV gU gV w) =
      (chartSpec B S hS E).map h :=
  rfl

/-- **The arrow of the site between the charts of the extension over two affine charts is
étale**, with no hypothesis beyond the affineness of the two charts.  The underlying morphism of
schemes is the arrow of the chart diagram, so this is
`AlgebraicGeometry.Space.SquareZeroExtension.etale_chartSpec_map_of_isAffine`. -/
theorem etale_toScheme_map_chartSiteObjectHom {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hconU : B.Contains ((chartSpec B S hS E).obj U))
    (hconV : B.Contains ((chartSpec B S hS E).obj V))
    (gU : (chartSpec B S hS E).obj U ⟶ S) (gV : (chartSpec B S hS E).obj V ⟶ S)
    (w : (chartSpec B S hS E).map h ≫ gV = gU)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    Etale ((BigFppfOver.toScheme B S hS).map
      (chartSiteObjectHom B S hS E h hconU hconV gU gV w)) :=
  etale_chartSpec_map_of_isAffine B S hS E h hU hV

/-- **The chart diagram of a square-zero extension as a diagram in the big fppf site of `S`**,
over a terminal base scheme: `U ↦ Spec(𝒜(U))`, a functor from the small étale site of `X` to the
big fppf site of `S`.

Terminality of `S` is what supplies the structure morphisms and makes every arrow of the small
étale site lie over `S`; it is satisfied by the base `Spec (ULift ℤ)` of
`AlgebraicGeometry.specULiftZIsTerminal`, which every big fppf site contains, and it is the base
at which the source of [Stacks Project, Tag 05ZT] builds its ambient space.  The hypothesis
`hcon` is the site's size cutoff at every chart at once; see the implementation notes of this
file for what discharges it and why it is not a hypothesis of the source. -/
def chartSiteDiagram (hterm : IsTerminal S)
    (hcon : ∀ U : SmallEtale B S hS X.1, B.Contains ((chartSpec B S hS E).obj U)) :
    SmallEtale B S hS X.1 ⥤ BigFppfOver B S hS where
  obj U := chartSiteObject B S hS E U (hcon U) (hterm.from _)
  map h := chartSiteObjectHom B S hS E h (hcon _) (hcon _) _ _ (hterm.hom_ext _ _)
  map_id U := BigFppfOver.map_toScheme_injective B S hS (by
    change (chartSpec B S hS E).map (𝟙 U) = 𝟙 _
    exact (chartSpec B S hS E).map_id U)
  map_comp a b := BigFppfOver.map_toScheme_injective B S hS (by
    change (chartSpec B S hS E).map (a ≫ b) =
      (chartSpec B S hS E).map a ≫ (chartSpec B S hS E).map b
    exact (chartSpec B S hS E).map_comp a b)

/-- The scheme underlying the chart diagram in the site over a chart is `Spec(𝒜(U))`. -/
theorem chartSiteDiagram_obj (hterm : IsTerminal S)
    (hcon : ∀ U : SmallEtale B S hS X.1, B.Contains ((chartSpec B S hS E).obj U))
    (U : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).obj ((chartSiteDiagram B S hS E hterm hcon).obj U) =
      (chartSpec B S hS E).obj U :=
  rfl

/-- The morphism of schemes underlying the chart diagram in the site on an arrow is `Spec` of the
restriction map of `𝒜`. -/
theorem chartSiteDiagram_map (hterm : IsTerminal S)
    (hcon : ∀ U : SmallEtale B S hS X.1, B.Contains ((chartSpec B S hS E).obj U))
    {U V : SmallEtale B S hS X.1} (h : U ⟶ V) :
    (BigFppfOver.toScheme B S hS).map ((chartSiteDiagram B S hS E hterm hcon).map h) =
      (chartSpec B S hS E).map h :=
  rfl

/-- **The arrows of the chart diagram in the site between affine charts are étale**, with no
hypothesis beyond the affineness of the two charts.  These are the two étaleness fields of
`Stacks.Groupoids.IsEtaleEquivalenceRelation` for a pair of arrows of the small étale site; what
the remaining field still asks for is set out in the implementation notes of this file. -/
theorem etale_toScheme_map_chartSiteDiagram_map (hterm : IsTerminal S)
    (hcon : ∀ U : SmallEtale B S hS X.1, B.Contains ((chartSpec B S hS E).obj U))
    {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    Etale ((BigFppfOver.toScheme B S hS).map ((chartSiteDiagram B S hS E hterm hcon).map h)) :=
  etale_chartSpec_map_of_isAffine B S hS E h hU hV

end SquareZeroExtension

end AlgebraicGeometry.Space

end
