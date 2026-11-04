module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# The restricted thickening of a chart is the base-changed chart

Let `Z ⊂ X'` be a thickening of algebraic spaces over a scheme `S` contained in a big fppf site
`C` and let `U'` be an étale scheme chart of `X'`.  There are two descriptions of "`Z` over
`U'`":

* the **restricted thickening** `Z.preimage (chartToSpace U').hom` — the closed subspace of the
  chart space cut out by `Z`, which is a thickening of it by [Stacks Project, Tag 09ZX]
  (`AlgebraicGeometry.Space.isThickening_preimage`);
* the **base-changed chart** `thickeningChartBaseChange.obj U'` — the étale scheme chart of `Z`
  obtained from `U'` by base change along the inclusion of `Z`, which is
  `AlgebraicGeometry.Space.smallBaseChange` of [Stacks Project, Tag 03G2] part (4).

This file identifies them, **for a bare `U'`**: no chart presentation of a lifting problem, no
affine hypothesis, nothing but the thickening and the chart.

## Main results

* `AlgebraicGeometry.Space.preimageChartIso`: the restricted thickening of the chart space is
  the space of the base-changed chart, as algebraic spaces over `S`, with
  `AlgebraicGeometry.Space.preimageChartIso_hom_chartToSpace` and
  `AlgebraicGeometry.Space.preimageChartIso_inv_inclusion` the two triangles that pin it down —
  one over `Z`, one over the chart space of `U'`.
* `AlgebraicGeometry.Space.preimageChartOverIso`: the same isomorphism read in `Over` the space
  of `Z`, which is the form a transport of a sheaf on the small étale site of `Z` consumes.

## Implementation notes

**Both sides are pullbacks of one cospan**, namely of `Z.ι` and the chart morphism `U'.1.hom`:

* the restricted thickening by [Stacks Project, Tag 083Q],
  `CategoryTheory.Subfunctor.isPullback_preimage`;
* the base-changed chart by the defining property of a relatively representable morphism, the
  inclusion of a closed subspace being representable
  (`AlgebraicGeometry.Space.isClosedImmersion_inclusion_of_isThickening`).

So the comparison is the canonical isomorphism of two pullbacks of a cospan, and it is already
in the tree in exactly that generality: `AlgebraicGeometry.Space.preimageIso` compares
`yoneda.obj (hrep.pullback φ)` with `(U.preimage φ).toFunctor` for an *arbitrary* subfunctor `U`
with representable inclusion and an *arbitrary* chart morphism `φ`.  Its docstring speaks of an
open subspace because of where it was first needed, but its statement assumes no openness, and
it is reused here rather than restated.  What this file adds is the passage from presheaves to
algebraic spaces and the two triangles in that category, which is what a consumer working with
`AlgebraicGeometry.Space.liftActionSheaf` needs.

**The comparison is taken at object level**, not as a natural isomorphism of functors: a
transport of the acting sheaf is read at one chart at a time, and an object-level identification
is `rfl`-cheap where the corresponding statement about direct-image *functors* forces
`smallToposMorphismTypeU` to unfold.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 03G2] part (4) is registered on
`AlgebraicGeometry.Space.smallBaseChange` and [Stacks Project, Tag 083Q] on
`CategoryTheory.Subfunctor.isPullback_preimage`; comparing two pullbacks of one cospan asserts
neither.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {X' : AlgebraicSpaces C S hS} (Z : Subfunctor X'.1)

/-! ### The comparison of presheaves -/

/-- **The restricted thickening of a chart space is the base-changed chart**, as presheaves.

Both are pullbacks of the cospan formed by the inclusion of `Z` and the chart morphism of `U'`,
so this is `AlgebraicGeometry.Space.preimageIso` at the representable inclusion of the
thickening. -/
def preimageChartPresheafIso (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1) :
    (Z.preimage (chartToSpace C S hS X' U').hom).toFunctor ≅
      (chartSpace C S hS (IsThickening.space C S hS hG)
        ((thickeningChartBaseChange C S hS hG).obj U')).1 :=
  (preimageIso C S hS Z (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep
    U'.1.hom).symm

/-- The comparison of `AlgebraicGeometry.Space.preimageChartPresheafIso` is compatible with the
inclusions into the chart space of `U'`: the base-changed chart sits inside `U'` by the cartesian
projection, and the restricted thickening by the inclusion of a preimage. -/
theorem preimageChartPresheafIso_inv_ι (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1) :
    (preimageChartPresheafIso C S hS Z hG U').inv ≫
        (Z.preimage (chartToSpace C S hS X' U').hom).ι =
      yoneda.map ((isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.snd U'.1.hom) :=
  preimageIso_hom_ι C S hS Z (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep
    U'.1.hom

/-- The comparison of `AlgebraicGeometry.Space.preimageChartPresheafIso` is compatible with the
projections to `Z`: the base-changed chart lies over `Z` by its structure morphism, and the
restricted thickening by the canonical morphism out of a preimage.  Both are the second
projection of the same cartesian square. -/
theorem preimageChartPresheafIso_hom_fst (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1) :
    (preimageChartPresheafIso C S hS Z hG U').hom ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.fst U'.1.hom =
      Z.fromPreimage (chartToSpace C S hS X' U').hom :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

/-! ### The comparison of algebraic spaces -/

/-- **The restricted thickening of a chart space is the space of the base-changed chart**, as
algebraic spaces over `S`, for a bare chart `U'`.

The isomorphism of presheaves is `AlgebraicGeometry.Space.preimageChartPresheafIso`; the
category of algebraic spaces being a full subcategory of presheaves, that is already an
isomorphism of algebraic spaces. -/
def preimageChartIso (hG : IsThickening C S hS X' Z) (U' : SmallEtale C S hS X'.1) :
    IsThickening.space C S hS
        (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG) ≅
      chartSpace C S hS (IsThickening.space C S hS hG)
        ((thickeningChartBaseChange C S hS hG).obj U') :=
  ObjectProperty.isoMk _ (preimageChartPresheafIso C S hS Z hG U')

/-- **The comparison is a morphism over `Z`.**  Its composite with the structure morphism of the
base-changed chart is the canonical morphism from the restricted thickening to `Z`, both being
the second projection of the same cartesian square. -/
theorem preimageChartIso_hom_chartToSpace (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1) :
    ((preimageChartIso C S hS Z hG U').hom ≫
        chartToSpace C S hS (IsThickening.space C S hS hG)
          ((thickeningChartBaseChange C S hS hG).obj U')).hom =
      Z.fromPreimage (chartToSpace C S hS X' U').hom :=
  preimageChartPresheafIso_hom_fst C S hS Z hG U'

/-- **The comparison is compatible with the inclusions into the chart space of `U'`.**  The
inclusion of the restricted thickening is the cartesian projection of the base-changed chart,
read through the comparison. -/
theorem preimageChartIso_inv_inclusion (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1) :
    ((preimageChartIso C S hS Z hG U').inv ≫
        IsThickening.inclusion C S hS
          (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG)).hom =
      yoneda.map ((isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.snd U'.1.hom) :=
  preimageChartPresheafIso_inv_ι C S hS Z hG U'

/-! ### The comparison over the space of the thickening -/

/-- **The comparison of `AlgebraicGeometry.Space.preimageChartIso`, read over the space of
`Z`.**  This is the form that a transport of a sheaf on the small étale site of `Z` consumes: the
restricted thickening of the chart space and the base-changed chart are the same object over `Z`,
not merely isomorphic algebraic spaces. -/
def preimageChartOverIso (hG : IsThickening C S hS X' Z) (U' : SmallEtale C S hS X'.1) :
    Over.mk (ObjectProperty.homMk (Z.fromPreimage (chartToSpace C S hS X' U').hom) :
        IsThickening.space C S hS
          (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG) ⟶
      IsThickening.space C S hS hG) ≅
      chartOver C S hS (IsThickening.space C S hS hG)
        ((thickeningChartBaseChange C S hS hG).obj U') :=
  Over.isoMk (preimageChartIso C S hS Z hG U')
    (ObjectProperty.hom_ext _ (preimageChartIso_hom_chartToSpace C S hS Z hG U'))

end AlgebraicGeometry.Space

end
