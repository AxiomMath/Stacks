module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjGeneral.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative homogeneous spectrum of a quasi-coherent graded algebra, assembled

Situation 01NN fixes a scheme `S` together with a quasi-coherent, commutative, nonnegatively
graded `𝒪_S`-algebra. Tag 01NQ asserts that the projective spectra of its graded rings of
sections over the affine opens of `S` glue to a scheme over `S`, with each chart the inverse
image of its affine open and the charts for nested affine opens related by the canonical
morphism induced by restriction of sections. Tag 01NO is the statement about one such nested
pair: the induced morphism of projective spectra is defined everywhere, and the square it forms
with the two structure morphisms and the inclusion of the affine opens is cartesian.

Both assertions were available only as quantifications over data with no instance. This file
assembles them over `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, the
library form of Situation 01NN's sheaf-level input, whose graded rings of sections and their
restriction maps are *constructed* in `RelativeProjBridge` rather than selected from an
existence statement.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen`: the structure morphism of the
  chart over an affine open of the base, to that affine open.
* `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap`: the morphism of projective
  spectra induced by restriction along an arbitrary inclusion of affine opens.
* `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`: the glued scheme, its structure
  morphism, and compatible projective-spectrum charts on every affine open.
* `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`: **Tag 01NQ.** That datum, built.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.projInclusionDomain_eq_top`: **Tag 01NO, the
  everywhere-defined morphism.**
* `Stacks.AlgebraicGeometry.RelativeProj.projInclusion_isPullback`: **Tag 01NO, the
  cartesian square.**

## How the five components are assembled

`RelativeProjData` has five fields, and each is a single library result applied to
`SheafGradedAlgebra.toGradedAlgebra`, the bridge from the sheaf-level input to the
affine-open-wise graded algebra that the glueing consumes.

* `scheme` is `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj`, the colimit of the chart
  functor on the small affine Zariski site of `S`.
* `toBase` is `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProjToBase`, the morphism the
  relative glueing datum produces.
* `chart` is `Stacks.AlgebraicGeometry.RelativeProjGlue.chart`, the colimit inclusion. An affine
  open of `S` presented as an open together with a proof of affineness is read as an object of
  `AlgebraicGeometry.Scheme.AffineZariskiSite`, which is by definition that pair.
* `chart_isPullback` is `Stacks.AlgebraicGeometry.RelativeProjGlue.isPullback_chart`, flipped:
  that statement puts the chart's structure morphism first and the chart second, and the
  transpose of a cartesian square is cartesian.
* `chart_transition` is
  `Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_comp_chart_of_le_opens`, which is the
  compatibility for an *arbitrary* inclusion of affine opens; the glueing itself only gives it
  for the basic open inclusions, which are the arrows of the site.

The two results of Tag 01NO are
`Stacks.AlgebraicGeometry.RelativeProjGeneral.mapDomain_res_eq_top_of_le_opens` and
`Stacks.AlgebraicGeometry.RelativeProjGeneral.isPullback_transition_of_le_opens`, at the same
generality, with `projInclusionMap` the transition morphism of the bridged algebra.

## Implementation notes

**Everywhere-definedness is not what makes the morphism exist.** The morphism of projective
spectra used here is the one defined on
`Stacks.AlgebraicGeometry.ProjShared.mapDomain`, the exact open where a general graded ring
homomorphism induces a morphism, restricted along the isomorphism that
`mapDomain = ⊤` provides. It is *not* obtained from Mathlib's `AlgebraicGeometry.Proj.map`
by way of everywhere-definedness: `mapDomain = ⊤` is equivalent only to the inclusion of the
irrelevant ideal in the **radical** of the image of the irrelevant ideal
(`Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_iff_irrelevant_le_radical`), while
Mathlib asks for the plain inclusion, and the gap is strict. Everything below that needs the
plain inclusion goes through
`Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens` instead.

**Universes.** Monomorphic in the scheme universe `u`, forced on both sides and not a narrowing
of the source. `SheafOfModules.IsQuasicoherent` is stated for module sheaves in the universe of
the base ring sheaf, so the homogeneous pieces and hence the graded rings of sections live in
`Type u`; and `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra S` records those rings in
`CommRingCat.{u}`, which is what the glueing consumes. The glued scheme is a `Scheme.{u}`.

**Transparency.** `AlgebraicGeometry.Scheme.AffineZariskiSite` is a `def` for the subtype of
affine opens, so the pair of an open and a proof of its affineness is written as an anonymous
constructor at an ascribed type at each occurrence, and the inclusion of opens is passed to the
library lemmas by the named arguments `U` and `V` rather than left to be inferred from the type
of the inclusion proof — the two sites objects cannot be recovered from `U ≤ V` alone.
`projInclusionToOpen` and `projInclusionMap` are semireducible `def`s mirroring the source's own
definitions; the library statements are transferred onto them by `exact`, which unfolds them,
rather than by rewriting.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)

## Not done here

Tag 01NO labels four assertions and only its first two are here. The comparison maps on the
twisting sheaves `𝒪(n)` of a projective spectrum *are* constructed — `θ` is
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, bundled in `projMapData` — and `θ` *is*
an **isomorphism** for the restriction between affine opens:
`Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_res_of_le_opens`, and at the type
Tag 01NO itself gives the comparison, along `projInclusionMap` rather than along
`Stacks.AlgebraicGeometry.ProjShared.mapHom`, it is
`Stacks.AlgebraicGeometry.ProjInclusionTwist.isIso_projInclusionTwistMap`. Its route is
not the base change `A(U) = A(V) ⊗_{𝒪(V)} 𝒪(U)` but local and pointwise, through
`Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_of_inputs`. What is still missing for
the twist assertions is the compatibility of `θ` with the multiplication maps
`𝒪(n) ⊗ 𝒪(m) → 𝒪(n + m)` and with the unit, so the clause that the comparison is a map of
graded algebras is untouched. The relative
`𝒪(n)` of Tag 01NP is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist` (`Morphism/Twist.lean`), the homogeneous
pieces of the twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` builds from the graded
algebra alone. Tag 01NP's
transitivity of the transitions is proved in
`StacksFrontier.AlgebraicGeometry.RelativeProjGeneral.Basic` and is not restated here.

Nothing is said about quasi-compactness, separatedness or properness of the structure morphism
of the relative homogeneous spectrum, nor about the case of a graded algebra generated in degree
one, nor about uniqueness of the datum `relativeProj` constructs.

No project tag is attached to any declaration in this file.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProj

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### Tag 01NO: an inclusion of affine opens of the base -/

/-- **Tag 01NO, the everywhere-defined morphism.** For an inclusion `U ⊆ V` of affine opens of
the base, the morphism of projective spectra induced by restriction of homogeneous sections is
defined on all of `Proj Γ(U, A)`.

This is `Stacks.AlgebraicGeometry.RelativeProjGeneral.mapDomain_res_eq_top_of_le_opens` for the
graded algebra the bridge produces. -/
@[stacks 01NO "the everywhere-defined morphism"]
public theorem projInclusionDomain_eq_top (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    mapDomain (A.grading V) (A.grading U) (A.res h) = ⊤ :=
  RelativeProjGeneral.mapDomain_res_eq_top_of_le_opens A.toGradedAlgebra
    (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h

/-- The structure morphism of the chart over an affine open `U` of the base, to `U` itself:
`Proj` of the graded ring of sections over `U` maps to the spectrum of its degree-zero part,
hence to `U` through the structure map and the canonical identification of `U` with the spectrum
of its ring of functions. -/
public def projInclusionToOpen (U : S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.Proj (A.grading U) ⟶ U.toScheme :=
  A.toGradedAlgebra.toOpen ⟨U, hU⟩

/-- The morphism of projective spectra induced by restriction of homogeneous sections along an
inclusion `U ⊆ V` of affine opens of the base, read on the whole of `Proj Γ(U, A)` through
`projInclusionDomain_eq_top`. -/
public def projInclusionMap (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    AlgebraicGeometry.Proj (A.grading U) ⟶ AlgebraicGeometry.Proj (A.grading V) :=
  A.toGradedAlgebra.transition (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h
    (projInclusionDomain_eq_top A U V h hU hV)

/-- **Tag 01NO, the cartesian square.** For an inclusion `U ⊆ V` of affine opens of the base,
the square formed by the induced morphism of projective spectra, the two structure morphisms to
the affine opens and the inclusion `U ⊆ V` is cartesian.

This is `Stacks.AlgebraicGeometry.RelativeProjGeneral.isPullback_transition_of_le_opens` for the
graded algebra the bridge produces. -/
@[stacks 01NO "the cartesian square"]
public theorem projInclusion_isPullback (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPullback (projInclusionMap A U V h hU hV) (projInclusionToOpen A U hU)
      (projInclusionToOpen A V hV) (S.homOfLE h) :=
  RelativeProjGeneral.isPullback_transition_of_le_opens A.toGradedAlgebra
    (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h _

/-! ### Tag 01NQ: the relative homogeneous spectrum -/

/-- A scheme over the base carrying projective-spectrum charts on all affine opens, each chart
being the inverse image of its affine open and the transition between the charts of a nested
pair being the canonical morphism induced by restriction of sections.

The chart condition is recorded as a cartesian square rather than as an isomorphism onto a
preimage, which is the same assertion and is the form the glueing produces. -/
public structure RelativeProjData where
  /-- The relative homogeneous spectrum. -/
  scheme : Scheme.{u}
  /-- Its structure morphism to the base. -/
  toBase : scheme ⟶ S
  /-- The chart over an affine open of the base. -/
  chart (U : S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.Proj (A.grading U) ⟶ scheme
  /-- Each chart is the inverse image of its affine open. -/
  chart_isPullback (U : S.Opens) (hU : IsAffineOpen U) :
    IsPullback (chart U hU) (projInclusionToOpen A U hU) toBase U.ι
  /-- The charts are compatible with the morphisms induced by restriction. -/
  chart_transition (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap A U V h hU hV ≫ chart V hV = chart U hU

/-- **Tag 01NQ.** The relative homogeneous spectrum of a quasi-coherent graded algebra on a
scheme, together with its structure morphism to the base and its canonical affine charts.

The scheme is the colimit of the chart functor on the small affine Zariski site of the base; the
chart over an affine open is the colimit inclusion, and it is cartesian over that affine open
because the relative glueing datum's squares are. Compatibility of the charts with the
transitions holds for the arrows of the site by the defining equation of the colimit, and for an
arbitrary inclusion of affine opens by
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_comp_chart_of_le_opens`. -/
@[stacks 01NQ, ega "II 3.1.2" "existence", ega "II 8.3.1"]
public def relativeProj : RelativeProjData A where
  scheme := RelativeProjGlue.relativeProj A.toGradedAlgebra
  toBase := RelativeProjGlue.relativeProjToBase A.toGradedAlgebra
  chart U hU := RelativeProjGlue.chart A.toGradedAlgebra ⟨U, hU⟩
  chart_isPullback U hU := (RelativeProjGlue.isPullback_chart A.toGradedAlgebra ⟨U, hU⟩).flip
  chart_transition U V h hU hV :=
    RelativeProjGeneral.transition_comp_chart_of_le_opens A.toGradedAlgebra
      (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h _

end Stacks.AlgebraicGeometry.RelativeProj

end
