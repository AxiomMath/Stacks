module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The flat locus of a module under flat base change

Let a cartesian square of algebraic spaces over a scheme `S` of a big fppf site be given, with
`f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'` and `g' : X' ⟶ X`, and let `F` be an `𝒪_X`-module.
Stacks 05WW says that if `g` is flat and both `f` and `F` are locally of finite presentation,
then the locus of points of `|X'|` at which the inverse image `(g')^*F` is flat over `Y'` is the
inverse image, under `|g'| : |X'| ⟶ |X|`, of the open subset of Stacks 05WV — the locus of
points of `|X|` at which `F` is flat over `Y`.

Stacks 05WW itself, for a module of finite presentation on the small étale site and with no
hypothesis beyond the source's own, is
`flatLocus_modulePullback_eq_preimage_and_isOpen_of_isFinitePresentationOnSite`
of `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusBaseChangeFinitePresentation.lean`, which
uses the proved Stacks 05VW at a geometric point.  This file gives the same two statements for
a module whose quasi-coherence and finite presentation are read on the étale scheme charts, a
reading under which the comparison with geometric points is not available; there the module
form of Stacks 05VW at a point is an assumption of the statements.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatAtPointStableUnderBaseChange`: the assertion of Stacks 05VW
  at a point for modules quasi-coherent on the étale scheme charts.

## Main results

* `AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage`: the set equality of Stacks
  05WW for a module quasi-coherent on the charts, assuming that assertion.
* `AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage_and_isOpen`: the same, together
  with openness of the locus by Stacks 05WV.

## Stacks 05VW for modules quasi-coherent on the charts

The source proves Stacks 05WW by citing Stacks 05VW (Morphisms of Spaces, Lemma 67.31.3), which
for a cartesian square as above, a quasi-coherent `F` and a point `x'` of `|X'|` over
`x = |g'|(x')` asserts two implications:

1. if `F` is flat over `Y` at `x`, then `(g')^*F` is flat over `Y'` at `x'`;
2. if moreover `g` is flat at the point `|f'|(x')` of `|Y'|` and `(g')^*F` is flat over `Y'` at
   `x'`, then `F` is flat over `Y` at `x`.

Together they are exactly the two inclusions of Stacks 05WW, once flatness of `g` is read
pointwise.  Both implications *are* proved in this development for a module quasi-coherent on
the small étale site: part (1) is
`AlgebraicGeometry.Space.mem_flatLocus_modulePullback_of_mem_flatLocus` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChangePoint.lean`, and part (2) follows the
same way from `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback` through
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`.

What the assertion below asks for is weaker: it reads quasi-coherence *chartwise*, as
`AlgebraicGeometry.Space.IsQuasicoherentOnCharts`, which is the hypothesis the results of this
file take and of which the chart-free reading of the flat locus is not available — the passage
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite` runs the other way,
and no passage from the chartwise condition to the site condition exists.  So the assertion is
an assumption of the results here, as it is the field
`AlgebraicGeometry.Space.ModulePullbackStability.flat` of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFibered.lean` and as
`AlgebraicGeometry.Space.FlatnessSituation.IsFlatStableUnderBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalFlattening.lean`.  Following the last of these,
the assertion is a definition rather than a repeated quantifier block, and it carries no tag: it
states Stacks 05VW for chartwise quasi-coherent modules, it does not prove it.

It is quantified over all cartesian squares, modules and points, as the source lemma is, so the
cartesian square of the results below is consumed by it and nothing about flatness at a point
under base change is assumed beyond Stacks 05VW itself.

## Implementation notes

"`F` is flat over `Y` at `x`" is `AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR, the
some-chart form of flatness at a point of Stacks 05VV part (1), which is the locus Stacks 05WV
proves open in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusOpen.lean`; the hypotheses on `f` and `F`
are the ones that file consumes, `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` and the
chartwise `AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts`.  So the openness half is Stacks 05WV
verbatim, and all this file adds to it is that the locus on `|X'|` is the inverse image of that
open subset and hence open, the map on points being continuous by clause (2) of Stacks 03BX,
`AlgebraicGeometry.Space.continuous_pointsMap`.

The cartesian square is `CategoryTheory.IsPullback` on the underlying presheaves, as in
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback`, so that it is
independent of a chosen fibre product.  The inverse image of the module is
`AlgebraicGeometry.Space.modulePullback` of Stacks 03LU, at the module universe of the structure
rings.

`AlgebraicGeometry.Space.pointTopology` of Stacks 03BY is a plain definition rather than an
instance and is made a local instance here, as in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusOpen.lean`.

## References

* [Stacks Project, Tag 05WW](https://stacks.math.columbia.edu/tag/05WW)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 05VW at a point, for modules quasi-coherent on the charts -/

/-- The assertion of Stacks 05VW at a point, for modules quasi-coherent on the étale scheme
charts: in every cartesian square of algebraic spaces over `S` with `f : X ⟶ Y`,
`g : Y' ⟶ Y`, `f' : X' ⟶ Y'` and `g' : X' ⟶ X`, for every quasi-coherent `𝒪_X`-module `F`
and every point `x'` of `|X'|`,

1. if `F` is flat over `Y` at the image of `x'` in `|X|`, then the inverse image `(g')^*F` is
   flat over `Y'` at `x'`; and
2. if `g` is flat at the image of `x'` in `|Y'|` and `(g')^*F` is flat over `Y'` at `x'`, then
   `F` is flat over `Y` at the image of `x'` in `|X|`.

Flatness at a point is membership of `AlgebraicGeometry.Space.flatLocus`, the some-chart form of
Stacks 05VV part (1), and quasi-coherence is read on the étale scheme charts, as Stacks 05VU
and Stacks 0DLR do.

This states Stacks 05VW for chartwise quasi-coherent modules and does not prove it, so it
carries no tag.  Stacks 05VW at a point *is* proved for a module quasi-coherent on the small
étale site; it is the chartwise reading of quasi-coherence here that puts it out of reach.  See
the module docstring, also for the other places in the tree that use the same assertion. -/
def IsFlatAtPointStableUnderBaseChange : Prop :=
  ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X},
    IsPullback g'.hom f'.hom f.hom g.hom →
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsQuasicoherentOnCharts B S hS X.2 F →
        ∀ x' : points B S hS X'.1,
          (pointsMap B S hS X'.1 g'.hom x' ∈ flatLocus B S hS X.2 f.hom F →
              x' ∈ flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)) ∧
            (IsFlatAt B S hS g.hom (pointsMap B S hS X'.1 f'.hom x') →
              x' ∈ flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) →
                pointsMap B S hS X'.1 g'.hom x' ∈ flatLocus B S hS X.2 f.hom F)

/-! ### The flat locus of the base change -/

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- The set equality of Stacks 05WW for a module quasi-coherent on the étale scheme charts,
assuming Stacks 05VW at a point for such modules.  For a module of finite presentation on the
small étale site, where Stacks 05VW is proved, the equality needs no such assumption and is
`AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage_of_isFinitePresentationOnSite`.

In a cartesian square of algebraic spaces over `S` with
`f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'` and `g' : X' ⟶ X` whose base morphism `g` is flat,
the locus of points of `|X'|` at which the inverse image `(g')^*F` of a quasi-coherent
`𝒪_X`-module is flat over `Y'` is the inverse image under `|g'| : |X'| ⟶ |X|` of the locus of
points of `|X|` at which `F` is flat over `Y`.

Both inclusions are the two implications of Stacks 05VW at a point, the assumption `h05VW`: the
inclusion `⊆` is its second implication, flatness of `g` being read pointwise by Stacks 03MM
(`AlgebraicGeometry.Space.isFlat_iff_forall_isFlatAt`), and the inclusion `⊇` is its first.  The
finite-presentation hypotheses of Stacks 05WW are not needed for the equality; they are what
makes the right-hand side open, by Stacks 05WV, and are carried by
`AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage_and_isOpen`. -/
theorem flatLocus_modulePullback_eq_preimage
    (h05VW : IsFlatAtPointStableUnderBaseChange B S hS) {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : IsQuasicoherentOnCharts B S hS X.2 F)
    (hg : IsFlat B S hS g.hom) :
    flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' flatLocus B S hS X.2 f.hom F :=
  Set.ext fun x' =>
    ⟨fun hx' => (h05VW sq F hqc x').2
      ((isFlat_iff_forall_isFlatAt B S hS g.hom).1 hg _) hx',
     fun hx => (h05VW sq F hqc x').1 hx⟩

/-- Stacks 05WW for a module quasi-coherent of finite presentation on the étale scheme charts,
assuming Stacks 05VW at a point for such modules.  For a module of finite presentation on the
small étale site this is proved with no such assumption, as
`flatLocus_modulePullback_eq_preimage_and_isOpen_of_isFinitePresentationOnSite`.

Let a cartesian square of algebraic spaces over `S` be given, with
`f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'` and `g' : X' ⟶ X`.  Assume `g` is flat, `f` is
locally of finite presentation, and the `𝒪_X`-module `F` is quasi-coherent of finite
presentation on the étale scheme charts.  Then the locus of points of `|X'|` at which the
inverse image `(g')^*F` is flat over `Y'` is the inverse image under `|g'| : |X'| ⟶ |X|` of the
open subset of Stacks 05WV, and is therefore itself open.

The equality is `AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage`, which is where
the assumed Stacks 05VW and the flatness of `g` are used.  Openness of the subset of `|X|` is
Stacks 05WV, `AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`, which
is where the two finite-presentation hypotheses are used, and the map on points is continuous by
clause (2) of Stacks 03BX. -/
theorem flatLocus_modulePullback_eq_preimage_and_isOpen
    (h05VW : IsFlatAtPointStableUnderBaseChange B S hS) {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hg : IsFlat B S hS g.hom)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hqc : IsQuasicoherentOnCharts B S hS X.2 F)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) =
        pointsMap B S hS X'.1 g'.hom ⁻¹' flatLocus B S hS X.2 f.hom F ∧
      IsOpen (flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)) := by
  have heq := flatLocus_modulePullback_eq_preimage B S hS h05VW sq F hqc hg
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS X.2 f.hom F hf hqc hfp).preimage
    (continuous_pointsMap B S hS g'.hom)

end AlgebraicGeometry.Space

end
