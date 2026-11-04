module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.CompactFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.FlatnessAtRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecializationLift

/-!
# Flatness over a local base from flatness along the closed fibre

Let `S` be a local scheme with closed point `s`, let `f : X ⟶ S` be a morphism from an
algebraic space `X` to `S` which is locally of finite type and let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module. Stacks 0CWM says that `ℱ` is flat over `S` as soon as

1. every point of `Ass_{X/S}(ℱ)` specializes to a point of the closed fibre `X_s`, and
2. `ℱ` is flat over `S` at every point of `X_s`.

The source's proof is one line: by Stacks 0CWL it suffices to check flatness at the points of
the relative assassin, and at such a point the two hypotheses give it. Unwinding that line, the
argument at an arbitrary point `x` of `|X|` is: condition (2) of Stacks 0CWL asks for flatness
at the points `x'` of `Ass_{X/S}(ℱ)` lying in the fibre of `x` and specializing to `x`;
hypothesis (1) sends such an `x'` to a point `θ` of the closed fibre, hypothesis (2) makes `ℱ`
flat over `S` at `θ`, and relative flatness at a point passes to the generalizations of that
point, so `ℱ` is flat over `S` at `x'`. Theorem 0CWL then gives flatness at `x`, and a module
flat over the target at every point of `|X|` is flat over the target.

The step the source's proof invokes, the implication (2) ⇒ (1) of Stacks 0CWL, is a theorem of
this development:
`AlgebraicGeometry.Space.isFlatOverAtPoint_of_forall_isRelativeWeaklyAssociatedPoint`,
proved for arbitrary `X` and `Y` with no decency by reduction to a commuting square of étale
scheme charts over the *scheme* case More on Flatness Theorem 05UA (2) ⇒ (1), which is itself
proved, as `AlgebraicGeometry.isFlatOverAt_of_forall_mem_relativeAssassin_specializes`. It is
therefore applied directly below and is not a hypothesis.

The other step, that relative flatness at `θ` passes to the generalization `x'`, is proved here
for the points it is applied to, as
`AlgebraicGeometry.Space.isFlatOverAtPoint_of_specializes_of_isRelativeWeaklyAssociatedPoint`.
The two points lie over the distinct points `f(x')` and `s` of the base, so the same-fibre form
of the scheme case is not enough; but the scheme case holds at an arbitrary generalization,
`AlgebraicGeometry.isFlatOverAt_of_specializes_acrossFibres`, and what has to be done is to lift
`x' ⤳ θ` to an étale scheme chart. That is Decent Spaces, Lemma 03IL, and its only input is that
the chart fibre above `x'` is finite. Decency of `X` would give this at every point, but Stacks
0CWM does not assume it. At a point of `Ass_{X/S}(ℱ)` the finiteness holds as soon as the target is
decent, which a local scheme is. The chart points above `x'` lie in the relative assassin of the
chart morphism `U ⟶ V` (Stacks 0CUZ) over the finitely many points of the affine chart `V`
above `f(x')`. Above each such point that relative assassin is the set of associated points of a
coherent module on a Noetherian affine scheme, hence finite.

So nothing is carried, and `X` is not assumed decent anywhere in this file.

## Main results

* `AlgebraicGeometry.finite_relativeWeaklyAssociatedPoints_inter_preimage_singleton`: for a
  morphism locally of finite type between affine schemes, finitely many points of the relative
  weak assassin of a finite type quasi-coherent module lie over each point of the base.
* `AlgebraicGeometry.Space.finite_chartFibre_of_isRelativeWeaklyAssociatedPoint`: for a decent
  target, an affine chart diagram has finitely many chart points above a point of the relative
  assassin.
* `AlgebraicGeometry.Space.isFlatOverAtPoint_of_specializes_of_isRelativeWeaklyAssociatedPoint`:
  for a decent target, relative flatness passes from a point to every generalization of it in
  the relative assassin.
* `AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_fibre`: the implication of Stacks
  0CWM over an arbitrary decent algebraic space target and an arbitrary point of it.
* `AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_closedFibre`: **Stacks 0CWM**, at
  the source's own base — a local scheme with its closed point.
* `AlgebraicGeometry.Space.isFlatOver_of_isPureAbove_of_isAffineLocalAt`: the first example of
  the footnote of Stacks 0CWM — for `f` of finite type and decent, purity of `ℱ` above the
  closed point of a local base supplies hypothesis (1), so hypothesis (2) alone gives flatness
  of `ℱ` over `S`.

## Implementation notes

The relative assassin `Ass_{X/S}(ℱ)` is
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints` of Stacks 0CV0: for `f` locally of
finite type the fibres are locally Noetherian by Stacks 0CUY and the relative weak assassin is
the set the source writes `Ass_{X/S}(ℱ)`. Flatness over the target at a point is
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, Stacks 05VV at a point, and flatness over the
target is `AlgebraicGeometry.Space.IsFlatOver`, Stacks 05VV.

The locality of the base enters the tagged statement
`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_closedFibre` in one place: the target
is represented by a scheme of the site, so it is a decent space. Beyond that, once hypothesis
(1) is granted, the fibre over `s` plays no special role. This is why the argument is isolated
over an arbitrary decent target and base point as
`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_fibre`, and why the closedness of `s`
is not consumed. The full locality is used in the footnote: it is a hypothesis of
`AlgebraicGeometry.Space.purityFibreSpecialization`, the step which turns purity above `s` into
hypothesis (1), and so of
`AlgebraicGeometry.Space.isFlatOver_of_isPureAbove_of_isAffineLocalAt`. The local base is
spelled there as `AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt`, and in the tagged
statement by the same data written out: a scheme of the site isomorphic to the spectrum of a
local ring, representing the target.

The standing hypotheses of Stacks 0CWM — `f` locally of finite type, `ℱ` quasi-coherent and of
finite type — are consumed by Stacks 0CWL and by the finiteness of the chart fibres above points
of the relative assassin.

## References

* [Stacks Project, Tag 0CWM](https://stacks.math.columbia.edu/tag/0CWM)
* [Stacks Project, Tag 0CWL](https://stacks.math.columbia.edu/tag/0CWL)
* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.CoherentOfFiniteType in
/-- **Finitely many points of the relative weak assassin lie over a point of the base**, for a
morphism `q : U ⟶ V` locally of finite type between affine schemes and a quasi-coherent
`𝒪_U`-module `N` of finite type.

The relative weak assassin is the relative assassin here (Stacks 05F2), and its part over `v`
is the image of `Ass(N_v)` in the fibre `U_v`. That fibre is affine, since `q` is affine, and
locally Noetherian, being locally of finite type over the residue field of `v`; the restriction
`N_v` is quasi-coherent of finite type, so coherent (Stacks 01XZ), and a coherent module on a
Noetherian scheme has finitely many associated points (Stacks 05AF). -/
theorem finite_relativeWeaklyAssociatedPoints_inter_preimage_singleton
    {U V : Scheme.{u}} (q : U ⟶ V) [LocallyOfFiniteType q] [IsAffine U] [IsAffine V]
    (N : U.Modules) [N.IsQuasicoherent] [N.IsFiniteType] (v : V) :
    (relativeWeaklyAssociatedPoints q N ∩ q ⁻¹' {v}).Finite := by
  rw [relativeWeaklyAssociatedPoints_eq_relativeAssassin]
  have : IsLocallyNoetherian (q.fiber v) := by
    have hft : LocallyOfFiniteType (q.fiberToSpecResidueField v) := by
      show LocallyOfFiniteType (Limits.pullback.snd q (V.fromSpecResidueField v))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (q.fiberToSpecResidueField v)
  have : ((Scheme.Modules.pullback (q.fiberι v)).obj N).IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pullback (q.fiberι v)).obj N).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (q.fiberι v).toLRSHom.toShHom N
  have := isCoherent_of_isQuasicoherent_of_isFiniteType
    ((Scheme.Modules.pullback (q.fiberι v)).obj N)
  refine ((associatedPoints_finite ((Scheme.Modules.pullback (q.fiberι v)).obj N)).image
    (q.fiberι v)).subset ?_
  rintro w ⟨hw, hwv⟩
  obtain ⟨v', hv'⟩ := Set.mem_iUnion.1 hw
  obtain ⟨p, hp, rfl⟩ := hv'
  have : v' = v := by
    have h1 : q (q.fiberι v' p) ∈ ({v'} : Set V) := by
      have := (q.range_fiberι v').symm ▸ Set.mem_range_self (f := q.fiberι v') p
      exact this
    exact (Set.mem_singleton_iff.1 h1).symm.trans hwv
  subst this
  exact ⟨p, hp, rfl⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### The generalization step at a point of the relative assassin -/

/-- **The chart fibre above a point of the relative assassin is finite**, when the target is
decent. Let `f : X ⟶ Y` be locally of finite type with `Y` decent, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `x'` be a point of `WeakAss_{X/Y}(F)`. Then on the source
chart of a commuting square of étale scheme charts over `f` whose two charts are affine, only
finitely many points lie above `x'`.

Every chart point above `x'` lies in the relative weak assassin of the chart morphism
`q : U ⟶ V`, by the étale invariance of Stacks 0CUZ
(`AlgebraicGeometry.Space.mem_relativeWeaklyAssociatedPoints_chartDiagram`), and is sent by `q`
to a point of `V` above the image `t` of `x'` in `|Y|`. Decency of `Y` makes the affine étale
chart `V` have finitely many points above `t` (Stacks 03JV, (4) ⇒ (1)), and above each of them
`q` has finitely many relative weakly associated points
(`AlgebraicGeometry.finite_relativeWeaklyAssociatedPoints_inter_preimage_singleton`). -/
theorem finite_chartFibre_of_isRelativeWeaklyAssociatedPoint {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) (hYdec : IsDecentSpace B S hS Y.1)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x') :
    {w : chartScheme d.U | chartSchemeToPoints B S hS X.1 d.U w = x'}.Finite := by
  have := locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have : SheafOfModules.IsQuasicoherent (chartDiagramRestrictSource B S hS f F d) :=
    isQuasicoherent_restrictToChart B S hS X F hF d.U
  have : SheafOfModules.IsFiniteType (chartDiagramRestrictSource B S hS f F d) :=
    isFiniteType_restrictToChart B S hS X F hF hFft d.U
  set t := pointsMap B S hS X.1 f.hom x' with ht
  have hVt : {v : chartScheme d.V | chartSchemeToPoints B S hS Y.1 d.V v = t}.Finite := by
    have h := ((hYdec t).hasFiniteFibresOnEveryAffineEtaleChart B S hS Y.1 Y.2
      ((SmallEtale.toOver B S hS Y.1).obj d.V) hV d.V.obj.hom
      (isEtale_of_presheaf_etale B S hS d.V.property)).1
    refine (h.image (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj d.V))).subset ?_
    intro v hv
    refine ⟨(pointsEquivScheme B S hS _).symm v, ?_, Equiv.apply_symm_apply _ v⟩
    have hv' : chartSchemeToPoints B S hS Y.1 d.V v = t := hv
    rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm] at hv'
    exact hv'
  refine (hVt.biUnion fun v _ =>
    finite_relativeWeaklyAssociatedPoints_inter_preimage_singleton
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) v).subset ?_
  intro w hw
  have hw' : chartSchemeToPoints B S hS X.1 d.U w = x' := hw
  refine Set.mem_biUnion (x := chartDiagramSchemeMap B S hS f d w) ?_ ⟨?_, rfl⟩
  · show chartSchemeToPoints B S hS Y.1 d.V ((BigFppfOver.toScheme B S hS).map d.g w) = t
    rw [chartSchemeToPoints_chartDiagram, hw']
  · exact mem_relativeWeaklyAssociatedPoints_chartDiagram B S hS f F hF d w (hw' ▸ hx')

/-- **Relative flatness at a point passes to generalizations lying in the relative assassin**,
for a decent target. Let `f : X ⟶ Y` be locally of finite type with `Y` decent and let `F` be a
quasi-coherent `𝒪_X`-module of finite type. If `F` is flat over `Y` at a point `θ` of `|X|`,
then it is flat over `Y` at every point `x'` of `WeakAss_{X/Y}(F)` specializing to `θ`. No
relation between the images of `x'` and `θ` in `|Y|` is asked for, and `X` need not be decent.

This is the step the proof of Stacks 0CWM uses: its points `x'` lie in `Ass_{X/S}(F)` and
specialize to a point `θ` of the closed fibre. Lifting `x' ⤳ θ` to an étale scheme chart is
Decent Spaces, Lemma 03IL, whose only input is finiteness of the chart fibre above `x'`
(`AlgebraicGeometry.Space.exists_specializes_of_finite_chartFibre`). Decency of `X` would give
that at every point; at a point of the relative assassin it already follows from decency of the
target, by `AlgebraicGeometry.Space.finite_chartFibre_of_isRelativeWeaklyAssociatedPoint`. On
the chart the scheme case `AlgebraicGeometry.isFlatOverAt_of_specializes_acrossFibres` then
applies. -/
theorem isFlatOverAtPoint_of_specializes_of_isRelativeWeaklyAssociatedPoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) (hYdec : IsDecentSpace B S hS Y.1)
    {θ x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hflat : IsFlatOverAtPoint B S hS X.2 f.hom F θ) (hspec : x' ⤳ θ) :
    IsFlatOverAtPoint B S hS X.2 f.hom F x' := by
  have e : ∀ (U : SmallEtale B S hS X.1) (w : chartScheme U),
      pointOfEtaleChart B S hS U w = chartSchemeToPoints B S hS X.1 U w := fun U w =>
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 U w).symm
  obtain ⟨d₀, u₀, hu₀⟩ := exists_chartDiagram_pointOfEtaleChart B S hS X.2 Y.2 f.hom θ
  obtain ⟨W, a, ⟨hWaff, V, q, hq, hVaff⟩, u, hu⟩ :=
    exists_hasAffineChartDiagram B S hS f d₀.U u₀
  let d : ChartDiagram B S hS X.1 Y.1 f.hom := { U := W, V := V, g := q, comm := hq.symm }
  have hθ : pointOfEtaleChart B S hS d.U u = θ := by
    calc pointOfEtaleChart B S hS d.U u = chartSchemeToPoints B S hS X.1 W u := e _ _
      _ = chartSchemeToPoints B S hS X.1 d₀.U
          ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) u) :=
        (chartSchemeToPoints_map B S hS X.1 a u).symm
      _ = chartSchemeToPoints B S hS X.1 d₀.U u₀ := by rw [hu]
      _ = θ := (e _ _).symm.trans hu₀
  have hNqc : SheafOfModules.IsQuasicoherent (chartDiagramRestrictSource B S hS f F d) :=
    isQuasicoherent_restrictToChart B S hS X F hF d.U
  have hflatu : IsFlatOverAtOnChartDiagram B S hS X.2 F d u :=
    (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d u).1
      (by rw [hθ]; exact hflat)
  have hfin := finite_chartFibre_of_isRelativeWeaklyAssociatedPoint f hf F hF hFft hYdec d
    hWaff hVaff hx'
  have hfin' : (chartFibre B S hS X.1 d.U.obj.hom x').Finite := by
    refine (hfin.image (pointsEquivScheme B S hS d.U.obj.left).symm).subset ?_
    intro p hp
    refine ⟨pointsEquivScheme B S hS d.U.obj.left p, ?_, Equiv.symm_apply_apply _ p⟩
    show chartSchemeToPoints B S hS X.1 d.U _ = x'
    rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
    exact ((pointsEquivScheme B S hS d.U.obj.left).symm_apply_apply p).symm ▸ hp
  obtain ⟨p', hp'spec, hp'img⟩ := exists_specializes_of_finite_chartFibre B S hS X.1 hspec
    d.U.obj.hom d.U.property hfin' (p := (pointsEquivScheme B S hS d.U.obj.left).symm u) hθ
  obtain ⟨u', hu'eq⟩ : ∃ u' : etaleChartScheme B S hS d.U,
      (pointsEquivScheme B S hS d.U.obj.left).symm u' = p' :=
    ⟨pointsEquivScheme B S hS d.U.obj.left p',
      (pointsEquivScheme B S hS d.U.obj.left).symm_apply_apply p'⟩
  have hu'pt : pointOfEtaleChart B S hS d.U u' = x' := by
    rw [pointOfEtaleChart, hu'eq]; exact hp'img
  have hu'spec : u' ⤳ u := by
    have h := hp'spec.map (schemePointsHomeomorph B S hS d.U.obj.left).continuous
    have e1 : (schemePointsHomeomorph B S hS d.U.obj.left) p' = u' := by
      rw [← hu'eq]; exact (pointsEquivScheme B S hS d.U.obj.left).apply_symm_apply u'
    have e2 : (schemePointsHomeomorph B S hS d.U.obj.left)
        ((pointsEquivScheme B S hS d.U.obj.left).symm u) = u :=
      (pointsEquivScheme B S hS d.U.obj.left).apply_symm_apply u
    rw [e1, e2] at h
    exact h
  have key : IsFlatOverAt (chartDiagramSchemeMap B S hS f d).toLRSHom.toShHom
      (chartDiagramRestrictSource B S hS f F d) u' :=
    @isFlatOverAt_of_specializes_acrossFibres _ _ (chartDiagramSchemeMap B S hS f d)
      (chartDiagramRestrictSource B S hS f F d) hNqc u u' hu'spec hflatu
  rw [← hu'pt]
  exact (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F hF d u').2 key

/-! ### The implication of Stacks 0CWM -/

/-- **The implication of Stacks 0CWM over an arbitrary decent base and base point.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces which is locally of finite type, with `Y` decent,
let `F` be a finite type quasi-coherent `𝒪_X`-module and let `y` be a point of `|Y|`. If every
point of `Ass_{X/Y}(F)` specializes to a point of the fibre `X_y` and `F` is flat over `Y` at
every point of `X_y`, then `F` is flat over `Y`.

`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_closedFibre` is the source's
statement, at a local base and its closed point; a local scheme is a decent space, so it is this
one. Decency of `Y` is what makes relative flatness pass from a point `θ` of the fibre to a
point of the relative assassin specializing to it
(`AlgebraicGeometry.Space.isFlatOverAtPoint_of_specializes_of_isRelativeWeaklyAssociatedPoint`);
`X` need not be decent. -/
theorem isFlatOver_of_forall_specializes_fibre {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (y : points B S hS Y.1)
    (hlft : IsLocallyOfFiniteType B S hS f.hom) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (hYdec : IsDecentSpace B S hS Y.1)
    (hass : ∀ x' ∈ relativeWeaklyAssociatedPoints B S hS f F,
      ∃ θ : points B S hS X.1, x' ⤳ θ ∧ pointsMap B S hS X.1 f.hom θ = y)
    (hflat : ∀ θ : points B S hS X.1, pointsMap B S hS X.1 f.hom θ = y →
      IsFlatOverAtPoint B S hS X.2 f.hom F θ) :
    IsFlatOver B S hS X.2 f.hom F := by
  refine isFlatOver_of_forall_isFlatOverAtPoint B S hS f F hqc fun x => ?_
  refine isFlatOverAtPoint_of_forall_isRelativeWeaklyAssociatedPoint B S hS f hlft F hqc hft x
    fun x' _ hx' _ => ?_
  obtain ⟨θ, hspec, hθ⟩ := hass x' hx'
  exact isFlatOverAtPoint_of_specializes_of_isRelativeWeaklyAssociatedPoint f hlft F hqc hft
    hYdec hx' (hflat θ hθ) hspec

/-- **Stacks Project, Tag 0CWM.** Let `S` be a local scheme with closed point `s`, read as the
target `Y` of a morphism of algebraic spaces: the target is represented by a scheme of the site
isomorphic to the spectrum of a local ring, and `s` is a closed point of `|Y|`. Let
`f : X ⟶ Y` be locally of finite type and let `F` be a finite type quasi-coherent
`𝒪_X`-module. Assume

1. every point of `Ass_{X/S}(F)` specializes to a point of the closed fibre `X_s` (`hass`),
   and
2. `F` is flat over `S` at every point of `X_s` (`hflat`).

Then `F` is flat over `S`.

The conclusion is the tag's, with no clause dropped and nothing carried. The representability
of the target in `hlocal` is consumed: a representable algebraic space is decent, which is what
`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_fibre` asks of the target. The
closedness of `s` is a hypothesis of the tag that the implication does not use. -/
@[stacks 0CWM "the lemma's implication: from its hypotheses (1) and (2) to flatness of ℱ over \
the local base. UNCONDITIONAL -- nothing is carried and no decency of X is assumed: the step \
the source's proof invokes, the implication (2) => (1) of Stacks 0CWL, is proved here for \
arbitrary X and Y as isFlatOverAtPoint_of_forall_isRelativeWeaklyAssociatedPoint, and the \
passage of flatness from a point of the closed fibre to a point of Ass_{X/S}(F) specializing \
to it is proved here as isFlatOverAtPoint_of_specializes_of_isRelativeWeaklyAssociatedPoint, \
using only that the local base is a decent space. The closedness of s is a hypothesis of the \
statement that the implication does not use"]
theorem isFlatOver_of_forall_specializes_closedFibre {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (s : points B S hS Y.1)
    (hlocal : ∃ (T : BigFppfOver B S hS) (A : CommRingCat.{u}), IsLocalRing A ∧
      Nonempty (Spec A ≅ (BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (yoneda.obj T ≅ Y.1))
    (_hs : IsClosed ({s} : Set (points B S hS Y.1)))
    (hlft : IsLocallyOfFiniteType B S hS f.hom) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hass : ∀ x' ∈ relativeWeaklyAssociatedPoints B S hS f F,
      ∃ θ : points B S hS X.1, x' ⤳ θ ∧ pointsMap B S hS X.1 f.hom θ = s)
    (hflat : ∀ θ : points B S hS X.1, pointsMap B S hS X.1 f.hom θ = s →
      IsFlatOverAtPoint B S hS X.2 f.hom F θ) :
    IsFlatOver B S hS X.2 f.hom F := by
  obtain ⟨T, -, -, -, ⟨e⟩⟩ := hlocal
  exact isFlatOver_of_forall_specializes_fibre f F s hlft hqc hft
    (isDecentSpace_of_iso B S hS e (isDecentSpace_yoneda B S hS T)) hass hflat

/-! ### The footnote: purity above the closed point supplies hypothesis (1) -/

/-- **The first example of the footnote of Stacks 0CWM.** In a pre-pure situation — `f` of
finite type and decent, `ℱ` finite type and quasi-coherent — over a base which is affine local
with closed point `y`, purity of `ℱ` above `y` is enough: hypothesis (1) of Stacks 0CWM is then
automatic, so flatness of `ℱ` over the base at every point of the closed fibre already gives
flatness of `ℱ` over the base.

Hypothesis (1) comes from `AlgebraicGeometry.Space.purityFibreSpecialization`, the
specialization step of Stacks 0CW3 clause (2), which is proved; the rest is
`AlgebraicGeometry.Space.isFlatOver_of_forall_specializes_fibre`, whose decency hypothesis on
the target holds because the affine local base is represented by a scheme of the site. -/
theorem isFlatOver_of_isPureAbove_of_isAffineLocalAt (P : PrePureSituation.{u, u} B S hS)
    (hlocal : P.IsAffineLocalAt) (hpure : IsPureAbove P)
    (hflat : ∀ θ : points B S hS P.X, pointsMap B S hS P.X P.f θ = P.y →
      IsFlatOverAtPoint B S hS P.hX P.f P.F θ) :
    IsFlatOver B S hS P.hX P.f P.F := by
  obtain ⟨T, -, -, -, ⟨e⟩⟩ := hlocal.1
  exact isFlatOver_of_forall_specializes_fibre P.structureSpaceMorphism P.F P.y
    P.finiteType.1 P.moduleQuasicoherent P.moduleFiniteType
    (isDecentSpace_of_iso B S hS e (isDecentSpace_yoneda B S hS T))
    (purityFibreSpecialization P hlocal hpure) hflat

end AlgebraicGeometry.Space

end
