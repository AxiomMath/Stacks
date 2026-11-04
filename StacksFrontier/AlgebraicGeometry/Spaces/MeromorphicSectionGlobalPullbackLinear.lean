module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramSieveRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
import StacksCore.Tactic.StacksAttribute

/-!
# The global pullback of meromorphic sections is additive and semilinear

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules.  The
global map

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

of Stacks 0ENC, part (1) — `AlgebraicGeometry.Space.pullbackMeromorphicSection` — is built on the
underlying sets of the sheaves of meromorphic sections, and its construction asserts nothing
about the algebra.  This file proves that it is **additive** and **semilinear over the pullback
of meromorphic functions**: the pullback of a sum of meromorphic sections is the sum of the
pullbacks, and if `s = c · s'` with `c` a meromorphic function on a chart of `Y`, then
`f^*s = (f^♯c) · f^*s'` over the chart of `X` above it.

Both come from the one formula available for the map,
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram`, which computes it over a
commuting square of étale charts on which the section is an honest element of
`M ⊗_{𝒪_Y} 𝒦_Y`.  The chartwise rule `m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` is additive and carries a
coefficient `c` to `f^♯c` (`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_smul`),
and the sheafification map of Stacks 0EN5 over a chart is additive and linear
(`AlgebraicGeometry.Space.toMeromorphicSectionSheaf_add` and
`AlgebraicGeometry.Space.toMeromorphicSectionSheaf_smul`), so the identities hold over every
square over which the sections are presented.  Those squares cover: the presentation exists over
a covering sieve of the chart of `Y`
(`AlgebraicGeometry.Space.exists_eval_toMeromorphicSectionSheaf_sieve_mem`), the sieve is base
changed to a covering family of the chart of `X`
(`AlgebraicGeometry.Space.exists_affine_chartDiagram_cover_of_sieve`), and the sheaf
`𝒦_X(f^*M)` is separated.

## Main results

* `AlgebraicGeometry.Space.toMeromorphicSectionSheaf_add`: the sheafification map of
  Stacks 0EN5 over a chart is additive.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_smul`: the chartwise pullback
  of meromorphic sections is semilinear over the chartwise pullback of meromorphic functions.
* `AlgebraicGeometry.Space.meromorphicSectionSheaf_eq_of_cover`: two sections of the sheaf of
  meromorphic sections over a chart agreeing over a covering family of it are equal.
* `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add_chartDiagram` and
  `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add`: **the global pullback map of
  Stacks 0ENC, part (1) is additive**, over the chart of `X` of an affine commuting square and
  then over every chart of `X`.
* `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_smul_chartDiagram`: **the global
  pullback map of Stacks 0ENC, part (1) is semilinear** over the chartwise pullback of
  meromorphic functions.

## Implementation notes

The statements are *pointwise*: a meromorphic section is a section of a sheaf of modules, a type
on which no module structure is registered, so "the pullback of `s + s'`" is spelled through a
meromorphic section `w` whose value over every chart is the sum of the values of `s` and `s'`,
and "`c · s'`" as a relation between values over a chart.

Semilinearity is stated over a commuting square of *affine* étale charts, with the coefficient
`AlgebraicGeometry.Space.chartMeromorphicPullbackHom` of that square, and not over every chart of
`X` with a single global coefficient: pulling a meromorphic function back is a chartwise
operation, the global map `Γ(Y, 𝒦_Y) ⟶ Γ(X, 𝒦_X)` on meromorphic functions not being available,
and the refinement of a square along a covering sieve of its chart of `Y`
(`AlgebraicGeometry.Space.exists_affine_chartDiagram_cover_of_sieve`) — which is what keeps the
coefficient in sight — needs the two charts affine.  Additivity has no coefficient, so there the
square can be eliminated: every chart of `X` is covered by the charts of `X` of affine squares
(`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`).

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sheafification map of Stacks 0EN5 over a chart is additive.**  The section of the
sheaf `𝒦_F(M)` that a sum `t + t'` of meromorphic sections over a chart becomes is the sum of
the sections that `t` and `t'` become.

As for `AlgebraicGeometry.Space.toMeromorphicSectionSheaf_smul`, the map is the component at the
chart of a morphism of presheaves of modules. -/
theorem toMeromorphicSectionSheaf_add
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (t t' : (meromorphicSectionModule B S hS F hF M).obj (op V)) :
    toMeromorphicSectionSheaf B S hS F hF M V (t + t') =
      toMeromorphicSectionSheaf B S hS F hF M V t +
        toMeromorphicSectionSheaf B S hS F hF M V t' := by
  let := moduleHasWeakSheafify.{u, u} B S hS F
  let := moduleWEqualsLocallyBijective.{u, u} B S hS F
  let : Presheaf.IsLocallyInjective (meromorphicRingedSite B S hS F hF).J
      (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
        (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf) :=
    ((meromorphicRingedSite B S hS F hF).J.W_toSheafify _).isLocallyInjective
  let : Presheaf.IsLocallySurjective (meromorphicRingedSite B S hS F hF).J
      (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
        (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf) :=
    ((meromorphicRingedSite B S hS F hF).J.W_toSheafify _).isLocallySurjective
  exact map_add (((PresheafOfModules.toSheafify
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)
    (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
      (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf)).app (op V)).hom)
    (ULift.up t) (ULift.up t')

/-- **The sheaf of meromorphic sections is separated.**  Two sections of the sheaf `𝒦_F(M)` of
Stacks 0EN5 over an étale chart whose restrictions to the members of a covering family of that
chart agree are equal. -/
theorem meromorphicSectionSheaf_eq_of_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    {I : Type w} (W : I → SmallEtale B S hS F) (a : ∀ i, W i ⟶ V)
    (hcov : Sieve.ofArrows W a ∈ SmallEtale.topology B S hS F V)
    (x y : (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.obj (op V))
    (h : ∀ i, ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map (a i).op).hom x =
      ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map (a i).op).hom y) :
    x = y := by
  set LP := (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.presheaf ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1} with hLP
  have hLsheaf : Presheaf.IsSheaf (SmallEtale.topology B S hS F) LP :=
    GrothendieckTopology.HasSheafCompose.isSheaf _
      (meromorphicSectionSheaf.{u, u} B S hS F hF M).isSheaf
  refine ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS F) LP).1 hLsheaf
    (Sieve.ofArrows W a) hcov).isSeparatedFor.ext ?_
  rintro Z g ⟨Z', p, q, ⟨i⟩, rfl⟩
  have hcomp : ∀ z : (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.obj (op V),
      ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map (p ≫ a i).op).hom z =
        ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map p.op).hom
          (((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map (a i).op).hom z) := fun z ↦ by
    rw [op_comp, PresheafOfModules.map_comp_apply]
  show ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map (p ≫ a i).op).hom x =
    ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map (p ≫ a i).op).hom y
  rw [hcomp, hcomp, h i]

/-- The value of a meromorphic section over a chart is the restriction of its value over a larger
chart. -/
private theorem map_eval_meromorphicSection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) (v : MeromorphicSection.{u, u} B S hS F hF M)
    {Z V : SmallEtale B S hS F} (g : Z ⟶ V) :
    ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map g.op).hom (v.eval (op V)) =
      v.eval (op Z) :=
  PresheafOfModules.sections_property v g.op

/-- If `t` becomes the restriction of the value of `v` over `V` to `Z`, then `t` is the value of
`v` over `Z`. -/
private theorem eval_eq_toMeromorphicSectionSheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) (v : MeromorphicSection.{u, u} B S hS F hF M)
    {Z V : SmallEtale B S hS F} (g : Z ⟶ V)
    {t : (meromorphicSectionModule B S hS F hF M).obj (op Z)}
    (ht : toMeromorphicSectionSheaf B S hS F hF M Z t =
      ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map g.op).hom (v.eval (op V))) :
    v.eval (op Z) = toMeromorphicSectionSheaf B S hS F hF M Z t :=
  (ht.trans (map_eval_meromorphicSection B S hS F hF M v g)).symm

section Linear

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
  (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- **The chartwise pullback of meromorphic functions at the ringed-site spelling of the ring of
meromorphic functions.**  `AlgebraicGeometry.Space.chartMeromorphicPullbackHom` lands in
`(meromorphicChartSheaf …).obj.obj (op d.U)`, while the multiplication on the sections of the
sheaf `𝒦_X(f^*M)` of meromorphic sections is by an element of
`(Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite …).O).obj.obj (op d.U)`.  Both are
the sections of `𝒦` over the chart carried into `RingCat` by the same forgetful functor, but only
after unfolding `AlgebraicGeometry.Space.meromorphicFunctionSheaf`, which the elaboration of `•`
does not do.

This is the same ring homomorphism at the second spelling, as
`AlgebraicGeometry.Space.chartMeromorphicPullbackHom` is at the first and
`AlgebraicGeometry.Space.meromorphicSectionModuleRingedSiteModule` is for the module
structure. -/
noncomputable abbrev chartMeromorphicRingedSitePullbackHom
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.obj
        (op d.V) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj
        (op d.U) :=
  chartMeromorphicPullbackHom B S hS f hf d

/-- The value of the pullback of a meromorphic section over a chart is the restriction of its
value over a larger chart. -/
private theorem map_eval_pullback {Z V : SmallEtale B S hS X.1} (g : Z ⟶ V)
    (v : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M) :
    ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2
        ((modulePullback B S hS f).obj M)).val.map g.op).hom
      ((pullbackMeromorphicSection B S hS f M hf v).eval (op V)) =
        (pullbackMeromorphicSection B S hS f M hf v).eval (op Z) :=
  map_eval_meromorphicSection B S hS X.1 X.2 _ _ g

/-- **The chartwise pullback of meromorphic sections is semilinear.**  The chartwise rule
`m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` carries `r · t` to `(f^♯r) ·` the pullback of `t`, with `f^♯` the
chartwise pullback of meromorphic functions.

This is the semilinearity of the universal map out of a tensor product,
`Stacks.PresheafOfModules.ChangeOfRings.tmulMap_smul`, at the square of coefficient rings
`AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_algebraMap`. -/
theorem chartPullbackMeromorphicSectionsSheaf_smul
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.obj
      (op d.V))
    (t : (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op d.V)) :
    chartPullbackMeromorphicSectionsSheaf B S hS f M hf d (r • t) =
      chartMeromorphicRingedSitePullbackHom B S hS f hf d r •
        chartPullbackMeromorphicSectionsSheaf B S hS f M hf d t :=
  tmulMap_smul (chartRing B S hS Y.1 Y.2 d.V)
    ((meromorphicChartSheaf B S hS Y.1 Y.2).obj.obj (op d.V))
    (chartRing B S hS X.1 X.2 d.U)
    ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op d.U))
    (chartDiagramRestrict B S hS f d)
    (chartMeromorphicPullbackHom B S hS f hf d)
    (chartMeromorphicFunctionPullback_algebraMap B S hS f hf d)
    (M.val.obj (op d.V)) (((modulePullback B S hS f).obj M).val.obj (op d.U))
    (chartNumeratorPullback B S hS f M d) (chartNumeratorPullback_smul B S hS f M d) r t

/-- **The global pullback map of Stacks 0ENC, part (1) is additive over the chart of `X` of an
affine commuting square.**  Let `d` be a commuting square of affine étale scheme charts, `d.U` of
`X` above `d.V` of `Y`, and let `w` be a meromorphic section of `M` whose value over `d.V` is the
sum of the values of `s` and `s'` there.  Then the value of the pullback of `w` over `d.U` is the
sum of the values of the pullbacks of `s` and `s'`.

Over a covering family of `d.U` refining the sieve over which `s` and `s'` are both honest
elements of `M ⊗_{𝒪_Y} 𝒦_Y`, the three values are computed by
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram` and the identity is the
additivity of the chartwise rule; the sheaf of meromorphic sections is separated. -/
theorem pullbackMeromorphicSection_eval_add_chartDiagram
    (s s' w : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj d.U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)))
    (hw : w.eval (op d.V) = s.eval (op d.V) + s'.eval (op d.V)) :
    (pullbackMeromorphicSection B S hS f M hf w).eval (op d.U) =
      (pullbackMeromorphicSection B S hS f M hf s).eval (op d.U) +
        (pullbackMeromorphicSection B S hS f M hf s').eval (op d.U) := by
  obtain ⟨Ts, hTs, hTsrep⟩ := exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS Y.1 Y.2 M
    d.V (s.eval (op d.V))
  obtain ⟨Ts', hTs', hTs'rep⟩ := exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS Y.1 Y.2 M
    d.V (s'.eval (op d.V))
  obtain ⟨n, d', a, κ, -, -, hκ, -, hcov⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d hU hV
      ((SmallEtale.topology B S hS Y.1).intersection_covering hTs hTs')
  refine meromorphicSectionSheaf_eq_of_cover B S hS X.1 X.2
    ((modulePullback B S hS f).obj M) d.U (fun i ↦ (d' i).U) a hcov _ _ fun i ↦ ?_
  obtain ⟨ts, hts⟩ := hTsrep (κ i) (hκ i).1
  obtain ⟨ts', hts'⟩ := hTs'rep (κ i) (hκ i).2
  have hsV := eval_eq_toMeromorphicSectionSheaf B S hS Y.1 Y.2 M s (κ i) hts
  have hs'V := eval_eq_toMeromorphicSectionSheaf B S hS Y.1 Y.2 M s' (κ i) hts'
  have hwV : w.eval (op (d' i).V) =
      toMeromorphicSectionSheaf B S hS Y.1 Y.2 M (d' i).V (ts + ts') := by
    rw [← map_eval_meromorphicSection B S hS Y.1 Y.2 M w (κ i), hw, map_add, ← hts, ← hts']
    exact (toMeromorphicSectionSheaf_add B S hS Y.1 Y.2 M (d' i).V ts ts').symm
  have hres := map_eval_pullback B S hS f M hf (a i)
  rw [map_add, hres, hres, hres,
    pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf w (d' i) (ts + ts') hwV,
    pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf s (d' i) ts hsV,
    pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf s' (d' i) ts' hs'V,
    map_add]
  exact toMeromorphicSectionSheaf_add B S hS X.1 X.2 ((modulePullback B S hS f).obj M) (d' i).U
    (chartPullbackMeromorphicSectionsSheaf B S hS f M hf (d' i) ts)
    (chartPullbackMeromorphicSectionsSheaf B S hS f M hf (d' i) ts')

/-- **The global pullback map of Stacks 0ENC, part (1) is additive.**  Let `w` be a meromorphic
section of `M` whose value over every étale scheme chart of `Y` is the sum of the values of `s`
and `s'` there.  Then the value of the pullback of `w` over every étale scheme chart of `X` is
the sum of the values of the pullbacks of `s` and `s'`.

A meromorphic section is a section of a sheaf of modules, a type carrying no module structure, so
this is the assertion that the global map of part (1) is additive.

Every chart of `X` is covered by the charts of `X` of affine commuting squares
(`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`), over which the identity is
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add_chartDiagram`. -/
@[stacks 0ENC "the algebra of the part (1) map, which its construction leaves unasserted: \
the global map on meromorphic sections is additive"]
theorem pullbackMeromorphicSection_eval_add
    (s s' w : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (hw : ∀ V : SmallEtale B S hS Y.1, w.eval (op V) = s.eval (op V) + s'.eval (op V))
    (U : SmallEtale B S hS X.1) :
    (pullbackMeromorphicSection B S hS f M hf w).eval (op U) =
      (pullbackMeromorphicSection B S hS f M hf s).eval (op U) +
        (pullbackMeromorphicSection B S hS f M hf s').eval (op U) := by
  obtain ⟨I, W, a, d, hdU, hUaff, hVaff, hcov⟩ := exists_affine_chartDiagram_ofArrows B S hS f U
  refine meromorphicSectionSheaf_eq_of_cover B S hS X.1 X.2
    ((modulePullback B S hS f).obj M) U W a hcov _ _ fun i ↦ ?_
  have key := pullbackMeromorphicSection_eval_add_chartDiagram B S hS f M hf s s' w (d i)
    (by rw [hdU i]; exact hUaff i) (hVaff i) (hw (d i).V)
  rw [hdU i] at key
  have hres := map_eval_pullback B S hS f M hf (a i)
  rw [map_add, hres, hres, hres]
  exact key

/-- **The global pullback map of Stacks 0ENC, part (1) is semilinear over the chartwise pullback
of meromorphic functions.**  Let `d` be a commuting square of affine étale scheme charts, `d.U`
of `X` above `d.V` of `Y`, let `c` be a meromorphic function on `d.V` and let the meromorphic
sections `s` and `s'` of `M` satisfy `s|_{d.V} = c · s'|_{d.V}`.  Then over `d.U`

`(f^*s)|_{d.U} = (f^♯c) · (f^*s')|_{d.U}`,

with `f^♯` the chartwise pullback of meromorphic functions
`AlgebraicGeometry.Space.chartMeromorphicPullbackHom`.

Over a covering family of `d.U` refining the sieve over which `s'` is an honest element of
`M ⊗_{𝒪_Y} 𝒦_Y` both values are computed by
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram`, and the identity is that
the chartwise rule carries a coefficient to its pullback. -/
@[stacks 0ENC "the algebra of the part (1) map, which its construction leaves unasserted: \
the global map on meromorphic sections is semilinear over the chartwise pullback of \
meromorphic functions. The coefficient over the chart of X of a commuting square of affine \
etale charts is the image of the coefficient over its chart of Y under \
AlgebraicGeometry.Space.chartMeromorphicPullbackHom; a single coefficient over all of X would \
need the global map on meromorphic functions, which is not available"]
theorem pullbackMeromorphicSection_eval_smul_chartDiagram
    (s s' : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj d.U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)))
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.obj
      (op d.V))
    (hc : s.eval (op d.V) = c • s'.eval (op d.V)) :
    (pullbackMeromorphicSection B S hS f M hf s).eval (op d.U) =
      chartMeromorphicRingedSitePullbackHom B S hS f hf d c •
        (pullbackMeromorphicSection B S hS f M hf s').eval (op d.U) := by
  obtain ⟨Ts', hTs', hTs'rep⟩ := exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS Y.1 Y.2 M
    d.V (s'.eval (op d.V))
  obtain ⟨n, d', a, κ, -, -, hκ, hcomm, hcov⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d hU hV hTs'
  refine meromorphicSectionSheaf_eq_of_cover B S hS X.1 X.2
    ((modulePullback B S hS f).obj M) d.U (fun i ↦ (d' i).U) a hcov _ _ fun i ↦ ?_
  obtain ⟨ts', hts'⟩ := hTs'rep (κ i) (hκ i)
  have hs'V := eval_eq_toMeromorphicSectionSheaf B S hS Y.1 Y.2 M s' (κ i) hts'
  have hsV : s.eval (op (d' i).V) =
      toMeromorphicSectionSheaf B S hS Y.1 Y.2 M (d' i).V
        (((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map
          (κ i).op c) • ts') := by
    rw [toMeromorphicSectionSheaf_smul, ← hs'V,
      ← map_eval_meromorphicSection B S hS Y.1 Y.2 M s (κ i), hc]
    exact meromorphicSectionSheaf_map_smul_eval B S hS Y.1 Y.2 M s' (κ i) c
  have hcoeff : chartMeromorphicRingedSitePullbackHom B S hS f hf (d' i)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map
          (κ i).op c) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj.map
        (a i).op
        (chartMeromorphicRingedSitePullbackHom B S hS f hf d c) :=
    chartMeromorphicFunctionPullback_comp B S hS f hf d (d' i) (a i) (κ i) (hcomm i) c
  rw [meromorphicSectionSheaf_map_smul_eval B S hS X.1 X.2 ((modulePullback B S hS f).obj M)
      (pullbackMeromorphicSection B S hS f M hf s') (a i)
      (chartMeromorphicRingedSitePullbackHom B S hS f hf d c),
    map_eval_pullback B S hS f M hf (a i),
    pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf s (d' i) _ hsV,
    pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf s' (d' i) ts' hs'V,
    chartPullbackMeromorphicSectionsSheaf_smul, toMeromorphicSectionSheaf_smul, hcoeff]

end Linear

end AlgebraicGeometry.Space

end
