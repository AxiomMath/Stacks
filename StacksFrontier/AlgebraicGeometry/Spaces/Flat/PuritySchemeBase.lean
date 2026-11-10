module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Specializing a relative weakly associated point into a flat fibre, over a scheme base

Let `X` be a decent algebraic space over a scheme `S` of a big fppf site, let `f : X ⟶ h_V` be a
morphism locally of finite type into the algebraic space of a scheme `V` of the site, let `F` be
a finite type quasi-coherent `𝒪_X`-module and let `s` be a point of `|h_V|` at which `F` is flat
over `h_V` at every point of the fibre `X_s`.  A point of the relative weak assassin
`WeakAss_{X/V}(F)` whose closure meets `|X_s|` specializes to a point of `WeakAss_{X/V}(F)`
lying over `s`.

This is **Stacks 0CW1 at the source's own generality**: the base of the source's lemma is a
scheme, and the set it is about is the relative weak assassin of the structure morphism to it.
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_isFlatOver`
carries the same statement for an arbitrary algebraic space target, granting the criterion of
Stacks 05L3 on an étale scheme chart; here the target is represented, and that criterion is
proved rather than granted.

## Main results

* `AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`:
  **Stacks 0CW1** for a morphism into the algebraic space of a scheme of the site.

## Implementation notes

The proof is the source's: choose an affine étale scheme chart `a : h_U ⟶ X` through a point `t`
of `|X_s|` in the closure of `x'`, with `u` above `t`, and descend everything to `U`.

* Yoneda fullness factors `a ≫ f` through a morphism `α : U ⟶ V` of the site, so the chart and
  the identity chart of `V` form a commuting square of étale scheme charts of `f`,
  `AlgebraicGeometry.Space.etaleChartDiagramOfFactorization`.  Its vertical morphism of schemes
  is locally of finite type, by
  `AlgebraicGeometry.Space.locallyOfFiniteType_chartDiagram`, and the restriction of `F` to the
  source chart is a quasi-coherent module of finite type on it.
* The relative weak assassin of Stacks 0CV0 for `h_α` and the pullback `a^* F` is, read through
  the comparison of Stacks 03BV, the scheme-level relative weak assassin of Stacks 05AV of that
  restriction: this is
  `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints`,
  which asks only that `a^* F` be quasi-coherent, transported along the identifications
  `AlgebraicGeometry.Space.restrictToChartIsoRepresentedZariskiRestrictionPullback` of the chart
  restriction of `F` with the represented comparison of `a^* F` and
  `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` of the two readings of that
  comparison, by `AlgebraicGeometry.relativeWeaklyAssociatedPoints_congr`.
* Decency lifts the specialization `x' ⤳ t` to a specialization `u' ⤳ u` in `|h_U|` with `u'`
  above `x'` (Stacks 03IL), and the relative weak assassin is the preimage of the relative weak
  assassin along the étale `a` (Stacks 0CUZ), so `u'` lies in `WeakAss_{h_U/h_V}(a^* F)` and
  hence, through the comparison, in the scheme-level relative weak assassin on `U`.
* The flatness hypothesis is read on the chart by the chart independence of Stacks 05VU, in the
  form `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram`, at the square
  above; a point of the scheme-theoretic fibre of `α` over the point of `V` underlying `s` cuts
  out a point of `|X|` lying over `s`, so the hypothesis applies there.
* Stacks 05L3 on `α` then produces the point, and the comparison carries it back.

The point of `V` underlying `s` is used through the injectivity of the comparison of
Stacks 03BV, `AlgebraicGeometry.Space.injective_pointsToScheme`: an identity of points of `|h_V|`
is checked on `V`.  Specializations are transported between `|h_U|` and `U` along the
homeomorphism of Stacks 03BX, `AlgebraicGeometry.Space.schemePointsHomeomorph`.

The two private lemmas below exist to keep the two halves apart.  The first is Stacks 05L3 with
its fibre points eliminated, stated for the relative weak assassin of Stacks 05AV rather than
the relative assassin, which is the same set here by Stacks 05F2; it is purely about schemes.
The second is the compatibility of the comparison of Stacks 03BV with the factorization, which
is the one computation the descent needs and is stated in term mode: the Yoneda spelling
`yoneda.obj V` of the target and the spelling `(schemeSpace V).obj` it carries in the main
statement are definitionally but not reducibly equal, so a `rw` through it fails on motive
type-correctness.

## References

* [Stacks Project, Lemma 77.6.1 (Tag 0CW1)](https://stacks.math.columbia.edu/tag/0CW1)
* [Stacks Project, Tag 05L3](https://stacks.math.columbia.edu/tag/05L3)
* [Stacks Project, Tag 03IL](https://stacks.math.columbia.edu/tag/03IL)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **Stacks 05L3 with its fibre points eliminated.** For `g : P ⟶ Q` locally of finite type and
`N` a quasi-coherent `𝒪_P`-module of finite type which is flat over `Q` at every point of the
fibre over `q`, a point of the relative weak assassin `WeakAss_{P/Q}(N)` of Stacks 05AV which
specializes to a point of `P` above `q` specializes to a point of `WeakAss_{P/Q}(N)` above `q`.

The relative weak assassin is the relative assassin, by Stacks 05F2, and a point of the fibre
over `q` is associated to the fibre module exactly when its image lies in the relative assassin,
so this is Stacks 05L3 with the passages to and from the scheme-theoretic fibre performed. -/
private theorem exists_specializes_mem_relativeWeaklyAssociatedPoints {P Q : Scheme.{u}}
    (g : P ⟶ Q) (hg : LocallyOfFiniteType g) (N : P.Modules) (hqc : N.IsQuasicoherent)
    (hft : N.IsFiniteType) (q : Q)
    (hflat : ∀ z : g.fiber q, AlgebraicGeometry.IsFlatOverAt
      (LocallyRingedSpace.forgetToSheafedSpace.map g.toLRSHom) N (g.fiberι q z))
    {p' p : P} (hp' : p' ∈ _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints g N)
    (hspec : p' ⤳ p) (hp : g p = q) :
    ∃ y : P, p' ⤳ y ∧ g y = q ∧
      y ∈ _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints g N := by
  have := hg
  have := hqc
  have := hft
  rw [_root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin] at hp' ⊢
  obtain ⟨z, hz⟩ : p ∈ Set.range (g.fiberι q) := by
    rw [g.range_fiberι q]
    exact hp
  obtain ⟨x₀, hx₀spec, hx₀ass⟩ :=
    Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre g N q hflat hp'
      ⟨z, by rw [hz]; exact hspec⟩
  exact ⟨g.fiberι q x₀, hx₀spec, g.apply_fiberι q x₀,
    (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin g N q x₀).1 hx₀ass⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of Stacks 03BV against a factorization of `f` through an étale scheme
chart.** If `a : h_U ⟶ X` is a scheme chart of `X` and `α : U ⟶ V` is a morphism of the site
with `a ≫ f = h_α`, then the point of `V` underlying the image under `|f|` of the point of `|X|`
cut out by a point `p` of `|h_U|` is the image under `α` of the point of `U` underlying `p`. -/
private theorem toScheme_map_pointsToScheme_chart {V : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X.1) (α : U ⟶ V)
    (hαmap : (a ≫ f.hom : yoneda.obj U ⟶ yoneda.obj V) = yoneda.map α)
    (p : points B S hS (yoneda.obj U)) :
    (BigFppfOver.toScheme B S hS).map α (pointsToScheme B S hS U p) =
      pointsToScheme B S hS V
        (pointsMap B S hS X.1 f.hom (pointsMap B S hS (yoneda.obj U) a p)) :=
  (pointsToScheme_pointsMap B S hS α p).symm.trans
    (congrArg (pointsToScheme B S hS V)
      ((congrArg (fun m : yoneda.obj U ⟶ yoneda.obj V =>
            pointsMap B S hS (yoneda.obj U) m p) hαmap).symm.trans
        (congrFun (pointsMap_comp B S hS (yoneda.obj U) a f.hom) p)))

/-- **Stacks 0CW1.** Let `X` be a decent algebraic space over a scheme `S` of a big fppf site,
let `f : X ⟶ h_V` be a morphism locally of finite type into the algebraic space of a scheme `V`
of the site, let `F` be a finite type quasi-coherent `𝒪_X`-module, and let `s` be a point of
`|h_V|` such that `F` is flat over `h_V` at every point of the fibre `X_s`. If a point `x'` of
the relative weak assassin `WeakAss_{X/V}(F)` specializes to a point of `X_s` — that is, if the
closure of `{x'}` in `|X|` meets `|X_s|` — then it specializes to a point of `WeakAss_{X/V}(F)`
lying over `s`, so that closure meets `WeakAss_{X/V}(F) ∩ |X_s|`.

The source's `Ass_{X/S}(ℱ)` is the relative weak assassin of Stacks 0CV0, which it writes that
way because a morphism locally of finite type has locally Noetherian fibres (Stacks 0CUY); its
flatness hypothesis "`ℱ` is flat over `S` at all points of `X_s`" is flatness of the *module*
over the target at the points of the fibre, which is
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, Stacks 05VV at a point.

The two companions in `StacksFrontier/AlgebraicGeometry/Spaces/Flat/PuritySpecialization.lean`
generalize the base to an arbitrary algebraic space and carry the chart criterion as a
hypothesis; neither of them is registered against this tag, which is registered here. -/
@[stacks 0CW1 "the source's own statement, unconditionally: the base is a scheme of the site \
(the source's S), flatness is read on the module, Stacks 05VV at a point, exactly as the source \
reads it, and nothing further is required of the data -- in particular no affineness, the \
affine etale chart being chosen inside the proof as the source chooses it"]
theorem exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase
    (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    (hXdec : IsDecentSpace B S hS X.1) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite F] (s : points B S hS (schemeSpace V).1)
    (hflat : ∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s →
      IsFlatOverAtPoint B S hS X.2 f.hom F t)
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hmeets : ∃ t : points B S hS X.1, x' ⤳ t ∧ pointsMap B S hS X.1 f.hom t = s) :
    ∃ x : points B S hS X.1, x' ⤳ x ∧ pointsMap B S hS X.1 f.hom x = s ∧
      IsRelativeWeaklyAssociatedPoint B S hS f F x := by
  obtain ⟨t, hspec, hts⟩ := hmeets
  -- An étale scheme chart of `X` through `t`, taken affine as the source takes it.
  obtain ⟨U, a, -, haps, u, hau⟩ := exists_affine_etale_chart_at_point B S hS X.1 X.2 t
  have ha : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 haps
  -- Yoneda fullness factors `a ≫ f` through a morphism of the site.
  obtain ⟨α, hαmap⟩ :
      ∃ α : U ⟶ V, (a ≫ f.hom : yoneda.obj U ⟶ yoneda.obj V) = yoneda.map α :=
    ⟨yoneda.preimage (a ≫ f.hom : yoneda.obj U ⟶ yoneda.obj V),
      (yoneda.map_preimage _).symm⟩
  have hgα : (ObjectProperty.homMk a ≫ f : schemeSpace U ⟶ schemeSpace V) =
      schemeSpaceMap α := ObjectProperty.hom_ext _ hαmap
  -- The scheme-level data on the chart.
  have hαft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    locallyOfFiniteType_chartDiagram B S hS hf
      (etaleChartDiagramOfFactorization B S hS f a ha α hαmap)
  have hNqc : (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha)).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F inferInstance (etaleChartOfIsEtale B S hS a ha)
  have hNft : (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha)).IsFiniteType :=
    isFiniteType_restrictToChart B S hS X F inferInstance inferInstance
      (etaleChartOfIsEtale B S hS a ha)
  -- The comparison of the two relative weak assassins on the chart.
  have hGqc : ((modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X) ha F inferInstance
  have hchart : _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α)
        (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha)) =
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α)
        (representedChartModule B S hS
          ((modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj F)) :=
    _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints_congr
      ((BigFppfOver.toScheme B S hS).map α)
      (restrictToChartIsoRepresentedZariskiRestrictionPullback B S hS a ha F inferInstance ≪≫
        restrictToChartIsoRestrictToChartScheme B S hS
          (isAlgebraicSpace_yoneda B S hS U) _ (selfChart B S hS U))
  have hbridge : ∀ w : points B S hS (yoneda.obj U),
      IsRelativeWeaklyAssociatedPoint B S hS
          (ObjectProperty.homMk a ≫ f : schemeSpace U ⟶ schemeSpace V)
          ((modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj F) w ↔
        pointsToScheme B S hS U w ∈
          _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
            ((BigFppfOver.toScheme B S hS).map α)
            (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha)) := fun w => by
    rw [hchart, hgα]
    exact isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints B S hS α _
      hGqc w
  -- Lift the specialization `x' ⤳ t` to the chart, by decency.
  obtain ⟨u', hu'spec, hu'x⟩ := exists_specialization_lift_of_isDecentSpace B S hS X.1 X.2
    hXdec t x' hspec U a haps u hau
  -- Transport the relative weak assassin to the chart, and across the comparison.
  have hu'mem : pointsToScheme B S hS U u' ∈
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α)
        (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha)) :=
    (hbridge u').1 ((isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X) ha f F u').2 (by
      change IsRelativeWeaklyAssociatedPoint B S hS f F (pointsMap B S hS (yoneda.obj U) a u')
      rw [hu'x]
      exact hx'))
  -- A point of `U` over the point of `V` underlying `s` cuts out a point of `|X|` over `s`.
  have hoverpt : ∀ w : (BigFppfOver.toScheme B S hS).obj U,
      (BigFppfOver.toScheme B S hS).map α w = pointsToScheme B S hS V s →
      IsFlatOverAtPoint B S hS X.2 f.hom F
        (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm w)) := by
    intro w hw
    refine hflat _ (injective_pointsToScheme B S hS V ?_)
    have e2 : pointsToScheme B S hS U ((pointsEquivScheme B S hS U).symm w) = w :=
      (pointsEquivScheme B S hS U).apply_symm_apply w
    refine (toScheme_map_pointsToScheme_chart B S hS f a α hαmap
      ((pointsEquivScheme B S hS U).symm w)).symm.trans ?_
    rw [e2]
    exact hw
  -- The flatness hypothesis of Stacks 05L3, by the chart independence of Stacks 05VU.
  have hflat' : ∀ z : ((BigFppfOver.toScheme B S hS).map α).fiber
      (pointsToScheme B S hS V s), AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map α).toLRSHom)
        (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha))
        (((BigFppfOver.toScheme B S hS).map α).fiberι (pointsToScheme B S hS V s) z) :=
    fun z => (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f F inferInstance
        (etaleChartDiagramOfFactorization B S hS f a ha α hαmap) _).1
      (hoverpt _ (((BigFppfOver.toScheme B S hS).map α).apply_fiberι _ z))
  -- The chart point `u` lies over the point of `V` underlying `s`.
  have huover : (BigFppfOver.toScheme B S hS).map α (pointsToScheme B S hS U u) =
      pointsToScheme B S hS V s :=
    (toScheme_map_pointsToScheme_chart B S hS f a α hαmap u).trans
      (congrArg (pointsToScheme B S hS V)
        ((congrArg (pointsMap B S hS X.1 f.hom) hau).trans hts))
  have hcoe : ((schemePointsHomeomorph B S hS U) :
      points B S hS (yoneda.obj U) → (BigFppfOver.toScheme B S hS).obj U) =
      pointsToScheme B S hS U := rfl
  have hspecU : pointsToScheme B S hS U u' ⤳ pointsToScheme B S hS U u := by
    have h := hu'spec.map (schemePointsHomeomorph B S hS U).continuous
    rwa [hcoe] at h
  -- Stacks 05L3 on the chart.
  obtain ⟨y, hyspec, hyover, hymem⟩ :=
    exists_specializes_mem_relativeWeaklyAssociatedPoints ((BigFppfOver.toScheme B S hS).map α)
      hαft (restrictToChart B S hS X.2 F (etaleChartOfIsEtale B S hS a ha)) hNqc hNft
      (pointsToScheme B S hS V s) hflat' hu'mem hspecU huover
  obtain ⟨v₀, hv₀⟩ := surjective_pointsToScheme B S hS U y
  have hspecv : u' ⤳ v₀ := by
    refine (schemePointsHomeomorph B S hS U).isEmbedding.isInducing.specializes_iff.1 ?_
    rw [hcoe, hv₀]
    exact hyspec
  refine ⟨pointsMap B S hS (yoneda.obj U) a v₀, ?_, ?_, ?_⟩
  · have h := hspecv.map (continuous_pointsMap B S hS a)
    rwa [hu'x] at h
  · refine injective_pointsToScheme B S hS V ?_
    refine (toScheme_map_pointsToScheme_chart B S hS f a α hαmap v₀).symm.trans ?_
    rw [hv₀]
    exact hyover
  · refine (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X) ha f F v₀).1 ((hbridge v₀).2 ?_)
    rw [hv₀]
    exact hymem

end AlgebraicGeometry.Space

end
