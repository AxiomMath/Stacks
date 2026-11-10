module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Affineness of a morphism descends to a stage of a limit of bases, under the chapter's convention

In Situation 70.6.1 of the source (tag 084W), carried by
`AlgebraicGeometry.Space.MorphismDescentSituation`, Lemma 70.6.3 (tag 084Y) says that if the
base change `f : X ⟶ Y` of `f₀` to the limit `B` is affine, then the base change
`f_i : X_i ⟶ Y_i` to some stage `B_i` is affine.

The source's proof: choose an affine scheme `V₀` and a surjective étale morphism `V₀ ⟶ Y₀`, and
set `V_i = V₀ ×_{Y₀} Y_i` and `V = V₀ ×_{Y₀} Y`. Since `f` is affine, `V ×_Y X` is affine; it is
the limit of the `V_i ×_{Y_i} X_i`, so by Stacks 07SQ some `V_i ×_{Y_i} X_i` is affine, and then
`f_i` is affine by Stacks 03WG.

The chapter works under the convention of its Section 70.2 (tag 07SD) that every ring considered
has its spectrum in the big fppf site. For the system of bases this is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, and it is the one hypothesis of the
results here beyond those of the situation; the source's two appeals to other lemmas, Stacks
07SF for the affineness of `B ⟶ B₀` and Stacks 07SQ for the system `V_i ×_{Y_i} X_i`, are made
under it.

## Main results

All in the namespace `AlgebraicGeometry.Space.MorphismDescentSituation`:

* `isAffineHom_limit_π_initial_of_siteContainsBaseChangeLimits`: Stacks 07SF, part (1), for the
  projection `B ⟶ B₀`.
* `siteContainsBaseChangeLimits_stagesBaseChangeSystem`: the convention holds for every system
  `B_i ×_{B₀} T`, in particular for `V_i ×_{Y_i} X_i`.
* `isAffineSpace_limitBaseChange_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits`:
  if `f` is affine then `V ×_Y X` is affine.
* `exists_isAffineHom_mapAt_of_descentAffineStage_of_siteContainsBaseChangeLimits`: the geometry
  of Stacks 084Y with Stacks 07SQ, over the convention, as a parameter.
* `exists_isAffineHom_mapAt_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits`:
  **Stacks 084Y**, the preceding theorem with its parameter discharged by Stacks 07SQ over the
  convention,
  `DescentSituation.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits`.

## Implementation notes

*Why the convention is needed.* It cannot be dropped from the statement. Let `k` be a prime
field, let `K` be a field extension of `k` whose cardinality is at least the size cutoff of the
site, written as the directed union of its subfields `K_i` finitely generated over `k`, and let
`B_i = Spec K_i`, `B₀ = Y₀ = Spec k`, `X₀ = ℙ¹_k` and `f₀` the structure morphism. A morphism
from a nonempty scheme of the site to `Spec K` would embed `K` in the ring of functions of a
nonempty affine open of that scheme, which is smaller than the cutoff; so the limit of the `B_i`
in presheaves on the site is represented by the empty scheme, `f` is an isomorphism and hence
affine, and yet no `f_i : ℙ¹_{K_i} ⟶ Spec K_i` is affine. This system satisfies every
hypothesis of the situation and fails the convention: the limit of the `B_i` is `Spec K`, which
is not in the site.

*Which fibre product.* `B_i ×_{B₀} (X₀ ×_{Y₀} V₀)` and `V_i ×_{Y_i} X_i` are the same object, the
limit of `B_i ⟶ B₀ ⟵ X₀ ⟶ Y₀ ⟵ V₀`. The first spelling is the one in which the stages form the
descent situation
`AlgebraicGeometry.Space.MorphismDescentSituation.stagesBaseChangeDescentSituation` that Stacks
07SQ is applied to, so it is the one used.

## References

* [Stacks Project, Tag 084Y](https://stacks.math.columbia.edu/tag/084Y)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_AffineMorphismDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, found directly from `HasPullbacks`. -/
local instance (priority := high) hasPullback_presheaf_AffineMorphismDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 07SF, part (1), at the distinguished stage, under the chapter's convention.** The
projection `B ⟶ B₀` from the limit of the system of bases is affine. -/
theorem isAffineHom_limit_π_initial_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) :
    IsAffineHom B S hS (limit.π D.base (op D.initial)) :=
  have := D.isCofiltered_op
  isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D.base hconv D.transition_affine _

/-- **The chapter's convention passes to the system `B_i ×_{B₀} T`**, the restriction of the
system of bases to the stages at or beyond the distinguished one, base changed along
`t : T ⟶ B₀`. -/
theorem siteContainsBaseChangeLimits_stagesBaseChangeSystem
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : T ⟶ D.base.obj (op D.initial)) :
    SiteContainsBaseChangeLimits B S hS (D.stagesBaseChangeSystem t) :=
  (hconv.comp_subtypeGe D.initial).baseChangeOverSystem (stagesBaseToInitial D) t

section Chart

variable {V₀ : BigFppfOver B S hS} (v : yoneda.obj V₀ ⟶ D.target₀)

/-- **The chart `V = V₀ ×_{Y₀} Y` of the target over the limit is affine, under the chapter's
convention.** It is the base change of the affine object `V₀` along the projection `B ⟶ B₀`. -/
theorem isAffineSpace_limitChartTarget_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)) :
    IsAffineSpace B S hS (pullback (limit.π D.base (op D.initial)) (v ≫ D.targetToBase)) := by
  obtain ⟨W, p, q, hpb⟩ :=
    D.isAffineHom_limit_π_initial_of_siteContainsBaseChangeLimits hconv ⟨V₀, hV₀⟩
      (v ≫ D.targetToBase)
  exact ⟨W.obj, W.property, ⟨hpb.isoPullback.symm⟩⟩

/-- **The limit `V ×_Y X` of the system of charts is affine when `f` is, under the chapter's
convention.** The projection `V ×_Y X ⟶ V` is the base change of `f` along `V ⟶ Y`, hence
affine, and `V` is affine. -/
theorem isAffineSpace_limitBaseChange_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (hf : IsAffineHom B S hS D.mapLimit) :
    IsAffineSpace B S hS
      (pullback (limit.π D.base (op D.initial)) (pullback.fst D.map₀ v ≫ D.sourceToBase)) :=
  isAffineSpace_source_of_isAffineHom
    (isAffineHom_of_isPullback (D.isPullback_chartSquare v (limit.π D.base (op D.initial))) hf)
    (D.isAffineSpace_limitChartTarget_of_siteContainsBaseChangeLimits v hconv hV₀)

end Chart

/-- **Stacks 084Y given Stacks 07SQ, under the chapter's convention.** In Situation 70.6.1, if
the base change `f` of `f₀` to the limit is affine then its base change `f_i` to some stage is
affine, for any statement `hstage` of Stacks 07SQ over the convention: an inverse system of
quasi-compact quasi-separated algebraic spaces with affine transition morphisms satisfying the
convention, whose limit is affine, has an affine stage.

Everything else in the source's proof is carried out: the affine étale surjective chart
`V₀ ⟶ Y₀`, the descent situation of the `V_i ×_{Y_i} X_i = B_i ×_{B₀} (X₀ ×_{Y₀} V₀)` and the
convention for it, affineness of its limit `V ×_Y X`, and the concluding appeal to Stacks 03WG,
`isAffineHom_mapAt_of_isAffineSpace_baseChange`. -/
theorem exists_isAffineHom_mapAt_of_descentAffineStage_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hstage : ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
      (E : DescentSituation B S hS hZ J), SiteContainsBaseChangeLimits B S hS E.system →
      IsAffineSpace B S hS E.limitCone.pt →
      ∃ j : J, E.base ≤ j ∧ IsAffineSpace B S hS (E.system.obj (op j)))
    (hf : IsAffineHom B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsAffineHom B S hS (D.mapAt i hi) := by
  -- an affine étale surjective chart `V₀ ⟶ Y₀` of the quasi-compact target
  obtain ⟨V₀, v, hV₀, hvSurj, hvEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀
      D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  -- the chart `T = X₀ ×_{Y₀} V₀` of the source is a quasi-compact quasi-separated algebraic
  -- space over the distinguished stage
  have hValg := isAlgebraicSpace_yoneda B S hS V₀
  have hTalg : IsAlgebraicSpace B S hS (D.chartSource v) :=
    isAlgebraicSpace_pullback B S hS D.map₀ v
      D.source₀_isAlgebraicSpace hValg D.target₀_isAlgebraicSpace
  have hTqc : IsQuasiCompactSpace B S hS (D.chartSource v) :=
    isQuasiCompactSpace_pullback B S hS hZ D.map₀ v
      D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace D.source₀_quasiCompact
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀) D.target₀_quasiSeparated
  have hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.chartSource v) :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ v
      D.source₀_isAlgebraicSpace hValg D.target₀_isAlgebraicSpace D.source₀_quasiSeparated
      (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ _
        (isAbsolutelySeparated_of_isAffineSpace B S hS hZ
          (isAffineSpace_yoneda B S hS V₀ hV₀)))
  -- Stacks 07SQ applied to the system `V_i ×_{Y_i} X_i = B_i ×_{B₀} T`, whose limit is affine
  obtain ⟨j, -, hj⟩ :=
    hstage (D.stagesBaseChangeDescentSituation (pullback.fst D.map₀ v ≫ D.sourceToBase)
        hTalg hTqc hTqs)
      (D.siteContainsBaseChangeLimits_stagesBaseChangeSystem hconv _)
      (D.isAffineSpace_limitBaseChange_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits
        v hconv hV₀ hf)
  exact ⟨j.1, j.2, D.isAffineHom_mapAt_of_isAffineSpace_baseChange v hV₀ hvSurj hvEtale
    j.1 j.2 hj⟩

/-- Notation and assumptions as in Situation 70.6.1 (tag 084W), carried by
`AlgebraicGeometry.Space.MorphismDescentSituation`, in the chapter's setting of Section 70.2
(tag 07SD): `B = lim B_i` a directed inverse limit of algebraic spaces over `S` with affine
transition morphisms, `f₀ : X₀ ⟶ Y₀` a morphism of algebraic spaces over `B₀` with `B₀`, `X₀`
and `Y₀` quasi-compact and quasi-separated, and `f_i : X_i ⟶ Y_i`, `f : X ⟶ Y` its base changes
to `B_i` for `i ≥ 0` and to `B`. If `f` is affine, then `f_i` is affine for some `i ≥ 0`.

The hypothesis `hconv` is the chapter's standing convention that every ring considered has its
spectrum in the big fppf site, read for the system of bases; nothing is asked of the index. The
implementation notes of this module show that the statement fails without it; the
corresponding failure of Stacks 07SQ, on which the proof rests, is
`AlgebraicGeometry.Space.DescentSituation.not_forall_exists_isAffineSpace_system_obj`.

The proof is the source's:
`exists_isAffineHom_mapAt_of_descentAffineStage_of_siteContainsBaseChangeLimits` with Stacks
07SQ supplied by
`DescentSituation.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits`. -/
@[stacks 084Y]
theorem exists_isAffineHom_mapAt_of_isAffineHom_mapLimit_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) (hf : IsAffineHom B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsAffineHom B S hS (D.mapAt i hi) :=
  D.exists_isAffineHom_mapAt_of_descentAffineStage_of_siteContainsBaseChangeLimits hconv
    (fun E hE hX => E.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits hE hX) hf

end AlgebraicGeometry.Space.MorphismDescentSituation
