module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteriaRepresentable03ZQ
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of finiteness properties of modules on algebraic spaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `F` be
an `𝒪_X`-module on the small étale site of `X`.  Finite presentation of `F` descends along an
fpqc covering of `X`, and for a finite morphism `f : X ⟶ Y` the module `F` is of finite type,
respectively of finite presentation, exactly when its direct image is.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeChart` is the base change `V ×_Y X` of an étale scheme
  chart `V` of `Y` along a representable morphism `X ⟶ Y`, an étale scheme chart of `X`.
* `AlgebraicGeometry.Space.ChartFinitePresentationDescent` is Stacks 05B0 for the étale scheme
  charts of `X`: descent of finite presentation along the fpqc covering of a chart produced
  from an fpqc covering of `X` by base change and refinement by scheme atlases.

## Main results

* `AlgebraicGeometry.Space.isSurjective_smallBaseChange_obj_hom`: the base change of an étale
  scheme chart which is surjective on points is surjective on points.
* `AlgebraicGeometry.Space.over_smallBaseChangeModulePushforward_obj`: the identity
  `f'_*(F|_U) = (f_*F)|_V` of Stacks 04CF, on objects.
* `AlgebraicGeometry.Space.isFinitePresentation_of_modulePullback_fpqcCovering`: the conditional
  form of Stacks 060V.
* `AlgebraicGeometry.Space.isFiniteType_iff_smallBaseChangePushforward`: the conditional form of
  Stacks 060Z.
* `AlgebraicGeometry.Space.isFinitePresentation_iff_smallBaseChangePushforward`: the conditional
  form of Stacks 0610.

The three tags are registered elsewhere, on the statements that assume quasi-coherence of the
module, as the source does, and prove these three hypotheses outright:
`AlgebraicGeometry.Space.isFinitePresentation_of_pullback_fpqc` for Stacks 060V,
`isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite` for Stacks 060Z and
`isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite` for Stacks 0610.

## Implementation notes

The direct image of modules along a finite — hence representable — morphism is taken to be
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, the direct image along the
base-change functor of étale scheme charts of Stacks 03G2, part (4) with the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp`.  That is the functor for which the identity
`f'_*(F|_U) = (f_*F)|_V` of Stacks 04CF holds as an *equality* of functors,
`AlgebraicGeometry.Space.overFunctor_comp_smallBaseChangeModulePushforward`; its comparison
with `AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU, is not
supplied in this development.

Each of the three statements in this file takes one hypothesis, in each case the case of schemes
that the source cites: Stacks 05B0 for Stacks 060V, Stacks 05B3 for Stacks 060Z and Stacks 05B4
for Stacks 0610.  In each case the hypothesis is that statement at a *chart*, with chart-level
premises only: for Stacks 060V the fpqc covering of the chart scheme that base change produces
and finite presentation of the modules on its members, for Stacks 060Z and Stacks 0610 the
equivalence at the base change of `f` to the chart.  None of the three is the conclusion of its
own tag in another reading.  The case of schemes is available on the *Zariski* site of a scheme
(`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`,
`AlgebraicGeometry.isFiniteType_iff_pushforward_isFiniteType` and
`AlgebraicGeometry.isFinitePresentation_iff_pushforward_isFinitePresentation`), while the étale
localization below produces it on the slices of the small étale sites, which by Stacks 04M0 are
the small étale sites of the chart schemes — `reindexRing_chartLocalizationEquivalence` matches
the two structure sheaves.  Translating between the two readings is the clause of Stacks 05VG
for Stacks 03DL (5) and (7) at the small étale site of a scheme, equivalently Stacks 03DX; of
Stacks 05VG only the seven global clauses are available, and
the local ones only behind an equivalence of ringed topoi,
`Stacks.Sheaves.LocalTypeComparison.isFlat_iff`, which the comparison of Stacks 03DX is not.

What the three proofs supply is the étale localization: the finiteness conditions are tested on
the étale charts of the space by the criteria of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFinitenessEtaleChart.lean`, a surjective étale
chart of the source of a finite morphism is produced from one of its target by base change, and
an fpqc covering of the space is carried to one of a chart by
`AlgebraicGeometry.Space.exists_chart_fpqc_refinement`, which pulls it back along the chart and
refines it by scheme atlases (Stacks 0419 for the members that are schemes).

The étale charts are written as objects of `AlgebraicGeometry.Space.smallEtaleRingedSite`
rather than of `AlgebraicGeometry.Space.SmallEtale`, to which that category is definitionally
equal, because that is the spelling at which the slice of the site and its structure sheaf are
found by instance search; the same convention is used in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFinitenessEtaleChart.lean`.

The module sections live in the universe `u` of the schemes, as they do for
`AlgebraicGeometry.Space.modulePushforward` and for the chart criteria.

## References

* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 060Z](https://stacks.math.columbia.edu/tag/060Z)
* [Stacks Project, Tag 0610](https://stacks.math.columbia.edu/tag/0610)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A finite morphism of algebraic spaces is representable. -/
theorem relativelyRepresentable_hom_of_isFinite {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom) : yoneda.relativelyRepresentable f.hom :=
  relativelyRepresentable_of_isFinite B S hS X.2.isSheaf Y.2.isSheaf hf

/-- The base change `V ×_Y X` of an étale scheme chart `V` of `Y` along a representable
morphism `f : X ⟶ Y` of algebraic spaces, as an étale scheme chart of `X`. -/
noncomputable abbrev baseChangeChart {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    (smallEtaleRingedSite B S hS X.1 X.2).C :=
  (smallBaseChange B S hS f hrep).obj V

/-- The base change along a representable morphism of an étale scheme chart which is surjective
on points is again surjective on points. -/
theorem isSurjective_smallBaseChange_obj_hom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsSurjective B S hS V.1.hom) :
    IsSurjective B S hS (baseChangeChart B S hS f hrep V).1.hom := by
  intro z
  obtain ⟨x, hx⟩ := hV (pointsMap B S hS X.1 f.hom z)
  obtain ⟨w, hw, -⟩ :=
    exists_point_of_isPullback_presheaf B S hS (hrep.isPullback V.1.hom) z x hx.symm
  exact ⟨w, hw⟩

/-- A property `a` of a module on `X`, which is tested on any étale scheme chart of `X` that is
surjective on points, is equivalent to a property `b` of a module on `Y`, tested likewise on
charts of `Y`, as soon as the two chart-level tests agree along the base change of `f`. -/
private theorem iff_of_forall_baseChangeChart {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) {a b : Prop}
    {PX : (smallEtaleRingedSite B S hS X.1 X.2).C → Prop} {QY : SmallEtale B S hS Y.1 → Prop}
    (hX : ∀ U, IsSurjective B S hS U.1.hom → (a ↔ PX U))
    (hY : ∀ V, IsSurjective B S hS V.1.hom → (b ↔ QY V))
    (h : ∀ V, PX (baseChangeChart B S hS f hrep V) ↔ QY V) : a ↔ b := by
  obtain ⟨V, hV⟩ := exists_isSurjective_chart B S hS Y
  exact (hX _ (isSurjective_smallBaseChange_obj_hom B S hS f hrep V hV)).trans
    ((h V).trans (hY V hV).symm)

/-- **Stacks 04CF** on objects: the restriction to an étale scheme chart `V` of `Y` of the
direct image of an `𝒪_X`-module along a representable morphism `f : X ⟶ Y` is the direct image,
along the base change of `f` to `V`, of its restriction to `V ×_Y X`. -/
theorem over_smallBaseChangeModulePushforward_obj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (M : SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :
    letI := isContinuous_overPost_smallBaseChange B S hS f hrep V
    ((smallBaseChangeModulePushforward B S hS f hrep).obj M).over V =
      (SheafOfModules.pushforward (RingedSite.MorphismLocalization.localizedStructureMap
        (smallBaseChange B S hS f hrep) (SmallEtale.topology B S hS X.1)
        (SmallEtale.topology B S hS Y.1) V (smallEtaleRingSheaf B S hS X.1 X.2)
        (smallEtaleRingSheaf B S hS Y.1 Y.2) (smallBaseChangeSharp B S hS f hrep))).obj
        (M.over (baseChangeChart B S hS f hrep V)) :=
  (Functor.congr_obj
    (overFunctor_comp_smallBaseChangeModulePushforward B S hS f hrep V) M).symm

/-- **Stacks 05B0 at an étale scheme chart.**  Finite presentation of a module on an étale
scheme chart `V` of `X` descends along the fpqc covering `W i ⟶ V` of that chart obtained from
a family `g : Xᵢ ⟶ X` by base change and refinement by scheme atlases, each `W i` being an
étale scheme chart of `Xᵢ i`.  The module on `W i` is the restriction of the pullback of `G`
to `Xᵢ i`, which the commuting square identifies with the pullback of `G|_V` along `W i ⟶ V`
in the sense of Stacks' Equation 03LW. -/
abbrev ChartFinitePresentationDescent {I : Type v} {X : AlgebraicSpaces B S hS}
    (Xᵢ : I → AlgebraicSpaces B S hS) (g : ∀ i, Xᵢ i ⟶ X) : Prop :=
  ∀ (V : (smallEtaleRingedSite B S hS X.1 X.2).C) (G : Modules.{u, u} B S hS X.1 X.2)
    (W : ∀ i, (smallEtaleRingedSite B S hS (Xᵢ i).1 (Xᵢ i).2).C)
    (r : ∀ i, (W i).1.left ⟶ V.1.left),
    Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (W i).1.left)
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (r i)) ∈
      Scheme.fpqcPrecoverage (etaleChartScheme B S hS V) →
    (∀ i, yoneda.map (r i) ≫ V.1.hom = (W i).1.hom ≫ (g i).hom) →
    (∀ i, SheafOfModules.IsFinitePresentation
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS (Xᵢ i).1 (Xᵢ i).2).over (W i)).O))
      (((modulePullback B S hS (g i)).obj G).over (W i))) →
    SheafOfModules.IsFinitePresentation
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS X.1 X.2).over V).O)) (G.over V)

/-- The conditional form of the descent statement for finite presentation of a module along an
fpqc covering of an algebraic space: the case of schemes, Stacks 05B0, is the hypothesis
`hscheme`, in the reading the étale localization produces — it is asked for on the étale scheme
charts of `X`, along the fpqc covering of a chart that base change and refinement by scheme
atlases produce from the given covering of `X`.

Stacks 060V itself is `AlgebraicGeometry.Space.isFinitePresentation_of_pullback_fpqc`, which
assumes quasi-coherence of the module as the source does and proves `hscheme` outright; that is
the declaration registered for the tag. -/
theorem isFinitePresentation_of_modulePullback_fpqcCovering {I : Type v}
    {X : AlgebraicSpaces B S hS} {Xᵢ : I → AlgebraicSpaces B S hS} (g : ∀ i, Xᵢ i ⟶ X)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hfp : ∀ i, ((modulePullback B S hS (g i)).obj F).IsFinitePresentation)
    (hscheme : ChartFinitePresentationDescent B S hS Xᵢ g) :
    F.IsFinitePresentation := by
  refine (isFinitePresentation_iff_forall_over B S hS X.1 X.2 F).2 fun V ↦ ?_
  obtain ⟨T, c, r, hc, hcov, hsq⟩ := exists_chart_fpqc_refinement B S hS Xᵢ g hg V
  exact hscheme V F (fun i ↦ ⟨CostructuredArrow.mk (c i), hc i⟩) r hcov hsq fun i ↦
    (isFinitePresentation_iff_forall_over B S hS (Xᵢ i).1 (Xᵢ i).2 _).1 (hfp i) _

/-- The conditional form of the comparison of finite type for a module on the source of a finite
morphism of algebraic spaces with finite type of its direct image: the case of schemes,
Stacks 05B3, is the hypothesis `hscheme`.  By
`AlgebraicGeometry.Space.over_smallBaseChangeModulePushforward_obj`, which is Stacks 04CF, the
right-hand side of `hscheme` is the direct image of `F|_{V ×_Y X}` along the base change of
`f` to the chart `V`.

Stacks 060Z itself is
`AlgebraicGeometry.Space.isFiniteType_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite`,
which assumes quasi-coherence of the module as the source does and proves `hscheme` outright;
that is the declaration registered for the tag. -/
theorem isFiniteType_iff_smallBaseChangePushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFinite B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hscheme : ∀ V : SmallEtale B S hS Y.1,
      (F.over (baseChangeChart B S hS f
          (relativelyRepresentable_hom_of_isFinite B S hS f hf) V)).IsFiniteType ↔
        (((smallBaseChangeModulePushforward B S hS f
          (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).over V).IsFiniteType) :
    F.IsFiniteType ↔
      ((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).IsFiniteType :=
  iff_of_forall_baseChangeChart B S hS f (relativelyRepresentable_hom_of_isFinite B S hS f hf)
    (isFiniteType_iff_over_of_isSurjective B S hS X.1 X.2 F)
    (isFiniteType_iff_over_of_isSurjective B S hS Y.1 Y.2 _) hscheme

/-- The conditional form of the comparison of finite presentation for a module on the source of a
finite morphism of finite presentation of algebraic spaces with finite presentation of its direct
image: the case of schemes, Stacks 05B4, is the hypothesis `hscheme`, in the same reading of
Stacks 04CF as for the finite type statement above.

Stacks 0610 itself is
`isFinitePresentation_iff_smallBaseChangePushforward_of_isQuasicoherentOnSite` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeFinitePresentationDescent.lean`, which assumes
quasi-coherence of the module as the source does and proves `hscheme` outright; that is the
declaration registered for the tag. -/
theorem isFinitePresentation_iff_smallBaseChangePushforward {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFinite B S hS f.hom) (_hfp : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hscheme : ∀ V : SmallEtale B S hS Y.1,
      (F.over (baseChangeChart B S hS f
          (relativelyRepresentable_hom_of_isFinite B S hS f hf) V)).IsFinitePresentation ↔
        (((smallBaseChangeModulePushforward B S hS f
          (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).over
            V).IsFinitePresentation) :
    F.IsFinitePresentation ↔
      ((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj F).IsFinitePresentation :=
  iff_of_forall_baseChangeChart B S hS f (relativelyRepresentable_hom_of_isFinite B S hS f hf)
    (isFinitePresentation_iff_over_of_isSurjective B S hS X.1 X.2 F)
    (isFinitePresentation_iff_over_of_isSurjective B S hS Y.1 Y.2 _) hscheme

end AlgebraicGeometry.Space

end
