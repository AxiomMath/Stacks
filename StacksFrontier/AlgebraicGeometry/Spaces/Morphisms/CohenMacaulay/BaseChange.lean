module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.BaseChangeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Cohen–Macaulay morphisms of algebraic spaces and base change

Let a morphism of algebraic spaces over `S` have locally Noetherian fibres, and base change it
along a morphism locally of finite type. Cohen–Macaulayness at a point is preserved, and it is
reflected when either the original morphism is flat at the image point or the base morphism is
flat at the corresponding point.

## Main results

* `AlgebraicGeometry.Space.isCohenMacaulayAt_pullback_snd` is preservation under base change.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_of_pullback_snd_of_isFlatAt` is reflection for an
  originally flat morphism.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_of_pullback_snd_of_isFlatAt_base` is reflection
  for a base morphism flat at the relevant point.

## Implementation notes

The three declarations state parts (1), (2) and (3) of the source lemma. The base change is the
presheaf fibre product with its second projection, so the images of the point of the
base-changed source in the original source and in the new target are its images under the two
projections on points.

The proof is the étale-local reduction the source gives. Compatible charts are chosen in the
order the source chooses them: a surjective étale scheme chart `V` of the target, a surjective
étale chart `V'` of the fibre product of the new target with `V`, and a surjective étale chart
`U` of the fibre product of the source with `V`. The fibre product `U ×_V V'` in the site is
then a chart of the base change: its étale surjective morphism to the base change is the base
change of the chart `U` along `V' ⟶ V` followed by the base change of the chart `V'` along the
base change itself, both of which are exhibited as pullback squares of presheaves.

Both conjuncts of `AlgebraicGeometry.Space.IsCohenMacaulayAt` are chart conditions of Tag 04NC,
so they are evaluated on those charts by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart`, and the statements become
the scheme statements of Tag 045T for the chart morphisms `U ⟶ V` and `V' ⟶ V`. The source of
the scheme-level base change is Mathlib's chosen fibre product rather than the chart
`U ×_V V'`, and the two are compared by the canonical isomorphism of
`CategoryTheory.Limits.PreservesPullback.iso` together with
the module's own étale-square transfer lemma, which transfers the
scheme-level predicate across a commuting square with étale verticals; that transfer is again
the étale locality of the two germ properties, so nothing beyond Tag 04NB is used.

The standing hypotheses are what make the scheme-level statement applicable: local
Noetherianity of the fibres of the morphism of spaces gives local Noetherianity of the fibres
of the chart morphism `U ⟶ V` through Tag 0CUW, and `Y' ⟶ Y` being locally of finite type gives
the same for the chart morphism `V' ⟶ V` directly from the chart definition of Tag 03XF.

## References

* [Stacks Project, Tag 0E0Z](https://stacks.math.columbia.edu/tag/0E0Z)
* [Stacks Project, Tag 045T](https://stacks.math.columbia.edu/tag/045T)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
* [Stacks Project, Tag 04NB](https://stacks.math.columbia.edu/tag/04NB)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 0CUX](https://stacks.math.columbia.edu/tag/0CUX)
* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Scheme-level transfer along an étale square -/

/-- Cohen–Macaulayness of a morphism of schemes at a point transfers across a commuting square
with étale verticals. -/
private theorem schemeIsCohenMacaulayAt_iff_of_etale_square
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (ha : Etale a) (hb : Etale b) (hcomm : a ≫ h = h' ≫ b) (x' : U')
    (hf' : ∀ y, IsLocallyNoetherian (h'.fiber y))
    (hf : ∀ y, IsLocallyNoetherian (h.fiber y)) :
    Scheme.Hom.IsCohenMacaulayAt h' hf' x' ↔ Scheme.Hom.IsCohenMacaulayAt h hf (a x') := by
  have hb' : b (h' x') = h (a x') := by
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
  have key : ∀ (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop),
      MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q →
      (Q (MorphismOfGerms.ofSchemeHom h (a x')) ↔
        Q (MorphismOfGerms.ofSchemeHom h' x')) := by
    intro Q hQ
    refine hQ.iff_of_etale_square (MorphismOfGerms.ofSchemeHom a x')
      (MorphismOfGerms.ofSchemeHomOfEq b (h' x') (h (a x')) hb')
      (MorphismOfGerms.ofSchemeHom h' x') (MorphismOfGerms.ofSchemeHom h (a x'))
      (MorphismOfGerms.isEtale_ofSchemeHomOfEq _ _ _ _ ha)
      (MorphismOfGerms.isEtale_ofSchemeHomOfEq _ _ _ _ hb) ?_
    rw [MorphismOfGerms.ofSchemeHomOfEq_comp, MorphismOfGerms.ofSchemeHomOfEq_comp]
    congr 1
    exact hcomm.symm
  have hfl := key _ MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat
  rw [MorphismOfGerms.isFlat_ofSchemeHom_iff, MorphismOfGerms.isFlat_ofSchemeHom_iff] at hfl
  rw [Scheme.Hom.isCohenMacaulayAt_iff_germ, Scheme.Hom.isCohenMacaulayAt_iff_germ]
  exact Iff.and hfl.symm
    (key _ hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget).symm


/-! ### Shared chart machinery -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Cohen–Macaulayness of a morphism of algebraic spaces at a point of its source, read off a
pointed étale chart whose chart morphism has locally Noetherian fibres. -/
theorem isCohenMacaulayAt_iff_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X)
    (c : EtaleChartAtPoint B S hS f x)
    (hc : ∀ y, IsLocallyNoetherian
      (((BigFppfOver.toScheme B S hS).map c.h).fiber y)) :
    IsCohenMacaulayAt B S hS f x ↔
      Scheme.Hom.IsCohenMacaulayAt ((BigFppfOver.toScheme B S hS).map c.h) hc
        (c.sourcePoint B S hS) := by
  have hflat := holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
    (@MorphismOfGerms.IsFlat.{u}) MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat f x c
  have hfib := holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
    (@HasCohenMacaulayFiberLocalRing.{u})
    hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget f x c
  rw [Scheme.Hom.isCohenMacaulayAt_iff_germ]
  exact Iff.and (hflat.trans (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _)) hfib

attribute [local instance] etale_isStableUnderComposition surjective_isStableUnderComposition

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_cohenMacaulayBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_cohenMacaulayBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _


section Statements

/-- Cohen–Macaulayness of the base change at the given point, read on the fibre product of the
chart morphisms. -/
private theorem isCohenMacaulayAt_pull_iff_of_chartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x')
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map C.q)] :
    IsCohenMacaulayAt B S hS (pullback.snd f g) x' ↔
      Scheme.Hom.IsCohenMacaulayAt
        (pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
          ((BigFppfOver.toScheme B S hS).map C.q))
        (fun y' => isLocallyNoetherian_fiber_pullback _ _ C.pFiber y')
        ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
          (C.chartPull.sourcePoint B S hS)) := by
  refine (isCohenMacaulayAt_iff_chart B S hS (pullback.snd f g) x' C.chartPull
    (pullFiber_of_chartData C)).trans ?_
  refine schemeIsCohenMacaulayAt_iff_of_etale_square
    (PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
    (𝟙 ((BigFppfOver.toScheme B S hS).obj C.V'))
    ((BigFppfOver.toScheme B S hS).map (pullback.snd C.p C.q))
    (pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q))
    inferInstance inferInstance (by rw [Category.comp_id, toScheme_map_snd_of_chartData C]) _
    (pullFiber_of_chartData C)
    (fun y' => isLocallyNoetherian_fiber_pullback _ _ C.pFiber y')

/-- The first projection of the scheme-level fibre product sends the image of the chart point of
the base change to the chart point of the source. -/
private theorem fst_iso_hom_chartPull_sourcePoint
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    (pullback.fst ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q))
      ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
        (C.chartPull.sourcePoint B S hS)) =
      C.chartSource.sourcePoint B S hS := by
  rw [C.sourcePoint_chartSource, ← PreservesPullback.iso_hom_fst
    (BigFppfOver.toScheme B S hS) C.p C.q]
  rfl

/-- Cohen–Macaulayness of the original morphism at the image point, read on the chart
morphism. -/
private theorem isCohenMacaulayAt_source_iff_of_chartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    IsCohenMacaulayAt B S hS f (pointsMap B S hS (pullback f g) (pullback.fst f g) x') ↔
      Scheme.Hom.IsCohenMacaulayAt ((BigFppfOver.toScheme B S hS).map C.p) C.pFiber
        ((pullback.fst ((BigFppfOver.toScheme B S hS).map C.p)
          ((BigFppfOver.toScheme B S hS).map C.q))
          ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
            (C.chartPull.sourcePoint B S hS))) := by
  have hfst := fst_iso_hom_chartPull_sourcePoint B S hS C
  rw [hfst]
  exact isCohenMacaulayAt_iff_chart B S hS f _ C.chartSource C.pFiber

/-- **Stacks 0E0Z, part (1).** Cohen–Macaulayness of a morphism of algebraic spaces with
locally Noetherian fibres at a point is preserved by base change along a morphism locally of
finite type. -/
@[stacks 0E0Z "part (1)", ega "IV 6.8.3" "(iii) CM, h loc fin type"]
theorem isCohenMacaulayAt_pullback_snd
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (x' : points B S hS (pullback f g))
    (hcm : IsCohenMacaulayAt B S hS f
      (pointsMap B S hS (pullback f g) (pullback.fst f g) x')) :
    IsCohenMacaulayAt B S hS (pullback.snd f g) x' := by
  obtain ⟨C⟩ := exists_baseChangeChartData B S hS hX hY hY' f g hf hg x'
  have := C.qLft
  exact (isCohenMacaulayAt_pull_iff_of_chartData B S hS C).mpr
    (_root_.AlgebraicGeometry.isCohenMacaulayAt_pullback _ _ C.pFiber _
      ((isCohenMacaulayAt_source_iff_of_chartData B S hS C).mp hcm))

/-- **Stacks 0E0Z, part (2).** Cohen–Macaulayness descends from the base change when the
original morphism is flat at the point in question. -/
@[stacks 0E0Z "part (2)"]
theorem isCohenMacaulayAt_of_pullback_snd_of_isFlatAt
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (x' : points B S hS (pullback f g))
    (hflat : IsFlatAt B S hS f (pointsMap B S hS (pullback f g) (pullback.fst f g) x'))
    (hcm : IsCohenMacaulayAt B S hS (pullback.snd f g) x') :
    IsCohenMacaulayAt B S hS f
      (pointsMap B S hS (pullback f g) (pullback.fst f g) x') := by
  obtain ⟨C⟩ := exists_baseChangeChartData B S hS hX hY hY' f g hf hg x'
  have := C.qLft
  have hfst := fst_iso_hom_chartPull_sourcePoint B S hS C
  have hflatScheme := (MorphismOfGerms.isFlat_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map C.p) (C.chartSource.sourcePoint B S hS)).mp
      (hflat C.chartSource)
  rw [← hfst] at hflatScheme
  exact (isCohenMacaulayAt_source_iff_of_chartData B S hS C).mpr
    (_root_.AlgebraicGeometry.isCohenMacaulayAt_of_pullback_of_flat _ _ C.pFiber _
      hflatScheme ((isCohenMacaulayAt_pull_iff_of_chartData B S hS C).mp hcm))

/-- **Stacks 0E0Z, part (3).** Cohen–Macaulayness descends from the base change when the base
morphism is flat at the corresponding point. -/
@[stacks 0E0Z "part (3)", ega "IV 6.8.3" "(iii) converse, CM"]
theorem isCohenMacaulayAt_of_pullback_snd_of_isFlatAt_base
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (x' : points B S hS (pullback f g))
    (hflat : IsFlatAt B S hS g (pointsMap B S hS (pullback f g) (pullback.snd f g) x'))
    (hcm : IsCohenMacaulayAt B S hS (pullback.snd f g) x') :
    IsCohenMacaulayAt B S hS f
      (pointsMap B S hS (pullback f g) (pullback.fst f g) x') := by
  obtain ⟨C⟩ := exists_baseChangeChartData B S hS hX hY hY' f g hf hg x'
  have := C.qLft
  have hsnd : (pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q))
      ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
        (C.chartPull.sourcePoint B S hS)) =
      C.chartBase.sourcePoint B S hS := by
    rw [C.sourcePoint_chartBase, ← PreservesPullback.iso_hom_snd
      (BigFppfOver.toScheme B S hS) C.p C.q]
    rfl
  have hflatScheme := (MorphismOfGerms.isFlat_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map C.q) (C.chartBase.sourcePoint B S hS)).mp
      (hflat C.chartBase)
  rw [← hsnd] at hflatScheme
  exact (isCohenMacaulayAt_source_iff_of_chartData B S hS C).mpr
    (_root_.AlgebraicGeometry.isCohenMacaulayAt_of_pullback_of_flat_base _ _ C.pFiber _
      hflatScheme ((isCohenMacaulayAt_pull_iff_of_chartData B S hS C).mp hcm))

end Statements

end AlgebraicGeometry.Space

end
