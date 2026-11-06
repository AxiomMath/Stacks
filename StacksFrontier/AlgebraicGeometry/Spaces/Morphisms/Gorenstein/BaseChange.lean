module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.GorensteinFiber
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.BaseChangeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Gorenstein morphisms of algebraic spaces and base change

Let a morphism of algebraic spaces over `S` have locally Noetherian fibres, and base change it
along a morphism locally of finite type. Gorensteinness at a point is preserved, and it is
reflected when either the original morphism is flat at the image point or the base morphism is
flat at the corresponding point.

## Main results

* `AlgebraicGeometry.Space.isGorensteinAt_pullback_snd` is preservation under base change.
* `AlgebraicGeometry.Space.isGorensteinAt_of_pullback_snd_of_isFlatAt` is reflection for an
  originally flat morphism.
* `AlgebraicGeometry.Space.isGorensteinAt_of_pullback_snd_of_isFlatAt_base` is reflection for a
  base morphism flat at the relevant point.

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

Both conjuncts of `AlgebraicGeometry.Space.IsGorensteinAt` are chart conditions of Tag 04NC, so
they are evaluated on those charts by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart`, and the statements become
the scheme statements of Tag 0C07 for the chart morphisms `U ⟶ V` and `V' ⟶ V`. The source of
the scheme-level base change is Mathlib's chosen fibre product rather than the chart `U ×_V V'`,
and the two are compared by the canonical isomorphism of
`CategoryTheory.Limits.PreservesPullback.iso` together with the module's own étale-square
transfer lemma, which transfers the scheme-level predicate across a commuting square with étale
verticals; that transfer is again the étale locality of the two germ properties, so nothing
beyond Tag 04NB is used.

The standing hypotheses are what make the scheme-level statement applicable: local
Noetherianity of the fibres of the morphism of spaces gives local Noetherianity of the fibres of
the chart morphism `U ⟶ V` through Tag 0CUW, and `Y' ⟶ Y` being locally of finite type gives the
same for the chart morphism `V' ⟶ V` directly from the chart definition of Tag 03XF.

## References

* [Stacks Project, Tag 0E18](https://stacks.math.columbia.edu/tag/0E18)
* [Stacks Project, Tag 0C07](https://stacks.math.columbia.edu/tag/0C07)
* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E13](https://stacks.math.columbia.edu/tag/0E13)
* [Stacks Project, Tag 04NB](https://stacks.math.columbia.edu/tag/04NB)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 0CUX](https://stacks.math.columbia.edu/tag/0CUX)
* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Scheme-level transfer along an étale square -/

/-- Gorensteinness of a morphism of schemes with locally Noetherian fibres at a point of its
source is flatness there together with the fibre local ring condition on the induced morphism of
germs. -/
theorem schemeIsGorensteinAt_iff_germ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x : X) :
    Scheme.Hom.IsGorensteinAt f hf x ↔
      IsFlatAt f.toLRSHom.toShHom x ∧
        HasGorensteinFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) := by
  have : IsLocallyNoetherian (f.fiber (f x)) := hf (f x)
  rw [hasGorensteinFiberLocalRing_ofSchemeHom_iff_of_isNoetherianRing]

/-- Gorensteinness of a morphism of schemes at a point transfers across a commuting square with
étale verticals. -/
private theorem schemeIsGorensteinAt_iff_of_etale_square
    {U' U V' V : Scheme.{u}} (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (ha : Etale a) (hb : Etale b) (hcomm : a ≫ h = h' ≫ b) (x' : U')
    (hf' : ∀ y, IsLocallyNoetherian (h'.fiber y))
    (hf : ∀ y, IsLocallyNoetherian (h.fiber y)) :
    Scheme.Hom.IsGorensteinAt h' hf' x' ↔ Scheme.Hom.IsGorensteinAt h hf (a x') := by
  have hb' : b (h' x') = h (a x') := by
    calc b (h' x') = (h' ≫ b) x' := (Scheme.Hom.comp_apply h' b x').symm
      _ = (a ≫ h) x' := by rw [hcomm]
      _ = h (a x') := Scheme.Hom.comp_apply a h x'
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
  rw [schemeIsGorensteinAt_iff_germ, schemeIsGorensteinAt_iff_germ]
  exact Iff.and hfl.symm
    (key _ hasGorensteinFiberLocalRing_isEtaleLocalOnSourceAndTarget).symm


/-! ### Shared chart machinery -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Gorensteinness of a morphism of algebraic spaces at a point of its source, read off a
pointed étale chart whose chart morphism has locally Noetherian fibres. -/
theorem isGorensteinAt_iff_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X)
    (c : EtaleChartAtPoint B S hS f x)
    (hc : ∀ y, IsLocallyNoetherian
      (((BigFppfOver.toScheme B S hS).map c.h).fiber y)) :
    IsGorensteinAt B S hS f x ↔
      Scheme.Hom.IsGorensteinAt ((BigFppfOver.toScheme B S hS).map c.h) hc
        (c.sourcePoint B S hS) := by
  have hflat := holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
    (@MorphismOfGerms.IsFlat.{u}) MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat f x c
  have hfib := holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
    (@HasGorensteinFiberLocalRing.{u})
    hasGorensteinFiberLocalRing_isEtaleLocalOnSourceAndTarget f x c
  rw [schemeIsGorensteinAt_iff_germ]
  refine Iff.and (hflat.trans ?_) hfib
  exact MorphismOfGerms.isFlat_ofSchemeHom_iff _ _

attribute [local instance] etale_isStableUnderComposition surjective_isStableUnderComposition

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_GorensteinBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_GorensteinBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_GorensteinBaseChange B S hS).has_limit _


section Statements

/-- Gorensteinness of the base change at the given point, read on the fibre product of the chart
morphisms. -/
private theorem isGorensteinAt_pull_iff_of_chartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x')
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map C.q)] :
    IsGorensteinAt B S hS (pullback.snd f g) x' ↔
      Scheme.Hom.IsGorensteinAt
        (pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
          ((BigFppfOver.toScheme B S hS).map C.q))
        (fun y' => isLocallyNoetherian_fiber_pullback _ _ C.pFiber y')
        ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
          (C.chartPull.sourcePoint B S hS)) := by
  have hiso : IsIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom :=
    inferInstance
  refine (isGorensteinAt_iff_chart B S hS (pullback.snd f g) x' C.chartPull
    (pullFiber_of_chartData C)).trans ?_
  refine schemeIsGorensteinAt_iff_of_etale_square
    (PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
    (𝟙 ((BigFppfOver.toScheme B S hS).obj C.V'))
    ((BigFppfOver.toScheme B S hS).map (pullback.snd C.p C.q))
    (pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q))
    inferInstance inferInstance (by rw [Category.comp_id, toScheme_map_snd_of_chartData C]) _
    (pullFiber_of_chartData C)
    (fun y' => isLocallyNoetherian_fiber_pullback _ _ C.pFiber y')

/-- The first projection of the scheme-level pullback sends the comparison image of the chart
point of the base change to the chart point of the source. -/
private theorem fst_iso_hom_sourcePoint
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

/-- Gorensteinness of the original morphism at the image point, read on the chart morphism. -/
private theorem isGorensteinAt_source_iff_of_chartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    IsGorensteinAt B S hS f (pointsMap B S hS (pullback f g) (pullback.fst f g) x') ↔
      Scheme.Hom.IsGorensteinAt ((BigFppfOver.toScheme B S hS).map C.p) C.pFiber
        ((pullback.fst ((BigFppfOver.toScheme B S hS).map C.p)
          ((BigFppfOver.toScheme B S hS).map C.q))
          ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom
            (C.chartPull.sourcePoint B S hS))) := by
  rw [fst_iso_hom_sourcePoint B S hS C]
  exact isGorensteinAt_iff_chart B S hS f _ C.chartSource C.pFiber

/-- **Stacks 0E18, part (1).** Gorensteinness of a morphism of algebraic spaces with locally
Noetherian fibres at a point is preserved by base change along a morphism locally of finite
type. -/
@[stacks 0E18 "part (1)"]
theorem isGorensteinAt_pullback_snd
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (x' : points B S hS (pullback f g))
    (hgor : IsGorensteinAt B S hS f
      (pointsMap B S hS (pullback f g) (pullback.fst f g) x')) :
    IsGorensteinAt B S hS (pullback.snd f g) x' := by
  obtain ⟨C⟩ := exists_baseChangeChartData B S hS hX hY hY' f g hf hg x'
  have := C.qLft
  exact (isGorensteinAt_pull_iff_of_chartData B S hS C).mpr
    (_root_.AlgebraicGeometry.Scheme.Hom.isGorensteinAt_pullback _ _ C.pFiber _
      ((isGorensteinAt_source_iff_of_chartData B S hS C).mp hgor))

/-- **Stacks 0E18, part (2).** Gorensteinness descends from the base change when the original
morphism is flat at the point in question. -/
@[stacks 0E18 "part (2)"]
theorem isGorensteinAt_of_pullback_snd_of_isFlatAt
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (x' : points B S hS (pullback f g))
    (hflat : IsFlatAt B S hS f (pointsMap B S hS (pullback f g) (pullback.fst f g) x'))
    (hgor : IsGorensteinAt B S hS (pullback.snd f g) x') :
    IsGorensteinAt B S hS f
      (pointsMap B S hS (pullback f g) (pullback.fst f g) x') := by
  obtain ⟨C⟩ := exists_baseChangeChartData B S hS hX hY hY' f g hf hg x'
  have := C.qLft
  have hflatScheme := (MorphismOfGerms.isFlat_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map C.p) (C.chartSource.sourcePoint B S hS)).mp
      (hflat C.chartSource)
  rw [← fst_iso_hom_sourcePoint B S hS C] at hflatScheme
  exact (isGorensteinAt_source_iff_of_chartData B S hS C).mpr
    (_root_.AlgebraicGeometry.Scheme.Hom.isGorensteinAt_of_pullback_of_flat _ _ C.pFiber _
      hflatScheme ((isGorensteinAt_pull_iff_of_chartData B S hS C).mp hgor))

/-- **Stacks 0E18, part (3).** Gorensteinness descends from the base change when the base
morphism is flat at the corresponding point. -/
@[stacks 0E18 "part (3)"]
theorem isGorensteinAt_of_pullback_snd_of_isFlatAt_base
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (x' : points B S hS (pullback f g))
    (hflat : IsFlatAt B S hS g (pointsMap B S hS (pullback f g) (pullback.snd f g) x'))
    (hgor : IsGorensteinAt B S hS (pullback.snd f g) x') :
    IsGorensteinAt B S hS f
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
  exact (isGorensteinAt_source_iff_of_chartData B S hS C).mpr
    (_root_.AlgebraicGeometry.Scheme.Hom.isGorensteinAt_of_pullback_of_flat_base _ _
      C.pFiber _ hflatScheme ((isGorensteinAt_pull_iff_of_chartData B S hS C).mp hgor))

end Statements

end Space

end AlgebraicGeometry

end
