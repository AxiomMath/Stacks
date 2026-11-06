module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction

/-!
# The small étale site of a representable étale morphism of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` which is representable by algebraic spaces and étale. Stacks 0DED
attaches to `f` a functor `j : X_étale ⟶ Y_étale` between the small étale sites of Stacks 0DEA,
asserts that `j` is cocontinuous, that the morphism of topoi `f_small` of Stacks 0DEC, part (3),
is the morphism of topoi that Sites 00XO attaches to `j`, and that `j` is continuous as well, so
that Sites 00XR applies to it.

The small étale site of a formal algebraic space is by definition the small étale site of its
reduction, so `j` is postcomposition with the induced morphism of reductions
`X_red ⟶ Y_red`. Everything then follows from the case of algebraic spaces, Stacks 03LP, once
that morphism is known to be étale, and that is the content of the proof.

## The induced morphism of reductions is étale

The source proves it from `X_red = X ×_Y Y_red`: the fibre product is an algebraic space étale
over the reduced algebraic space `Y_red`, hence reduced, hence is the reduction of `X`. In this
library that identification is already available, for a representable *smooth* morphism, as
Stacks 0GB7 — `AlgebraicGeometry.FormalSpace.isReduction_pullback_reduction_of_smooth` together
with `AlgebraicGeometry.FormalSpace.isIso_of_isReduction_of_isPullback_of_smooth` — and an étale
morphism is smooth. So the morphism of reductions is, up to the comparison isomorphism, the
second projection of `X ×_Y Y_red`, which is a base change of `f` and therefore étale after
every further base change along a scheme-valued point of `Y_red`. Étaleness of morphisms of
schemes being étale local on the source and the target, the every-étale-chart condition of
Stacks 03MJ propagates from those base changes to the projection itself, and descends from the
value universe of the formal algebraic spaces to that of the algebraic spaces.

## The reduction is a given, not a construction

As in `StacksFrontier/AlgebraicGeometry/FormalSpace/EtaleSite.lean`, where Stacks 0DEA and
Stacks 0DEC are formalized, every declaration below is read against *given* reductions of `X` and
of `Y`, taking `AlgebraicGeometry.FormalSpace.Reduction` data for each as arguments. Such data
exist for every formal algebraic space, by Stacks 0AIN —
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`. This is not a
weakening of the content of Stacks 0DED, whose small étale sites are those of the reductions in
the source statement too.

## Main definitions

* `AlgebraicGeometry.FormalSpace.Reduction.smallEtalePostcomp`: **Stacks 0DED**, the functor
  `j : X_étale ⟶ Y_étale`.
* `AlgebraicGeometry.FormalSpace.Reduction.smallToposMorphism_pushforwardIso`: **Stacks 0DED**,
  the identification of `f_small` with the morphism of topoi of Sites 00XO attached to `j`.
* `AlgebraicGeometry.FormalSpace.Reduction.smallToposMorphism_inverseImageObjObjIso`:
  **Stacks 0DED**, the formula on sections that Sites 00XR gives for a functor which is
  continuous as well as cocontinuous.

## Main results

* `AlgebraicGeometry.FormalSpace.Reduction.isEtale_map`: **Stacks 0DED**, the induced morphism
  of reductions is étale. This is the content of the proof.
* `AlgebraicGeometry.FormalSpace.Reduction.smallEtalePostcomp_isCocontinuous` and
  `AlgebraicGeometry.FormalSpace.Reduction.smallEtalePostcomp_isContinuous`: **Stacks 0DED**,
  the two site properties of `j`.

## Implementation notes

Étaleness and smoothness of `f` are the conditions of Stacks 03XZ at the corresponding
properties of morphisms of algebraic spaces, that is `AlgebraicGeometry.Space.HasPropertyULift`,
exactly as étaleness of an atlas arrow is recorded in
`AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` and smoothness in Stacks 0GB7. Passing
from the étale to the smooth form needs a step, because the étale form is the relative condition
of Stacks 03FR while the smooth form is the every-étale-chart condition of Stacks 03MJ: for a
morphism whose target is a universe-lifted Yoneda presheaf — which is the shape of every
represented base change — both edges of a commuting square of étale charts come from morphisms
of the site, so the square is a factorisation there and étale cancellation applies. That step is
`holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site`, used once for smoothness and once for
étaleness.

Nothing about the sites or the topoi is reproved: the three site-level declarations are
`AlgebraicGeometry.Space.smallEtalePostcomp` and its two continuity properties, and the two
topos-level ones are `AlgebraicGeometry.Space.smallToposMorphism_pushforwardIso` and
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageObjObjIso`, all of Stacks 03LP, applied
to the induced morphism of reductions.

## References

* [Stacks Project, Tag 0DED](https://stacks.math.columbia.edu/tag/0DED)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From the relative étale condition to the every-étale-chart condition -/

/-- An étale morphism of algebraic spaces over `S`, in the value universe of the formal
algebraic spaces, whose target is a universe-lifted Yoneda presheaf satisfies the
every-étale-chart condition of Stacks 03MJ for any property of morphisms of schemes which
holds for étale morphisms.

Because the target is a universe-lifted Yoneda presheaf, both edges of a commuting square of
étale charts that end at it are images of morphisms of the site, by full faithfulness of the
universe-lifted Yoneda embedding: the chart `b` of the target, and the composite `a ≫ m` of the
chart of the source with the morphism, which is an étale chart of the target because `m` is
étale. The square then says that the first of the two morphisms of the site factors the second
through `h`, so the scheme morphism underlying `h` is étale by cancellation of étale morphisms,
and `P` holds of it.

Neither an atlas of the source nor étale locality of `P` is needed: the cancellation happens
among morphisms of the site rather than among charts, so the only input is that `P` holds for
étale morphisms of schemes. -/
theorem holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site
    (P : MorphismProperty Scheme.{u})
    (hPE : ∀ {A C : Scheme.{u}} (k : A ⟶ C), Etale k → P k)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {U : BigFppfOver B S hS} (m : F ⟶ (uliftYoneda.{u + 1}).obj U)
    (hm : Space.IsEtaleULift.{u + 1} B S hS m) :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P m := by
  intro W V a b h ha hb hsq
  obtain ⟨β, rfl⟩ := (uliftYoneda.{u + 1}).map_surjective b
  obtain ⟨α, hα⟩ := (uliftYoneda.{u + 1}).map_surjective (a ≫ m)
  have hsite : h ≫ β = α := (uliftYoneda.{u + 1}).map_injective (by simp [hα, hsq])
  have hαE := (Space.relative_etale_uliftYoneda_map_iff B S hS α).1 (hα ▸ hm W a ha)
  have hβE := (Space.relative_etale_uliftYoneda_map_iff B S hS β).1 hb
  exact hPE _ (MorphismProperty.of_postcomp (W := @Etale.{u}) (W' := @Etale.{u}) _ _ hβE
    (by rw [← Functor.map_comp, hsite]; exact hαE))

/-- A morphism of fppf sheaves on the big fppf site of `S` which is representable by algebraic
spaces and étale is smooth in the sense of Stacks 03XZ, an étale morphism of schemes being
smooth. Each represented base change has a universe-lifted Yoneda presheaf as target, so
`holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site` applies to it. -/
private theorem hasPropertyULift_smooth_of_etale {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    Space.HasPropertyULift.{u + 1} B S hS (Space.smoothPropertyULift.{u + 1} B S hS)
      f.hom hrep := fun U ξ ↦
  holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    (fun k hk ↦ by have : Etale k := hk; infer_instance) _ (het U ξ)

/-- Étaleness in the sense of Stacks 03FR, in the value universe of the formal algebraic spaces,
is invariant under isomorphism of algebraic spaces over `S`: the relative étaleness condition on
charts is, being stable under base change. -/
private instance isEtaleULiftProperty_respectsIso :
    MorphismProperty.RespectsIso
      (fun (A C : Space.AlgebraicSpacesULift.{u + 1} B S hS) (g : A ⟶ C) ↦
        Space.IsEtaleULift.{u + 1} B S hS g.hom) := by
  have hiso : ∀ {A C : Space.AlgebraicSpacesULift.{u + 1} B S hS} (e : A ≅ C),
      IsIso e.hom.hom := fun e ↦
    ⟨e.inv.hom, congrArg (fun k ↦ k.hom) e.hom_inv_id,
      congrArg (fun k ↦ k.hom) e.inv_hom_id⟩
  refine MorphismProperty.RespectsIso.mk _ (fun e g hg ↦ ?_) (fun e g hg ↦ ?_)
  · intro V φ hφ
    have _ := hiso e
    have hpre := MorphismProperty.RespectsIso.postcomp
      ((MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})) e.hom.hom φ hφ
    simpa [Category.assoc] using hg V (φ ≫ e.hom.hom) hpre
  · intro V φ hφ
    have _ := hiso e
    exact MorphismProperty.RespectsIso.postcomp _ e.hom.hom _ (hg V φ hφ)

namespace Reduction

variable {B S hS} {X Y : FppfSheaf B S hS}

/-! ### Stacks 0DED: the induced morphism of reductions is étale -/

/-- **Stacks 0DED**, the content of the proof. Let `f : X ⟶ Y` be a morphism of formal algebraic
spaces over `S` which is representable by algebraic spaces and étale. Then the induced morphism
of reductions `X_red ⟶ Y_red` is an étale morphism of algebraic spaces over `S`.

The fibre product `X ×_Y Y_red` is a reduction of `X` and every comparison morphism
`X_red ⟶ X ×_Y Y_red` over `X` is an isomorphism — this is Stacks 0GB7, applicable because an
étale morphism is smooth — so the morphism of reductions is, up to that isomorphism, the second
projection of the fibre product. That projection is a base change of `f`, hence étale after
every further base change along a scheme-valued point of `Y_red`; étaleness being étale local on
the source and target, it satisfies the every-étale-chart condition of Stacks 03MJ, which
descends to the value universe of the algebraic spaces. -/
@[stacks 0DED "étaleness of the induced morphism of reductions, which is the content of the
  proof; read against given reductions, which Stacks 0AIN supplies"]
theorem isEtale_map (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (RX : Reduction B S hS X) (RY : Reduction B S hS Y)
    (f : X ⟶ Y) (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    Space.IsEtale B S hS (RX.map RY f).hom := by
  have hsmooth := hasPropertyULift_smooth_of_etale B S hS hrep het
  -- The fibre product `X ×_Y Y_red`, with its two projections.
  have sq : IsPullback (pullback.fst f RY.inclusion) (pullback.snd f RY.inclusion) f
      RY.inclusion := IsPullback.of_hasPullback f RY.inclusion
  have sqh : IsPullback (pullback.fst f RY.inclusion).hom (pullback.snd f RY.inclusion).hom
      f.hom RY.inclusion.hom :=
    sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  -- The comparison morphism `X_red ⟶ X ×_Y Y_red`, an isomorphism by Stacks 0GB7.
  set c : liftSheaf B S hS RX.space ⟶ pullback f RY.inclusion :=
    sq.lift RX.inclusion (liftSheafMap B S hS (RX.map RY f))
      (RX.liftSheafMap_map RY f).symm with hc
  have hcfst : c ≫ pullback.fst f RY.inclusion = RX.inclusion := sq.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd f RY.inclusion = liftSheafMap B S hS (RX.map RY f) :=
    sq.lift_snd _ _ _
  have _ : IsIso c :=
    isIso_of_isReduction_of_isPullback_of_smooth B S hS hX hY hrep hsmooth RX.isReduction
      RY.isReduction sq hcfst
  have _ : IsIso c.hom :=
    CategoryTheory.Functor.map_isIso
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) c
  -- The second projection is a base change of `f`, hence étale on every chart.
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback f RY.inclusion).obj :=
    (isReduction_pullback_reduction_of_smooth B S hS hX hY hrep hsmooth
      RY.isReduction sq).algebraic
  have hsndRep := Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
    (pullback.fst f RY.inclusion).hom (pullback.snd f RY.inclusion).hom f.hom
    RY.inclusion.hom sqh hrep
  have hsndProp := Space.hasPropertyULift_of_isPullback B S hS sqh hrep het
  have hsndChart : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (pullback.snd f RY.inclusion).hom :=
    Space.holdsOnEveryEtaleChartULift_of_forall_pullback_fst B S hS _
      AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget hPalg
      RY.isReduction.algebraic _ (fun U ξ ↦
        holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS _
          (fun _ hk ↦ hk) _ (hsndProp U ξ))
  -- Transport along the comparison isomorphism, then descend the value universe.
  have hlift : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (Functor.whiskerRight (RX.map RY f).hom uliftFunctor.{u + 1}) := by
    have hcomp := Space.holdsOnEveryEtaleChartULift_precomp B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) c.hom
      (pullback.snd f RY.inclusion).hom hsndChart
    have heq : c.hom ≫ (pullback.snd f RY.inclusion).hom =
        Functor.whiskerRight (RX.map RY f).hom uliftFunctor.{u + 1} :=
      congrArg (fun k : liftSheaf B S hS RX.space ⟶ liftSheaf B S hS RY.space ↦ k.hom) hcsnd
    rwa [heq] at hcomp
  have hchart : Space.HoldsOnEveryEtaleChart B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (RX.map RY f).hom :=
    (Space.holdsOnEveryEtaleChartULift_whiskerRight_iff.{u + 1} B S hS _
      (RX.map RY f).hom).mp hlift
  obtain ⟨U, V, a, b, h, ha, hb, haS, hw, hhE⟩ :=
    (Space.holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
      AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget RX.space.property
      RY.space.property (RX.map RY f).hom).mp hchart
  exact (Space.isEtale_iff_exists_etale_chart_square B S hS RX.space.property
    RY.space.property (RX.map RY f).hom).mpr ⟨U, V, a, b, h, hw.symm, haS, ha, hb, hhE⟩

/-! ### Stacks 0DED: the functor `j` and the identification of `f_small` -/

/-- **Stacks 0DED.** The functor `j : X_étale ⟶ Y_étale` attached to a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` which is representable by algebraic spaces and étale:
postcomposition of an étale scheme chart of `X_red` with the induced étale morphism of
reductions, which is the functor of Stacks 03LP at that morphism. -/
@[stacks 0DED "the functor `j : X_étale ⟶ Y_étale`; read against given reductions, which
  Stacks 0AIN supplies"]
noncomputable def smallEtalePostcomp (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (RX : Reduction B S hS X)
    (RY : Reduction B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    RX.SmallEtale ⥤ RY.SmallEtale :=
  Space.smallEtalePostcomp B S hS (RX.map RY f) (isEtale_map hX hY RX RY f hrep het)

/-- **Stacks 0DED.** The functor `j` is cocontinuous: a covering sieve of `jU` in `Y_étale`
pulls back to a covering sieve of `U` in `X_étale`. -/
@[stacks 0DED "cocontinuity of `j`; read against given reductions, which Stacks 0AIN
  supplies"]
instance smallEtalePostcomp_isCocontinuous (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (RX : Reduction B S hS X)
    (RY : Reduction B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    (smallEtalePostcomp hX hY RX RY f hrep het).IsCocontinuous RX.smallEtaleTopology
      RY.smallEtaleTopology :=
  Space.smallEtalePostcomp_isCocontinuous B S hS (RX.map RY f)
    (isEtale_map hX hY RX RY f hrep het)

/-- **Stacks 0DED.** The functor `j` is continuous as well, so Sites 00XR applies to it. -/
@[stacks 0DED "continuity of `j`, which is what makes Sites 00XR applicable; read against
  given reductions, which Stacks 0AIN supplies"]
instance smallEtalePostcomp_isContinuous (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (RX : Reduction B S hS X)
    (RY : Reduction B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    (smallEtalePostcomp hX hY RX RY f hrep het).IsContinuous RX.smallEtaleTopology
      RY.smallEtaleTopology :=
  Space.smallEtalePostcomp_isContinuous B S hS (RX.map RY f)
    (isEtale_map hX hY RX RY f hrep het)

set_option synthInstance.maxHeartbeats 200000 in
/-- **Stacks 0DED.** The morphism of topoi `f_small` of Stacks 0DEC, part (3), is the morphism
of topoi that Sites 00XO attaches to the cocontinuous functor `j`: its direct image is the
direct image of `j`. -/
@[stacks 0DED "`f_small` is the morphism of topoi that Sites 00XO attaches to `j`, identified on
  direct images; read against given reductions, which Stacks 0AIN supplies"]
noncomputable def smallToposMorphism_pushforwardIso (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (RX : Reduction B S hS X)
    (RY : Reduction B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    (RX.smallToposMorphism RY f).pushforward ≅
      (smallEtalePostcomp hX hY RX RY f hrep het).sheafPushforwardCocontinuous
        (Type (u + 1)) RX.smallEtaleTopology RY.smallEtaleTopology :=
  Space.smallToposMorphism_pushforwardIso B S hS (RX.map RY f)
    (isEtale_map hX hY RX RY f hrep het)

/-- **Stacks 0DED**, the consequence of continuity of `j` recorded by Sites 00XR: the inverse
image of `f_small` is restriction along `j`, so a section of `f_small^{-1} G` over an étale
chart `U` of `X_red` is a section of `G` over the chart `jU` of `Y_red`. -/
@[stacks 0DED "the formula on sections which Sites 00XR gives for `j`, continuous as well as
  cocontinuous; read against given reductions, which Stacks 0AIN supplies"]
noncomputable def smallToposMorphism_inverseImageObjObjIso
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (RX : Reduction B S hS X) (RY : Reduction B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep)
    (G : Sheaf RY.smallEtaleTopology (Type (u + 1))) (U : RX.SmallEtale) :
    ((RX.smallToposMorphism RY f).inverseImage.obj G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op ((smallEtalePostcomp hX hY RX RY f hrep het).obj U)) :=
  Space.smallToposMorphism_inverseImageObjObjIso B S hS (RX.map RY f)
    (isEtale_map hX hY RX RY f hrep het) G U

end Reduction

end AlgebraicGeometry.FormalSpace

end
