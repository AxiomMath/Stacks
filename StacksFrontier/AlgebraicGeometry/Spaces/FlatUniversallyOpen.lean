module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique

/-!
# A flat morphism locally of finite presentation is open on points

A morphism of algebraic spaces over a scheme `S` which is flat and locally of finite
presentation is open on points. For morphisms of schemes this is Stacks 01UA, available as
Mathlib's `AlgebraicGeometry.UniversallyOpen.of_flat`; the content here is the passage to
algebraic spaces, in the form of a direct chart argument for openness.

Universal openness itself — Stacks 042S — is
`AlgebraicGeometry.Space.universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Flat.lean`, which obtains it from the
criterion of Stacks 03Z5; what is proved here is the unquantified openness statement, read off
the charts without going through that criterion.

The argument has two steps, and both are reductions to the point topology of a *scheme*.

First suppose the target is a represented presheaf `h_V`. An étale atlas `a : h_U ⟶ X` of the
source turns `f` into a morphism of the site `h : U ⟶ V`, with `h_U ⟶ h_V` equal to `a ≫ f`;
that morphism of the site is flat and locally of finite presentation as a morphism of schemes,
because flatness and local finite presentation of a morphism of algebraic spaces are by
definition conditions on the morphisms of schemes underlying commuting squares of étale charts
(Stacks 03MJ, condition (1)) and the square whose target edge is the identity of `V` is such a
square. So it is universally open, hence open, hence — by
`AlgebraicGeometry.Space.isOpenMap_pointsMap_yoneda_iff` — open on points; and `|a|` is a
continuous surjection, so `|f|` is open.

In general an étale atlas `b : h_V ⟶ Y` of the target is open on points (clause (3) of Stacks
03BX), continuous and surjective, hence a quotient map, so a set of points of `Y` is open
exactly when its preimage in `|V|` is. That preimage of the image `|f| '' W` is, by
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback`, the image of a preimage of
`W` along the two projections of `V ×_Y X`, whose first projection is the first case.

## Main results

* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation_yoneda`:
  the represented-target case.
* `AlgebraicGeometry.Space.isOpenMorphism_of_isFlat_of_isLocallyOfFinitePresentation`: a flat
  morphism of algebraic spaces locally of finite presentation is open.

## Implementation notes

The topology is `AlgebraicGeometry.Space.pointTopology`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Open.lean`; see the implementation notes
there for why that is the topology Stacks 03BX characterizes.

No locality of flatness or of local finite presentation on the target is used, and neither
property has to be transported through a criterion: both are consumed in the chart form in
which they are defined, and the only geometry is Mathlib's Stacks 01UA for schemes.

## References

* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A flat morphism locally of finite presentation from an algebraic space to a *represented*
presheaf is open on points.

The étale atlas of the source, composed with the morphism, is a morphism of the site; it sits
in a commuting square of étale charts whose target edge is the identity, so it is flat and
locally of finite presentation as a morphism of schemes, hence universally open by Stacks 01UA
and in particular an open map. Openness on points transfers from that morphism of schemes by
`AlgebraicGeometry.Space.isOpenMap_pointsMap_yoneda_iff`, and descends through the atlas
because the atlas is a continuous surjection on points. -/
@[sga "3 XVI 2.1" "more general"]
theorem isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation_yoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (V : BigFppfOver B S hS) (f : F ⟶ yoneda.obj V)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    IsOpenMap (pointsMap B S hS F f) := by
  obtain ⟨U, a, hasurj, haetale⟩ := hF.exists_atlas
  have hh : yoneda.map (yoneda.preimage (a ≫ f)) = a ≫ f := yoneda.map_preimage _
  have hsq : yoneda.map (yoneda.preimage (a ≫ f)) ≫ yoneda.map (𝟙 V) = a ≫ f := by
    simp
  have hflatScheme : Flat ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))) :=
    hflat U V a (yoneda.map (𝟙 V)) _ haetale (presheaf_yoneda_map_id_etale B S hS V) hsq
  have hfpScheme : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))) :=
    hfp U V a (yoneda.map (𝟙 V)) _ haetale (presheaf_yoneda_map_id_etale B S hS V) hsq
  have hopenScheme : IsOpenMap
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))) :=
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))).isOpenMap
  have hcomp : IsOpenMap (pointsMap B S hS (yoneda.obj U) (a ≫ f)) := by
    rw [← hh]
    exact (isOpenMap_pointsMap_yoneda_iff B S hS (yoneda.preimage (a ≫ f))).mpr hopenScheme
  rw [pointsMap_comp] at hcomp
  exact IsOpenMap.of_comp (continuous_pointsMap B S hS a)
    ((surjective_iff_surjective_pointsMap B S hS F hF U a).mp hasurj) hcomp

/-- **Stacks 042S.** A flat morphism of algebraic spaces over `S` which is locally of finite
presentation is open on points.

An étale atlas of the target is an open continuous surjection on points, hence a quotient map,
so it is enough to see that the base change of `f` to it is open on points; that base change
has a represented target and is still flat and locally of finite presentation, so
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation_yoneda`
applies to it, and the preimage of the image is the image of a preimage by
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback`. -/
@[sga "3 V 10.1.1" "more general"]
theorem isOpenMorphism_of_isFlat_of_isLocallyOfFinitePresentation
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    IsOpenMorphism B S hS f := by
  obtain ⟨V, b, hbsurj, hbetale⟩ := hG.exists_atlas
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hQ : IsAlgebraicSpace B S hS (pullback b f) :=
    isAlgebraicSpace_pullback B S hS b f hV hF hG
  have hflat' : IsFlat B S hS (pullback.fst b f) :=
    holdsOnEveryEtaleChart_pullback_fst_of_isAlgebraicSpace B S hS _
      Flat.isEtaleLocalOnSourceAndTarget inferInstance hF hG hV b f hflat
  have hfp' : IsLocallyOfFinitePresentation B S hS (pullback.fst b f) :=
    holdsOnEveryEtaleChart_pullback_fst_of_isAlgebraicSpace B S hS _
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget inferInstance hF hG hV b f hfp
  have hopen' : IsOpenMap (pointsMap B S hS (pullback b f) (pullback.fst b f)) :=
    isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation_yoneda B S hS hQ V _
      hflat' hfp'
  have hquot : Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj V) b) :=
    (isOpenMap_pointsMap_of_etale B S hS hG V b hbetale).isQuotientMap
      (continuous_pointsMap B S hS b)
      ((surjective_iff_surjective_pointsMap B S hS G hG V b).mp hbsurj)
  intro W hW
  rw [← hquot.isOpen_preimage,
    preimage_image_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback b f).flip W]
  exact hopen' _ (hW.preimage (continuous_pointsMap B S hS (pullback.snd b f)))

end AlgebraicGeometry.Space

end
