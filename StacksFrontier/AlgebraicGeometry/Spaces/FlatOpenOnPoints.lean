module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints

/-!
# Flat morphisms locally of finite presentation are universally open (Stacks 042S)

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S`
which is flat and locally of finite presentation induces an open map on the underlying
topological spaces of Tag 03BX, and so does every one of its base changes.

The proof is the one the source gives, read through the chart conditions that define the two
hypotheses. Choose a surjective étale scheme chart `q : yoneda.obj V ⟶ G` of the target and lift
it through `f` to a surjective étale scheme chart `p : yoneda.obj U ⟶ F` of the source sitting
over a morphism `α : U ⟶ V` of the site (Tag 02X1). Because flatness and local finite
presentation of a morphism of algebraic spaces are by definition the corresponding properties of
the morphism of schemes underlying *every* commuting square of étale charts, the single square
produced by that lift already gives that `α` is flat and locally of finite presentation on
schemes; a flat morphism of schemes locally of finite presentation is universally open, hence
open. On points `|p|` is a continuous surjection (Tag 03H5 and clause (2) of Tag 03BX), `|α|` is
open because `α` is open on schemes and the point topology of a represented presheaf is the
topology of the representing scheme, and `|q|` is open by clause (3) of Tag 03BX. So
`|f| ∘ |p| = |q| ∘ |α|` is open and `|p|` is a continuous surjection, which makes `|f|` open.

Universal openness then needs no further geometry: a base change of `f` is again flat
(Tag 03MO) and locally of finite presentation (Tag 03XR).

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isOpenMap_pointsMap_yonedaMap_of_isOpenMap`: a morphism of the site
  which is open on schemes is open on the points of the represented presheaves.
* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation`: a
  flat morphism of algebraic spaces locally of finite presentation is open on points.
* `AlgebraicGeometry.Space.universallyOpen_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation`:
  **Stacks 042S**, the same for every base change.

## Implementation notes

The tag is carried by the universal statement alone, since that is what Tag 042S concludes;
the non-universal form above it is the base change along the identity and is the shape the
consumers of this file take, so it is stated separately and left untagged rather than given a
second site on the same sentence.

Universal openness is phrased over an arbitrary cartesian square of algebraic spaces over `S`
rather than over a chosen fibre product, so it applies to whichever base change a consumer
already has in hand.

`AlgebraicGeometry.Space.isOpenMap_pointsMap_yonedaMap_of_isOpenMap` subsumes
`AlgebraicGeometry.Space.isOpenMap_pointsMap_yonedaMap_of_etale`
(`StacksFrontier/AlgebraicGeometry/Spaces/PointsTopologyUnique.lean`), which is its instance at an
étale morphism: that proof uses étaleness only to produce openness of the morphism of schemes.
Rewriting the étale one as a corollary of it would be the natural arrangement; it is **not** done
here, and `PointsTopologyUnique.lean`, which carries Tag 03BX, keeps its own proof.

These are **Chapter 67 results**, alongside `AlgebraicGeometry.Space.isFlat_of_isSmooth` (04TA)
and `AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fpqc` (041W).

## References

* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site over `S` whose morphism of schemes is open is open on the
points of the represented presheaves: by clause (1) of Tag 03BX the point topology of a
represented presheaf is the topology of the representing scheme. -/
theorem isOpenMap_pointsMap_yonedaMap_of_isOpenMap {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : IsOpenMap ((BigFppfOver.toScheme B S hS).map h).base) :
    @IsOpenMap _ _ (pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS (yoneda.obj V))
      (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) := by
  intro W hW
  rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_exists_preimage] at hW
  obtain ⟨V₀, hV₀, rfl⟩ := hW
  rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_exists_preimage]
  refine ⟨(BigFppfOver.toScheme B S hS).map h '' V₀, hh V₀ hV₀, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨v, hv, hvy⟩
    obtain ⟨x, hx⟩ := surjective_pointsToScheme B S hS U v
    refine ⟨x, by rwa [hx], injective_pointsToScheme B S hS V ?_⟩
    rw [pointsToScheme_pointsMap, hx, hvy]
  · rintro ⟨x, hx, hxy⟩
    refine ⟨pointsToScheme B S hS U x, hx, ?_⟩
    rw [← pointsToScheme_pointsMap, hxy]

/-- **The open half of Stacks 042S.** A flat morphism of algebraic spaces over `S` which is
locally of finite presentation induces an open map on points.

This is the base change along the identity of
`AlgebraicGeometry.Space.universallyOpen_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation`
below, which carries the tag; it is stated first because it is what the proof of that one
reduces to and what consumers use. -/
theorem isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hflat : IsFlat B S hS f) (hlfp : IsLocallyOfFinitePresentation B S hS f) :
    @IsOpenMap _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) := by
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hG.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V q hqSurj hqEtale
  have : Flat ((BigFppfOver.toScheme B S hS).map α) :=
    hflat U V p q α hpEtale hqEtale hcomm.symm
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α) :=
    hlfp U V p q α hpEtale hqEtale hcomm.symm
  have : UniversallyOpen ((BigFppfOver.toScheme B S hS).map α) :=
    UniversallyOpen.of_flat _
  let _tU : TopologicalSpace (points B S hS (yoneda.obj U)) :=
    pointTopology B S hS (yoneda.obj U)
  let _tV : TopologicalSpace (points B S hS (yoneda.obj V)) :=
    pointTopology B S hS (yoneda.obj V)
  let _tF : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  let _tG : TopologicalSpace (points B S hS G) := pointTopology B S hS G
  have hcompfun : pointsMap B S hS F f ∘ pointsMap B S hS (yoneda.obj U) p =
      pointsMap B S hS (yoneda.obj V) q ∘
        pointsMap B S hS (yoneda.obj U) (yoneda.map α) := by
    rw [← pointsMap_comp, ← pointsMap_comp, hcomm]
  refine IsOpenMap.of_comp (continuous_pointsMap B S hS p)
    ((surjective_iff_surjective_pointsMap B S hS F hF U p).mp hpSurj) ?_
  rw [hcompfun]
  exact (isOpenMap_pointsMap_of_etale B S hS hG V q hqEtale).comp
    (isOpenMap_pointsMap_yonedaMap_of_isOpenMap B S hS α (Scheme.Hom.isOpenMap _))

/-- **Stacks 042S.** A flat morphism of algebraic spaces over `S` which is locally of finite
presentation is universally open: in every cartesian square of algebraic spaces over `S`, the
base change of such a morphism induces an open map on the points of Tag 03BX.

The base change is again flat by Tag 03MO and again locally of finite presentation by
Tag 03XR, so this is the open half above,
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation`,
applied to it. -/
@[ega "IV 2.4.6" "in particular clause"]
theorem universallyOpen_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation
    {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Z ⟶ Y} {f' : W ⟶ Z} {g' : W ⟶ X}
    (sq : IsPullback g' f' f g)
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    @IsOpenMap _ _ (pointTopology B S hS W.obj) (pointTopology B S hS Z.obj)
      (pointsMap B S hS W.obj f'.hom) :=
  isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS W.property Z.property
    f'.hom ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hflat)
    ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hlfp)

end AlgebraicGeometry.Space

end
