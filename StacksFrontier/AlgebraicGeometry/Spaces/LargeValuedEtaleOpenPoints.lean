module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen

/-!
# Étale morphisms are open on points, for a value universe larger than the schemes

Let `S` be a scheme contained in a big fppf site `B`. Clause (3) of **Stacks 03BX** says that a
morphism of presheaves on the big fppf site of `S` each of whose represented base changes is an
étale morphism of schemes is open on the point sets of Stacks 03BU. That is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen` for presheaves with values in
`Type u`, the value universe of the site. This file proves it for presheaves with values in a
universe `max w u` independent of the universe `u` of the schemes, which is where a formal
algebraic space lives: it is a sheaf of `Type (u + 1)`.

Nothing here is a transfer along the universe lift. The point sets, their topology and the
map on points are defined for an *arbitrary* presheaf of `Type (max w u)` in
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints`, the only change from the value
universe of the site being that the scheme-valued points are morphisms out of
`CategoryTheory.uliftYoneda.{w}.obj U`. So the argument runs in that generality unchanged, and
the statements below carry no smallness hypothesis — which matters, because a formal algebraic
space need not be the universe lift of a presheaf of `Type u`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_pointsULift_of_isPullback` and
  `AlgebraicGeometry.Space.preimage_image_pointsMapULift_of_isPullback`: the comparison map
  from the points of a fibre product to the fibre product of the point sets is surjective, in
  the form in which the transfer of openness along a base change uses it.
* `AlgebraicGeometry.Space.isOpen_uliftYoneda_iff_isSchemeOpenULift`: **Stacks 03BX**,
  clause (1), for a value universe independent of the universe of the schemes.
* `AlgebraicGeometry.Space.isOpenMap_pointsMapULift_uliftYoneda_map_iff`: a morphism of the
  site is open on points exactly when the underlying morphism of schemes is open.
* `AlgebraicGeometry.Space.isOpenMap_pointsMapULift_of_relativeEtale`: **Stacks 03BX**,
  clause (3), for a value universe independent of the universe of the schemes.
* `AlgebraicGeometry.Space.isQuotientMap_pointsMapULift_of_relativeEtale` and
  `AlgebraicGeometry.Space.pointTopologyULift_eq_coinduced_of_relativeEtale`: such a morphism
  which is in addition surjective on points is a quotient map on points, so the point
  topology of the target is the quotient topology of an étale atlas.

## Implementation notes

The hypothesis of clause (3) is relative representability of the morphism along the
universe-lifted Yoneda embedding together with étaleness of the underlying morphism of schemes
of every represented base change, that is
`CategoryTheory.MorphismProperty.relative (CategoryTheory.uliftYoneda.{w})` of the inverse
image of `AlgebraicGeometry.Etale`. This is what
`CategoryTheory.MorphismProperty.presheaf` is in the value universe of the site, and it is
weaker than `AlgebraicGeometry.Space.IsEtaleULift`, which quantifies over the étale
scheme-valued points of the source instead.

The surjectivity of the comparison map on points is already available for presheaves of
`Type (max w u)` as
`AlgebraicGeometry.Space.exists_point_of_isPullbackULift`; what this file adds on that front is
the set-theoretic consequence used by the transfer, that the preimage of an image is the image
of a preimage.

Of the two statements about a universe-lifted represented presheaf, the first repeats the
argument in the value universe of the site, and the second is obtained from that universe
through `AlgebraicGeometry.Space.pointsHomeomorphPointsULift`, the universe-lifted Yoneda
presheaf being the universe lift of the Yoneda presheaf.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology pointTopologyULift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of the map on points, elementwise -/

/-- The map on points of a composite of morphisms of presheaves with values in a universe
`max w u` independent of the universe `u` of the schemes, applied to a point. -/
theorem pointsMapULift_comp_apply
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (α : F ⟶ G) (β : G ⟶ H)
    (v : pointsULift.{w} B S hS F) :
    pointsMapULift B S hS F (α ≫ β) v =
      pointsMapULift B S hS G β (pointsMapULift B S hS F α v) := by
  simp only [pointsMapULift_comp, Function.comp_apply]

/-- A commuting square of presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes induces a commuting square of maps on points. -/
theorem pointsMapULift_apply_comm
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (hw : p ≫ f = q ≫ g)
    (v : pointsULift.{w} B S hS W) :
    pointsMapULift B S hS X f (pointsMapULift B S hS W p v) =
      pointsMapULift B S hS Z g (pointsMapULift B S hS W q v) := by
  rw [← pointsMapULift_comp_apply, ← pointsMapULift_comp_apply, hw]

/-! ### Surjectivity of the comparison map -/

/-- **Stacks 03H4** for presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes: a point of one middle term of a cartesian square and a point of
the other with the same image in the base are the images of a common point of the fibre
product. This is `AlgebraicGeometry.Space.exists_point_of_isPullbackULift` with the two
middle terms in the order of `AlgebraicGeometry.Space.exists_points_of_isPullback`. -/
@[stacks 03H4 "for a value universe independent of the universe of the schemes"]
theorem exists_pointsULift_of_isPullback
    {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (sq : IsPullback p q f g)
    (a : pointsULift.{w} B S hS X) (b : pointsULift.{w} B S hS Z)
    (hab : pointsMapULift B S hS X f a = pointsMapULift B S hS Z g b) :
    ∃ v : pointsULift.{w} B S hS W,
      pointsMapULift B S hS W p v = a ∧ pointsMapULift B S hS W q v = b :=
  exists_point_of_isPullbackULift.{w} B S hS sq a b hab

/-- For a cartesian square of presheaves with values in a universe `max w u` independent of
the universe `u` of the schemes, the preimage along the base map of the image of a set of
points is the image of its preimage. This is
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback` for such presheaves, and the
inclusion that is not formal is again surjectivity of the comparison map. -/
theorem preimage_image_pointsMapULift_of_isPullback
    {W Z W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (C : Set (pointsULift.{w} B S hS W)) :
    pointsMapULift B S hS Z' h ⁻¹' (pointsMapULift B S hS W p '' C) =
      pointsMapULift B S hS W' p' '' (pointsMapULift B S hS W' c ⁻¹' C) := by
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hxC, hx⟩
    obtain ⟨v, hv₁, hv₂⟩ := exists_pointsULift_of_isPullback.{w} B S hS sq x z hx
    exact ⟨v, by rwa [Set.mem_preimage, hv₁], hv₂⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, hv, pointsMapULift_apply_comm.{w} B S hS sq.w v⟩

/-! ### The point space of a universe-lifted represented presheaf -/

/-- **Stacks 03BX, clause (1)** for a value universe `max w u` independent of the universe `u`
of the schemes: on a universe-lifted represented presheaf the point topology is the topology
of the representing scheme, a set of points being open exactly when it is cut out by an open
subset of the scheme. -/
theorem isOpen_uliftYoneda_iff_isSchemeOpenULift (U : BigFppfOver B S hS)
    (W : Set (pointsULift.{w} B S hS ((uliftYoneda.{w}).obj U))) :
    IsOpen W ↔ IsSchemeOpenULift.{w} B S hS U W := by
  constructor
  · intro hW
    simpa only [pointsMapULift_id, Set.preimage_id] using hW U (𝟙 _)
  · rintro ⟨V, hV, hmem⟩ U' a
    obtain ⟨h, rfl⟩ : ∃ h : U' ⟶ U, (uliftYoneda.{w}).map h = a :=
      ⟨(uliftYoneda.{w}).preimage a, by simp⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map h ⁻¹' V,
      hV.preimage ((BigFppfOver.toScheme B S hS).map h).continuous, fun p ↦ ?_⟩
    rw [Set.mem_preimage, pointsMapULift_class, hmem, schemePointULift_map_uliftYoneda]
    rfl

/-- For a morphism of the big fppf site of `S`, the map induced on the points of the
universe-lifted represented presheaves is open exactly when the underlying map of schemes is
open: the two point spaces are those of the represented presheaves, by
`AlgebraicGeometry.Space.pointsHomeomorphPointsULift`, and the two maps correspond. -/
theorem isOpenMap_pointsMapULift_uliftYoneda_map_iff {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    IsOpenMap (pointsMapULift.{w} B S hS ((uliftYoneda.{w}).obj U) ((uliftYoneda.{w}).map h)) ↔
      IsOpenMap ⇑((BigFppfOver.toScheme B S hS).map h) := by
  let e₁ : points B S hS (yoneda.obj U) ≃ₜ pointsULift.{w} B S hS ((uliftYoneda.{w}).obj U) :=
    pointsHomeomorphPointsULift.{w} B S hS (yoneda.obj U)
  let e₂ : points B S hS (yoneda.obj V) ≃ₜ pointsULift.{w} B S hS ((uliftYoneda.{w}).obj V) :=
    pointsHomeomorphPointsULift.{w} B S hS (yoneda.obj V)
  have hnat : pointsMapULift.{w} B S hS ((uliftYoneda.{w}).obj U) ((uliftYoneda.{w}).map h) ∘ ⇑e₁
      = ⇑e₂ ∘ pointsMap B S hS (yoneda.obj U) (yoneda.map h) := by
    funext x
    induction x using Quot.ind
    rfl
  rw [← isOpenMap_pointsMap_yoneda_iff B S hS h, ← e₂.comp_isOpenMap_iff, ← hnat,
    e₁.comp_isOpenMap_iff']

/-! ### Stacks 03BX, clause (3), in a larger value universe -/

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes, each of whose represented base changes is an
open map of schemes, is open on the point sets of Stacks 03BU. This is
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafIsOpenMap` for such presheaves. -/
theorem isOpenMap_pointsMapULift_of_relativeIsOpenMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f) :
    IsOpenMap (pointsMapULift.{w} B S hS F f) := by
  intro C hC
  rw [isOpen_pointTopologyULift_iff]
  intro U b
  rw [← isOpen_uliftYoneda_iff_isSchemeOpenULift.{w} B S hS,
    preimage_image_pointsMapULift_of_isPullback.{w} B S hS (hf.rep.isPullback b)]
  exact (isOpenMap_pointsMapULift_uliftYoneda_map_iff.{w} B S hS (hf.rep.snd b)).mpr
    (hf.property_snd b) _
    (IsOpen.preimage (continuous_pointsMapULift B S hS (hf.rep.fst b)) hC)

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe `max w u`
independent of the universe `u` of the schemes, each of whose represented base changes is
étale, has all of its represented base changes open, because an étale morphism of schemes is
flat and locally of finite presentation, hence universally open. -/
@[sga "3 X 4.7" "more general"]
theorem relativeIsOpenMap_of_relativeEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f) :
    (MorphismProperty.inverseImage
      (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f :=
  ⟨hf.rep, fun _ _ g fst snd sq ↦ by
    have : Etale ((BigFppfOver.toScheme B S hS).map snd) := hf.property g fst snd sq
    exact Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map snd)⟩

/-- **Stacks 03BX, clause (3)** for a value universe `max w u` independent of the universe `u`
of the schemes: a morphism of presheaves on the big fppf site of `S` each of whose represented
base changes is an étale morphism of schemes is open on the point sets of Stacks 03BU.

Clause (3) of Stacks 03BX is the case of a universe-lifted represented source and an algebraic
space as target; neither hypothesis is used. -/
theorem isOpenMap_pointsMapULift_of_relativeEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f) :
    IsOpenMap (pointsMapULift.{w} B S hS F f) :=
  isOpenMap_pointsMapULift_of_relativeIsOpenMap.{w} B S hS f
    (relativeIsOpenMap_of_relativeEtale.{w} B S hS f hf)

/-- An étale morphism of presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes which is surjective on points is a quotient map on points: it is
open and continuous, so the point topology of the target is the quotient topology. -/
@[sga "1 IX 2.2" "special case"]
theorem isQuotientMap_pointsMapULift_of_relativeEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f)
    (hsurj : Function.Surjective (pointsMapULift.{w} B S hS F f)) :
    Topology.IsQuotientMap (pointsMapULift.{w} B S hS F f) :=
  (isOpenMap_pointsMapULift_of_relativeEtale.{w} B S hS f hf).isQuotientMap
    (continuous_pointsMapULift B S hS f) hsurj

/-- The point topology of a presheaf with values in a universe `max w u` independent of the
universe `u` of the schemes which receives an étale morphism, surjective on points, is the
quotient topology of the point topology of the source. -/
theorem pointTopologyULift_eq_coinduced_of_relativeEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f)
    (hsurj : Function.Surjective (pointsMapULift.{w} B S hS F f)) :
    pointTopologyULift.{w} B S hS G =
      TopologicalSpace.coinduced (pointsMapULift.{w} B S hS F f)
        (pointTopologyULift.{w} B S hS F) :=
  (isQuotientMap_pointsMapULift_of_relativeEtale.{w} B S hS f hf hsurj).eq_coinduced

end AlgebraicGeometry.Space

end
