module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints

/-!
# Proper morphisms of algebraic spaces with values in a larger universe

A morphism of algebraic spaces over a scheme `S` is *separated* when its relative diagonal is
a closed immersion, *closed* when the map it induces on points is a closed map, *universally
closed* when its base change along every morphism from an algebraic space is closed, and
*proper* when it is separated, of finite type and universally closed. For presheaves with
values in `Type u`, the universe of the schemes, those are the notions of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms` and
`StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed`. This file carries them for a value
universe `max w u` with `w` independent of `u`, as
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType` carries finite type, and
packages properness as a property of morphisms of the category
`AlgebraicGeometry.Space.AlgebraicSpacesULift`.

## Main definitions

* `AlgebraicGeometry.Space.IsClosedImmersionULift` and
  `AlgebraicGeometry.Space.IsSeparatedULift` are
  `AlgebraicGeometry.Space.IsClosedImmersion` and
  `AlgebraicGeometry.Space.IsSeparated` for presheaves of `Type (max w u)`.
* `AlgebraicGeometry.Space.IsClosedMorphismULift` and
  `AlgebraicGeometry.Space.UniversallyClosedULift` are
  `AlgebraicGeometry.Space.IsClosedMorphism` and
  `AlgebraicGeometry.Space.UniversallyClosed` for such presheaves.
* `AlgebraicGeometry.Space.IsProperULift` is `AlgebraicGeometry.Space.IsProper` for such
  presheaves, and `AlgebraicGeometry.Space.properPropertyULift` is it as a property of
  morphisms of the category of large-valued algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isClosedMap_pointsMapULift_of_isIso`: the map on points induced by
  an isomorphism of large-valued presheaves is a closed map.
* `AlgebraicGeometry.Space.IsProperULift.isSeparated`,
  `AlgebraicGeometry.Space.IsProperULift.isFiniteType` and
  `AlgebraicGeometry.Space.IsProperULift.universallyClosed` are the three conjuncts of
  properness, and `AlgebraicGeometry.Space.IsProperULift.mk'` assembles them.

## Implementation notes

Separatedness is the closed-immersion condition on the relative diagonal, and
`AlgebraicGeometry.Space.IsClosedImmersion` is `CategoryTheory.MorphismProperty.presheaf` of
the closed immersions of schemes, that is, the relative property along
`CategoryTheory.yoneda`. The universe-lifted form replaces `CategoryTheory.yoneda` by
`CategoryTheory.uliftYoneda.{w}`, as every notion of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued` does. Closed immersions of algebraic spaces
are representable by schemes, so the relative form applies to them; properness is *not*
representable by schemes, so it is assembled from its three conjuncts rather than tested on
represented base changes.

Finite type is `AlgebraicGeometry.Space.IsFiniteTypeULift`, the universe-lifted form of
Stacks 03XF part (3) — locally of finite type and quasi-compact — matching
`AlgebraicGeometry.Space.IsProper`, which is Stacks 03ZM read with the finite type of that
part. Mathlib's `AlgebraicGeometry.IsProper` instead carries only
`AlgebraicGeometry.LocallyOfFiniteType`, quasi-compactness being implied for schemes by
universal closedness; it is not used here.

Closedness is the closed-map condition for the point topology of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints`, the universe-lifted counterpart of
`AlgebraicGeometry.Space.pointTopology`. As there, the base changes in the universal
condition are presheaf fibre products and algebraicity of the fibre product is not needed to
state the condition, while algebraicity of the covering object is part of the condition and
so is a hypothesis of the quantifier, as in the source.

As elsewhere the predicates are stated for arbitrary morphisms of presheaves, algebraicity of
the source and target being imposed by clients, and they are abbreviations, so a client may
use the constituent conditions without a conversion lemma.

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

/-! ### Separated, closed, universally closed and proper morphisms -/

section Defs

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe
`max w u` independent of the universe `u` of the schemes is a *closed immersion* when it is
representable by objects of the site with closed immersions of schemes for base changes.
This is `AlgebraicGeometry.Space.IsClosedImmersion` with the scheme-valued points taken to be
the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
abbrev IsClosedImmersionULift (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f

/-- A morphism of algebraic spaces over `S` with values in a universe `max w u` independent of
the universe `u` of the schemes is *separated* when its relative diagonal is a closed
immersion. This is `AlgebraicGeometry.Space.IsSeparated` for such presheaves. -/
abbrev IsSeparatedULift (f : F ⟶ G) : Prop :=
  IsClosedImmersionULift.{w} B S hS (pullback.diagonal f)

/-- A morphism of algebraic spaces over `S` with values in a universe `max w u` independent of
the universe `u` of the schemes is *closed* when the map it induces on points is a closed map
for the topology detected by universe-lifted scheme-valued points. This is
`AlgebraicGeometry.Space.IsClosedMorphism` for such presheaves. -/
abbrev IsClosedMorphismULift (f : F ⟶ G) : Prop :=
  letI := pointTopologyULift.{w} B S hS F
  letI := pointTopologyULift.{w} B S hS G
  IsClosedMap (pointsMapULift B S hS F f)

/-- A morphism of algebraic spaces over `S` with values in a universe `max w u` independent of
the universe `u` of the schemes is *universally closed* when its base change along every
morphism to its target from such an algebraic space is closed. This is
`AlgebraicGeometry.Space.UniversallyClosed` for such presheaves. -/
abbrev UniversallyClosedULift (f : F ⟶ G) : Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)), IsAlgebraicSpaceULift.{w} B S hS Z →
    ∀ g : Z ⟶ G, IsClosedMorphismULift.{w} B S hS (pullback.fst g f)

/-- A morphism of algebraic spaces over `S` with values in a universe `max w u` independent of
the universe `u` of the schemes is *proper* when it is separated, of finite type and
universally closed. This is `AlgebraicGeometry.Space.IsProper` for such presheaves. -/
abbrev IsProperULift (f : F ⟶ G) : Prop :=
  IsSeparatedULift.{w} B S hS f ∧ IsFiniteTypeULift.{w} B S hS f ∧
    UniversallyClosedULift.{w} B S hS f

end Defs

/-! ### Closedness on points of an isomorphism -/

section Comparisons

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopologyULift

/-- The map on points induced by an isomorphism of presheaves on the big fppf site of `S` with
values in a universe `max w u` independent of the universe `u` of the schemes is a closed map. -/
theorem isClosedMap_pointsMapULift_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ⟶ G) [IsIso e] :
    IsClosedMap (pointsMapULift.{w} B S hS F e) := by
  have h : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G) x,
      pointsMapULift B S hS G e.inv (pointsMapULift B S hS F e.hom x) = x := fun {F G} e x ↦ by
    rw [← Function.comp_apply (f := pointsMapULift B S hS G e.inv), ← pointsMapULift_comp,
      e.hom_inv_id, pointsMapULift_id, id]
  intro W hW
  have himg : pointsMapULift B S hS F e '' W = pointsMapULift B S hS G (inv e) ⁻¹' W :=
    congrFun (Set.image_eq_preimage_of_inverse (h (asIso e)) (h (asIso e).symm)) W
  rw [himg]
  exact hW.preimage (continuous_pointsMapULift B S hS (inv e))

/-- If a morphism of presheaves on the big fppf site of `S` with values in a larger universe
becomes, after precomposition with an isomorphism, a morphism whose map on points is closed,
then its own map on points is closed. -/
theorem isClosedMap_pointsMapULift_of_comp_isIso
    {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ⟶ F') [IsIso e]
    {g : F' ⟶ G} {f : F ⟶ G} (hfg : e ≫ g = f)
    (hg : IsClosedMap (pointsMapULift.{w} B S hS F' g)) :
    IsClosedMap (pointsMapULift.{w} B S hS F f) := by
  subst hfg
  rw [pointsMapULift_comp]
  exact IsClosedMap.comp hg (isClosedMap_pointsMapULift_of_isIso B S hS e)

/-- If `p` and `q` form a pullback of `g` and `f`, the closedness of the map on points of the
canonical first projection implies that of `p`. -/
private theorem isClosedMap_pointsMapULift_of_isPullback
    {Z F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {g : Z ⟶ G} {f : F ⟶ G}
    {p : P ⟶ Z} {q : P ⟶ F} (hpb : IsPullback p q g f)
    (h : IsClosedMap (pointsMapULift.{w} B S hS _ (pullback.fst g f))) :
    IsClosedMap (pointsMapULift.{w} B S hS _ p) :=
  isClosedMap_pointsMapULift_of_comp_isIso B S hS hpb.isoPullback.hom
    hpb.isoPullback_hom_fst h

/-- Universal closedness of a morphism is unchanged by precomposing with an isomorphism of
presheaves. -/
theorem universallyClosedULift_precomp
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G) (f : G ⟶ K)
    (hf : UniversallyClosedULift.{w} B S hS f) :
    UniversallyClosedULift.{w} B S hS (e.hom ≫ f) := by
  intro Z hZalg g
  have hpb : IsPullback (pullback.fst g (e.hom ≫ f))
      (pullback.snd g (e.hom ≫ f) ≫ e.hom) g f :=
    (IsPullback.of_hasPullback g (e.hom ≫ f)).of_iso (Iso.refl _) (Iso.refl _) e
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact isClosedMap_pointsMapULift_of_isPullback B S hS hpb (hf Z hZalg g)

/-- Universal closedness of a morphism is unchanged by postcomposing with an isomorphism of
presheaves. -/
theorem universallyClosedULift_postcomp
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : G ≅ K) (f : F ⟶ G)
    (hf : UniversallyClosedULift.{w} B S hS f) :
    UniversallyClosedULift.{w} B S hS (f ≫ e.hom) := by
  intro Z hZalg g
  have hpb : IsPullback (pullback.fst g (f ≫ e.hom)) (pullback.snd g (f ≫ e.hom))
      (g ≫ e.inv) f :=
    (IsPullback.of_hasPullback g (f ≫ e.hom)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.symm (by simp) (by simp) (by simp) (by simp)
  exact isClosedMap_pointsMapULift_of_isPullback B S hS hpb (hf Z hZalg (g ≫ e.inv))

end Comparisons

/-! ### The conjuncts of properness, and properness as a morphism property -/

section Permanence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}

/-- A proper morphism of large-valued algebraic spaces is separated. -/
theorem IsProperULift.isSeparated {f : F ⟶ G} (h : IsProperULift.{w} B S hS f) :
    IsSeparatedULift.{w} B S hS f := h.1

/-- A proper morphism of large-valued algebraic spaces is of finite type. -/
theorem IsProperULift.isFiniteType {f : F ⟶ G} (h : IsProperULift.{w} B S hS f) :
    IsFiniteTypeULift.{w} B S hS f := h.2.1

/-- A proper morphism of large-valued algebraic spaces is universally closed. -/
theorem IsProperULift.universallyClosed {f : F ⟶ G} (h : IsProperULift.{w} B S hS f) :
    UniversallyClosedULift.{w} B S hS f := h.2.2

/-- Properness of a morphism of large-valued algebraic spaces follows from its three
conjuncts. -/
theorem IsProperULift.mk' {f : F ⟶ G} (hsep : IsSeparatedULift.{w} B S hS f)
    (hft : IsFiniteTypeULift.{w} B S hS f) (huc : UniversallyClosedULift.{w} B S hS f) :
    IsProperULift.{w} B S hS f := ⟨hsep, hft, huc⟩

end Permanence

section Properties

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being separated, as a property of morphisms in the category of algebraic spaces over `S`
with values in `Type (max w u)`. -/
abbrev separatedPropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsSeparatedULift.{w} B S hS f.hom

/-- Being universally closed, as a property of morphisms in the category of algebraic spaces
over `S` with values in `Type (max w u)`. -/
abbrev universallyClosedPropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => UniversallyClosedULift.{w} B S hS f.hom

/-- Being proper, as a property of morphisms in the category of algebraic spaces over `S` with
values in `Type (max w u)`. -/
abbrev properPropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsProperULift.{w} B S hS f.hom

/-- Properness of morphisms of large-valued algebraic spaces is the infimum of its three
constituent properties. -/
theorem properPropertyULift_eq_inf :
    properPropertyULift.{w} B S hS =
      separatedPropertyULift.{w} B S hS ⊓ finiteTypePropertyULift.{w} B S hS ⊓
        universallyClosedPropertyULift.{w} B S hS := by
  ext X Y f
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- Separatedness is invariant under isomorphisms of algebraic spaces over `S` with values in
`Type (max w u)`. -/
instance separatedPropertyULift_respectsIso :
    (separatedPropertyULift.{w} B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage
    ((MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})).diagonal
    (ObjectProperty.ι _)

/-- Universal closedness is invariant under isomorphisms of algebraic spaces over `S` with
values in `Type (max w u)`. -/
instance universallyClosedPropertyULift_respectsIso :
    (universallyClosedPropertyULift.{w} B S hS).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ?_) (fun e f hf => ?_)
  · have := AlgebraicGeometry.Space.isIso_hom_of_iso B S hS e
    exact universallyClosedULift_precomp B S hS (asIso e.hom.hom) f.hom hf
  · have := AlgebraicGeometry.Space.isIso_hom_of_iso B S hS e
    exact universallyClosedULift_postcomp B S hS (asIso e.hom.hom) f.hom hf

/-- Properness is invariant under isomorphisms of algebraic spaces over `S` with values in
`Type (max w u)`. -/
instance properPropertyULift_respectsIso :
    (properPropertyULift.{w} B S hS).RespectsIso := by
  rw [properPropertyULift_eq_inf]
  infer_instance

end Properties

end AlgebraicGeometry.Space

end
