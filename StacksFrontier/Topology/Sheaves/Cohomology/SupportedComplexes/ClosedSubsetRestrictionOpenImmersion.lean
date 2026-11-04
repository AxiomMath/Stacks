module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedPullback

/-!
# The restriction of an open immersion to a closed subset, and its Cartesian square

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces, let `Z ⊆ X` be a subset and
let `Z' = f^{-1}(Z)`. The two subsets carry the restricted structure sheaves and `f` restricts to
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)`, giving the commutative square

```
(Z', 𝒪_{X'}|_{Z'}) --i'--> (X', 𝒪_{X'})
      |                          |
   f|_{Z'}                       f
      v                          v
(Z, 𝒪_X|_Z)  ------i----> (X, 𝒪_X)
```

This file proves the two geometric facts about that square that hold **when `f` is an open
immersion**: the horizontal arrow `f|_{Z'}` is again an open immersion, and the square is
Cartesian in `RingedSpace`. Together they are exactly the input of
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`, so the
base-change transformation of [Stacks, Tag 08HY] attached to the square is invertible, which is
the hypothesis `hbc` of `Stacks.Cohomology.SupportedComplexes.supportedPullbackMap`.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isOpenImmersion_closedSubsetRestriction`: for `f` an open
  immersion, `f|_{Z'}` is an open immersion.
* `Stacks.Cohomology.SupportedComplexes.isPullback_closedSubsetRestriction`: for `f` an open
  immersion, the square above is Cartesian in `RingedSpace`.
* `Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion`:
  for `f` an open immersion, the base-change transformation of [Stacks, Tag 08HY] for the
  square is an isomorphism on every object of `D(𝒪_X|_Z)`.

## Implementation notes

**Only for an open immersion.** Nothing here is claimed for a general morphism of ringed spaces;
`f` carries `AlgebraicGeometry.SheafedSpace.IsOpenImmersion` throughout. No general fibre product
of ringed spaces is constructed: the Cartesian square is produced directly from the universal
property of an open immersion, `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`, which
supplies both the lift and — `f` and `f|_{Z'}` being monomorphisms — its uniqueness.

**The open immersion.** The structure sheaf of `closedSubsetRingedSpace` is a *sheafified* inverse
image, so `c_iso` cannot be read off on sections. The proof goes through Mathlib's stalk criterion
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso` instead. The base map is the
restriction `Set.restrictPreimage` of an open embedding, hence an open embedding. For the stalks,
the commutativity of the square and `AlgebraicGeometry.PresheafedSpace.stalkMap.comp` give

`stalkMap i (f|_{Z'} z') ≫ stalkMap (f|_{Z'}) z' = stalkMap f (i' z') ≫ stalkMap i' z'`

in which the stalk maps of the two closed-subset inclusions are isomorphisms by
`AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection` (the Stacks Project's
"`i^{-1}𝒪_X = 𝒪_X|_Z`", which needs no hypothesis at all) and the stalk map of `f` is an
isomorphism because `f` is an open immersion. Cancelling the invertible left factor leaves the
stalk maps of `f|_{Z'}` invertible.

## References

* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.2 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [H : SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-! ### The restricted morphism is an open immersion -/

/-- The continuous map underlying `f|_{Z'}` is the restriction of the continuous map of `f` to
the preimage of `Z`. -/
theorem closedSubsetRestriction_base_eq :
    ⇑(closedSubsetRestriction f Z).hom.base = Z.restrictPreimage ⇑f.hom.base :=
  rfl

/-- The continuous map underlying `f|_{Z'}` is an open embedding, being the restriction of the
open embedding of `f` to the preimage of `Z`. -/
theorem isOpenEmbedding_closedSubsetRestriction_base :
    Topology.IsOpenEmbedding ⇑(closedSubsetRestriction f Z).hom.base := by
  rw [closedSubsetRestriction_base_eq]
  exact Set.restrictPreimage_isOpenEmbedding Z H.base_open

/-! The three steps of the stalk computation are stated at a variable category and applied with
`exact`: the stalks are indexed by points of a carrier that is the right type only at default
transparency, so a `rw` whose motive abstracts over the morphism or over the point is rejected
when the spaces are the concrete ones below. -/

/-- The stalk map of a composite is invertible when both factors' stalk maps are. -/
private theorem isIso_stalkMap_comp {C : Type*} [Category C] [Limits.HasColimits C]
    {P Q R : AlgebraicGeometry.PresheafedSpace C} (α : P ⟶ Q) (β : Q ⟶ R) (x : P)
    (hα : IsIso (α.stalkMap x)) (hβ : IsIso (β.stalkMap (α.base x))) :
    IsIso ((α ≫ β).stalkMap x) := by
  rw [AlgebraicGeometry.PresheafedSpace.stalkMap.comp]
  exact IsIso.comp_isIso' hβ hα

/-- Invertibility of a stalk map transported along an equality of morphisms. -/
private theorem isIso_stalkMap_of_eq {C : Type*} [Category C] [Limits.HasColimits C]
    {P Q : AlgebraicGeometry.PresheafedSpace C} (α β : P ⟶ Q) (h : α = β) (x : P)
    (hβ : IsIso (β.stalkMap x)) : IsIso (α.stalkMap x) := by
  subst h
  exact hβ

/-- Cancelling an invertible second factor from an invertible composite of stalk maps. -/
private theorem isIso_stalkMap_of_comp {C : Type*} [Category C] [Limits.HasColimits C]
    {P Q R : AlgebraicGeometry.PresheafedSpace C} (α : P ⟶ Q) (β : Q ⟶ R) (x : P)
    (hβ : IsIso (β.stalkMap (α.base x))) (hαβ : IsIso ((α ≫ β).stalkMap x)) :
    IsIso (α.stalkMap x) := by
  rw [AlgebraicGeometry.PresheafedSpace.stalkMap.comp] at hαβ
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (β.stalkMap (α.base x)) (α.stalkMap x) hβ hαβ

/-- **The stalk maps of `f|_{Z'}` are isomorphisms** when `f` is an open immersion. The square of
the restriction commutes, and three of the four stalk maps in it are known to be invertible: the
two stalk maps of the closed-subset inclusions unconditionally, and the stalk map of `f` because
`f` is an open immersion. -/
theorem isIso_stalkMap_closedSubsetRestriction (z' : closedSubsetPreimage f Z) :
    IsIso ((closedSubsetRestriction f Z).hom.stalkMap z') := by
  have hsq : (closedSubsetRestriction f Z).hom ≫ (closedSubsetInclusion X Z).hom =
      (closedSubsetInclusion X' (closedSubsetPreimage f Z)).hom ≫ f.hom :=
    congrArg (fun m : closedSubsetRingedSpace X' (closedSubsetPreimage f Z) ⟶ X => m.hom)
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z)
  have hi : IsIso ((closedSubsetInclusion X Z).hom.stalkMap
      ((closedSubsetRestriction f Z).hom.base z')) :=
    AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z) _
  have hi' : IsIso ((closedSubsetInclusion X' (closedSubsetPreimage f Z)).hom.stalkMap z') :=
    AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection X'
      (ClosedImmersionSheaves.closedSubsetInclusion (closedSubsetPreimage f Z)) _
  have hf : IsIso (f.hom.stalkMap
      ((closedSubsetInclusion X' (closedSubsetPreimage f Z)).hom.base z')) :=
    inferInstance
  exact isIso_stalkMap_of_comp (closedSubsetRestriction f Z).hom
    (closedSubsetInclusion X Z).hom z' hi
    (isIso_stalkMap_of_eq _ _ hsq z'
      (isIso_stalkMap_comp (closedSubsetInclusion X' (closedSubsetPreimage f Z)).hom f.hom z'
        hi' hf))

/-- **The restriction `f|_{Z'}` of an open immersion `f` to the preimage of a subset is an open
immersion.** The base map is an open embedding and the stalk maps are isomorphisms, so Mathlib's
stalk criterion applies. -/
instance isOpenImmersion_closedSubsetRestriction :
    SheafedSpace.IsOpenImmersion (closedSubsetRestriction f Z) := by
  have : ∀ z' : (closedSubsetRingedSpace X' (closedSubsetPreimage f Z)).carrier,
      IsIso ((closedSubsetRestriction f Z).hom.stalkMap z') :=
    isIso_stalkMap_closedSubsetRestriction f Z
  exact AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso _
    (isOpenEmbedding_closedSubsetRestriction_base f Z)

/-! ### The Cartesian square -/

/-- The image of the continuous map underlying `f|_{Z'}` is the part of `Z` lying in the image of
`f`. -/
theorem range_closedSubsetRestriction_base :
    Set.range ⇑(closedSubsetRestriction f Z).hom.base =
      (Subtype.val : Z → X.carrier) ⁻¹' Set.range ⇑f.hom.base := by
  rw [closedSubsetRestriction_base_eq]
  exact Set.range_restrictPreimage _ _

/-- A competitor to the square of the restriction maps into `Z` through the image of `f`, so it
can be lifted along `f|_{Z'}`. -/
private theorem range_pullbackCone_fst_le
    (s : PullbackCone (closedSubsetInclusion X Z) f) :
    Set.range ⇑s.fst.hom.base ⊆ Set.range ⇑(closedSubsetRestriction f Z).hom.base := by
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  rw [range_closedSubsetRestriction_base]
  refine ⟨s.snd.hom.base t, ?_⟩
  have h : ⇑(s.fst ≫ closedSubsetInclusion X Z).hom.base = ⇑(s.snd ≫ f).hom.base :=
    congrArg (fun m : s.pt ⟶ X => ⇑m.hom.base) s.condition
  exact (congrFun h t).symm

/-- The lift of a competitor to the square of the restriction, along the open immersion
`f|_{Z'}`. -/
private def pullbackConeLift (s : PullbackCone (closedSubsetInclusion X Z) f) :
    s.pt ⟶ closedSubsetRingedSpace X' (closedSubsetPreimage f Z) :=
  InducedCategory.homMk (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift
    (closedSubsetRestriction f Z).hom s.fst.hom (range_pullbackCone_fst_le f Z s))

private theorem pullbackConeLift_fst (s : PullbackCone (closedSubsetInclusion X Z) f) :
    pullbackConeLift f Z s ≫ closedSubsetRestriction f Z = s.fst := by
  apply AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace_faithful.map_injective
  exact AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac
    (closedSubsetRestriction f Z).hom s.fst.hom (range_pullbackCone_fst_le f Z s)

private theorem pullbackConeLift_snd (s : PullbackCone (closedSubsetInclusion X Z) f) :
    pullbackConeLift f Z s ≫ closedSubsetInclusion X' (closedSubsetPreimage f Z) = s.snd := by
  rw [← cancel_mono f, Category.assoc,
    ← closedSubsetRestriction_comp_closedSubsetInclusion f Z, ← Category.assoc,
    pullbackConeLift_fst, s.condition]

/-- **The square of the restriction is Cartesian in `RingedSpace` when `f` is an open
immersion.** The restriction `f|_{Z'}` is then an open immersion too, so a competitor lifts
through it uniquely; the second triangle follows because `f` is a monomorphism.

This is stated only for an open immersion: no fibre product of general ringed spaces is
constructed or claimed. -/
theorem isPullback_closedSubsetRestriction :
    IsPullback (closedSubsetRestriction f Z)
      (closedSubsetInclusion X' (closedSubsetPreimage f Z)) (closedSubsetInclusion X Z) f :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (closedSubsetRestriction_comp_closedSubsetInclusion f Z) (pullbackConeLift f Z)
    (pullbackConeLift_fst f Z) (pullbackConeLift_snd f Z) fun s m hm _ => by
      rw [← cancel_mono (closedSubsetRestriction f Z), hm, pullbackConeLift_fst])

/-! ### The base-change transformation of Tag 08HY for the square -/

omit H in
/-- **The base-change transformation of [Stacks, Tag 08HY] for the square of the restriction is
an isomorphism when `f` is an open immersion**, on every object of `D(𝒪_X|_Z)`.

This discharges the hypothesis `hbc` of
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMap` for an open immersion: the two
horizontal arrows of the square are open immersions and the square is Cartesian, which is exactly
what `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions` asks.
No quasi-compactness, quasi-separatedness or quasi-coherence hypothesis is used, and `Z` need not
be closed.

The hypotheses here are incomparable with those of
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackBaseChangeMap`, which proves the
same conclusion for an arbitrary morphism `f` of ringed spaces and a **closed** `Z`: neither
statement implies the other, and `_of_isOpenImmersion` names the hypothesis that replaces
`IsClosed Z` here.  The open-immersion hypothesis is written into this signature rather than
taken from the section, so that the two statements differ as written and not only in the
hypotheses they inherit. -/
theorem isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion
    [SheafedSpace.IsOpenImmersion f]
    (M : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    IsIso (supportedPullbackBaseChangeMap f Z M) :=
  Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions
    (closedSubsetRestriction f Z) (closedSubsetInclusion X' (closedSubsetPreimage f Z))
    (closedSubsetInclusion X Z) f (isPullback_closedSubsetRestriction f Z) M

end Stacks.Cohomology.SupportedComplexes

end
