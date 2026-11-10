module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubspaceSymmetry
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# The restriction of a smooth groupoid to an invariant subspace is smooth

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of Stacks 043W, and let `Z` be an invariant subspace of its space of
objects in the sense of Stacks 044F. The restriction `G.restrict` of `G` along the inclusion of
`Z` (Stacks 044B) has as its two structure maps the two projections of the space of restricted
arrows to `Z`. This file shows that both are smooth as soon as the source and the target map of
`G` are, so that the restricted groupoid is smooth in the sense of Stacks 04TH.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.subspaceInclusion`: a subspace of the object space,
  as an algebraic space over `S` mapping to the object space.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_fiberProductSnd_restrictionArrows`: for an
  invariant subspace, the space of restricted arrows is the inverse image of `Z` under the source
  map, through the projection that `restrictionSource` factors through.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_fiberProductFst_restrictionArrows`: and
  likewise the inverse image of `Z` under the target map.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.prop_restrictionSource_of_invariant` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.prop_restrictionTarget_of_invariant`: for an
  arbitrary property of morphisms of algebraic spaces over `S` stable under base change.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSmooth_restrictionSource` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSmooth_restrictionTarget`: the two structure maps
  of the restriction are smooth.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSmooth_restriction`: any groupoid satisfying the
  specification of the restriction of a smooth groupoid along an invariant subspace is smooth.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSmoothGroupoid_restrict_invariant` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSmoothGroupoid_restrict_invariantOpen`: the
  restriction of a smooth groupoid along an invariant locally closed, respectively open, subspace
  of its object space is a smooth groupoid.

## Implementation notes

The space of restricted arrows `restrictionArrows G Z.ι` is the fibre product over the arrow space
of `t⁻¹(Z)` with `s⁻¹(Z)`, each of those being the chosen fibre product of the inclusion of `Z`
with the relevant structure map. The identification `R_Z = s⁻¹(Z) = t⁻¹(Z)` is realized not as an
equality of subspaces but as invertibility of the two projections out of that fibre product.

Both inclusions `s⁻¹(Z) ≤ t⁻¹(Z)` and `t⁻¹(Z) ≤ s⁻¹(Z)` are needed, so the hypothesis is stated as
the equality of the two inverse images. That is part (2) of Stacks 044F, and for part (1), whose
condition is one-sided, it follows from
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.preimage_source_eq_preimage_target`.

## References

* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04YN](https://stacks.math.columbia.edu/tag/04YN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}
  (G : GroupoidInAlgebraicSpaces C S hS B) (Z : Subfunctor G.objects.obj)
  (hZ : IsAlgebraicSpace C S hS Z.toFunctor)

/-- A subspace of the object space of a groupoid in algebraic spaces, as an algebraic space over
`S` mapping to the object space: the morphism along which the groupoid is restricted. -/
noncomputable abbrev subspaceInclusion :
    (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces C S hS) ⟶ G.objects :=
  ObjectProperty.homMk Z.ι

/-- The inclusion of a subspace of the object space is a monomorphism of algebraic spaces, the
forgetful functor to presheaves being faithful. -/
theorem mono_subspaceInclusion : Mono (subspaceInclusion G Z hZ) := by
  refine Functor.ReflectsMonomorphisms.reflects (F := ObjectProperty.ι _) _ ?_
  exact (inferInstance : Mono Z.ι)

/-- An arrow whose source is lifted to `Z` has its target in `Z`, when `Z` is invariant. -/
private lemma range_target_comp_le_of_preimage_le
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    Subfunctor.range
      ((fiberProductFst G.source (subspaceInclusion G Z hZ) ≫ G.target).hom) ≤ Z := by
  intro T y hy
  obtain ⟨x, rfl⟩ := hy
  refine hinv T (show (fiberProductFst G.source (subspaceInclusion G Z hZ)).hom.app T x
      ∈ (Z.preimage G.source.hom).obj T from ?_)
  have hcond :
      G.source.hom.app T ((fiberProductFst G.source (subspaceInclusion G Z hZ)).hom.app T x)
        = ((fiberProductSnd G.source (subspaceInclusion G Z hZ)).hom.app T x :
            G.objects.obj.obj T) :=
    congrArg (fun k => k.hom.app T x)
      (fiberProduct_condition G.source (subspaceInclusion G Z hZ))
  change G.source.hom.app T ((fiberProductFst G.source (subspaceInclusion G Z hZ)).hom.app T x)
    ∈ Z.obj T
  rw [hcond]
  exact Subtype.property _

/-- An arrow whose target is lifted to `Z` has its source in `Z`, when `Z` is invariant. -/
private lemma range_source_comp_le_of_preimage_le
    (hinv : Z.preimage G.target.hom ≤ Z.preimage G.source.hom) :
    Subfunctor.range
      ((fiberProductSnd (subspaceInclusion G Z hZ) G.target ≫ G.source).hom) ≤ Z := by
  intro T y hy
  obtain ⟨x, rfl⟩ := hy
  refine hinv T (show (fiberProductSnd (subspaceInclusion G Z hZ) G.target).hom.app T x
      ∈ (Z.preimage G.target.hom).obj T from ?_)
  have hcond :
      ((fiberProductFst (subspaceInclusion G Z hZ) G.target).hom.app T x : G.objects.obj.obj T)
        = G.target.hom.app T
            ((fiberProductSnd (subspaceInclusion G Z hZ) G.target).hom.app T x) :=
    congrArg (fun k => k.hom.app T x)
      (fiberProduct_condition (subspaceInclusion G Z hZ) G.target)
  change G.target.hom.app T ((fiberProductSnd (subspaceInclusion G Z hZ) G.target).hom.app T x)
    ∈ Z.obj T
  rw [← hcond]
  exact Subtype.property _

/-- In a pullback square along a monomorphism `g`, the first projection is an isomorphism as soon
as the other map `f` factors through `g`. -/
private theorem isIso_fst_of_isPullback_of_factors {D : Type*} [Category D] {P X Y W : D}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ W} {g : Y ⟶ W} (h : IsPullback fst snd f g) [Mono g]
    (k : X ⟶ Y) (hk : k ≫ g = f) : IsIso fst :=
  have := h.mono_fst_of_mono
  have : IsSplitEpi fst := IsSplitEpi.mk' ⟨h.lift (𝟙 _) k (by simpa using hk.symm), by simp⟩
  isIso_of_mono_of_isSplitEpi _

/-- For an invariant subspace `Z` of the object space, the projection of the space of restricted
arrows onto the inverse image of `Z` under the source map is an isomorphism: it is the base change
of the monomorphism `t⁻¹(Z) ⟶ R`, and the invariance condition `s⁻¹(Z) ≤ t⁻¹(Z)` provides a
section of it. This is the identification `R_Z = s⁻¹(Z)`. -/
theorem isIso_fiberProductSnd_restrictionArrows
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    IsIso (fiberProductSnd (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ))) := by
  have := mono_subspaceInclusion G Z hZ
  have hA := (AlgebraicSpaces.isPullback_fiberProduct C S hS (subspaceInclusion G Z hZ)
    G.target).mono_snd_of_mono
  exact isIso_fst_of_isPullback_of_factors
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ))).flip _
    ((AlgebraicSpaces.isPullback_fiberProduct C S hS
        (subspaceInclusion G Z hZ) G.target).lift_snd
      (ObjectProperty.homMk
        (Subfunctor.lift _ (range_target_comp_le_of_preimage_le G Z hZ hinv)))
      (fiberProductFst G.source (subspaceInclusion G Z hZ))
      (ObjectProperty.hom_ext _
        (Subfunctor.lift_ι _ (range_target_comp_le_of_preimage_le G Z hZ hinv))))

/-- For an invariant subspace `Z` of the object space, the projection of the space of restricted
arrows onto the inverse image of `Z` under the target map is an isomorphism: it is the base change
of the monomorphism `s⁻¹(Z) ⟶ R`, and the invariance condition `t⁻¹(Z) ≤ s⁻¹(Z)` provides a
section of it. This is the identification `R_Z = t⁻¹(Z)`. -/
theorem isIso_fiberProductFst_restrictionArrows
    (hinv : Z.preimage G.target.hom ≤ Z.preimage G.source.hom) :
    IsIso (fiberProductFst (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ))) := by
  have := mono_subspaceInclusion G Z hZ
  have hB := (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source
    (subspaceInclusion G Z hZ)).mono_fst_of_mono
  exact isIso_fst_of_isPullback_of_factors
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ))) _
    ((AlgebraicSpaces.isPullback_fiberProduct C S hS G.source
        (subspaceInclusion G Z hZ)).lift_fst
      (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (ObjectProperty.homMk
        (Subfunctor.lift _ (range_source_comp_le_of_preimage_le G Z hZ hinv)))
      (ObjectProperty.hom_ext _
        (Subfunctor.lift_ι _ (range_source_comp_le_of_preimage_le G Z hZ hinv)).symm))

/-- The source map of the restriction of a groupoid in algebraic spaces along an **invariant**
subspace of its object space has any property of morphisms of algebraic spaces over `S` which is
stable under base change, as soon as the source map of the groupoid has it. -/
theorem prop_restrictionSource_of_invariant
    (P : MorphismProperty (AlgebraicSpaces C S hS)) (hbc : P.IsStableUnderBaseChange)
    (hs : P G.source) (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    P (restrictionSource G (subspaceInclusion G Z hZ)) := by
  have : P.IsStableUnderBaseChange := hbc
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := isIso_fiberProductSnd_restrictionArrows G Z hZ hinv
  exact MorphismProperty.RespectsIso.precomp P
    (fiberProductSnd (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ)))
    (fiberProductSnd G.source (subspaceInclusion G Z hZ))
    (hbc.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source
      (subspaceInclusion G Z hZ)) hs)

/-- The target map of the restriction of a groupoid in algebraic spaces along an **invariant**
subspace of its object space has any property of morphisms of algebraic spaces over `S` which is
stable under base change, as soon as the target map of the groupoid has it. -/
theorem prop_restrictionTarget_of_invariant
    (P : MorphismProperty (AlgebraicSpaces C S hS)) (hbc : P.IsStableUnderBaseChange)
    (ht : P G.target) (hinv : Z.preimage G.target.hom ≤ Z.preimage G.source.hom) :
    P (restrictionTarget G (subspaceInclusion G Z hZ)) := by
  have : P.IsStableUnderBaseChange := hbc
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := isIso_fiberProductFst_restrictionArrows G Z hZ hinv
  exact MorphismProperty.RespectsIso.precomp P
    (fiberProductFst (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ)))
    (fiberProductFst (subspaceInclusion G Z hZ) G.target)
    (hbc.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (subspaceInclusion G Z hZ) G.target).flip ht)

/-- The source map of the restriction of a groupoid in algebraic spaces with smooth source map
along an invariant subspace of its object space is smooth. -/
theorem isSmooth_restrictionSource (hs : Space.IsSmooth C S hS G.source.hom)
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    Space.IsSmooth C S hS (restrictionSource G (subspaceInclusion G Z hZ)).hom :=
  prop_restrictionSource_of_invariant G Z hZ (Space.smoothMorphismProperty C S hS)
    (Space.instIsStableUnderBaseChangeSmoothMorphismProperty C S hS) hs hinv

/-- The target map of the restriction of a groupoid in algebraic spaces with smooth target map
along an invariant subspace of its object space is smooth. -/
theorem isSmooth_restrictionTarget (ht : Space.IsSmooth C S hS G.target.hom)
    (hinv : Z.preimage G.target.hom ≤ Z.preimage G.source.hom) :
    Space.IsSmooth C S hS (restrictionTarget G (subspaceInclusion G Z hZ)).hom :=
  prop_restrictionTarget_of_invariant G Z hZ (Space.smoothMorphismProperty C S hS)
    (Space.instIsStableUnderBaseChangeSmoothMorphismProperty C S hS) ht hinv

/-- Any groupoid in algebraic spaces satisfying the specification of the restriction of a smooth
groupoid along an invariant subspace of its object space is itself smooth, in the sense of
Stacks 04TH. -/
theorem isSmooth_restriction (hG : IsSmooth C S hS G)
    (heq : Z.preimage G.source.hom = Z.preimage G.target.hom)
    (R : Restriction G (subspaceInclusion G Z hZ)) : IsSmooth C S hS R.groupoid := by
  have : (Space.smoothMorphismProperty C S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨?_, ?_⟩
  · rw [R.source_eq]
    exact MorphismProperty.RespectsIso.precomp (Space.smoothMorphismProperty C S hS) _ _
      (MorphismProperty.RespectsIso.postcomp (Space.smoothMorphismProperty C S hS) _ _
        (isSmooth_restrictionSource G Z hZ hG.1 heq.le))
  · rw [R.target_eq]
    exact MorphismProperty.RespectsIso.precomp (Space.smoothMorphismProperty C S hS) _ _
      (MorphismProperty.RespectsIso.postcomp (Space.smoothMorphismProperty C S hS) _ _
        (isSmooth_restrictionTarget G Z hZ hG.2 heq.ge))

variable {Z}

/-- The restriction (Stacks 044B) of a smooth groupoid in algebraic spaces (Stacks 04TH) along an
invariant locally closed subspace of its object space (Stacks 044F, part (2)) is again a smooth
groupoid in algebraic spaces. -/
theorem isSmoothGroupoid_restrict_invariant (hG : IsSmooth C S hS G)
    (hZ : IsInvariantLocallyClosed G Z) :
    IsSmooth C S hS (G.restrict (subspaceInclusion G Z hZ.1.1)).groupoid :=
  isSmooth_restriction G Z hZ.1.1 hG hZ.2.symm _

/-- The restriction (Stacks 044B) of a smooth groupoid in algebraic spaces (Stacks 04TH) along an
invariant open subspace of its object space (Stacks 044F, part (1)) is again a smooth groupoid in
algebraic spaces. -/
theorem isSmoothGroupoid_restrict_invariantOpen (hG : IsSmooth C S hS G)
    (hZ : IsInvariantOpen G Z) :
    IsSmooth C S hS (G.restrict (subspaceInclusion G Z hZ.1.1)).groupoid :=
  isSmooth_restriction G Z hZ.1.1 hG (preimage_source_eq_preimage_target G Z hZ.2) _

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
