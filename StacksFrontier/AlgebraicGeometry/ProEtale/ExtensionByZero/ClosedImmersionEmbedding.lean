module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageAffineReduction
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# A closed immersion is an embedding of small pro-étale topoi

Let `i : Z ⟶ X` be a closed immersion of objects of a chosen big pro-étale site. Then the
inverse image `i⁻¹` on small pro-étale sheaves of sets commutes with limits, the direct image
`i_*` is fully faithful, and the counit `i⁻¹ i_* ⟶ id` is an isomorphism. These are the three
assertions of [Stacks, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA), with no hypothesis
beyond `i` being a closed immersion.

The source's proof is followed. All three assertions are Zariski local on `X`, so one reduces to
the case of affine `X`, where they are
[Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL). The affine objects of the small
pro-étale site of `X` cover its final object, their base changes along `i` cover the final object
of the small pro-étale site of `Z`, and over an affine object `Y` the base change
`pullback.fst Y.obj.hom i` of `i` is again a closed immersion of affine objects. For the counit and
for full faithfulness the reduction is
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_affineCounit`; for limits it is
carried out below, because preservation of limits is not an invertibility statement about a natural
transformation and therefore falls outside that hub.

The reduction for limits runs as follows. Limits of sheaves of sets on the small pro-étale site
of `Z` exist, so the assertion is that the canonical map from `i⁻¹(lim F)` to `lim (i⁻¹F)` is
invertible, and invertibility of a morphism of sheaves is detected by the sections over the
objects lying over a member of a family covering the final object
(`AlgebraicGeometry.ProEtale.isIso_of_bijective_of_coversTop`). Restriction to such a member is
restriction to a localization of the site, which is a right adjoint and so commutes with limits,
and across the base-change square it exchanges with `i⁻¹` by the Beck–Chevalley isomorphism
`AlgebraicGeometry.ProEtale.isIso_smallProetaleBaseChangeCounitMate`. So the restriction of the
canonical map is the canonical map for the base-changed closed immersion of affine objects, where
`i⁻¹` has the left adjoint of Stacks 09BL (3) and therefore commutes with limits.

## Main results

* `CategoryTheory.Limits.isIso_map_lift_mapCone`: a functor `G` out of the target which commutes
  with limits of shape `J` and whose composite with `F` commutes with them too carries the
  canonical comparison map for `F` to an isomorphism.
* `AlgebraicGeometry.ProEtale.preservesLimits_smallProetaleRestrict`: restriction of small
  pro-étale sheaves of sets to a localization commutes with limits.
* `smallProetaleMorphism_inverseImage_preservesLimits_of_isClosedImmersion`: **Stacks 09AA (1)**,
  for a closed immersion `i` the inverse image `i⁻¹` on pro-étale sheaves of sets commutes with
  limits.
* `smallProetaleMorphism_pushforward_fullyFaithful_of_isClosedImmersion`: **Stacks 09AA (2)**,
  for a closed immersion `i` the direct image `i_*` on pro-étale sheaves of sets is fully faithful.
* `smallProetaleMorphism_counit_isIso_of_isClosedImmersion`: **Stacks 09AA (3)**, for a closed
  immersion `i` the counit `i⁻¹ i_* ⟶ id` is an isomorphism.

## Implementation notes

Assertions (2) and (3) are equivalent for any adjunction, by Sites 04D6, and that equivalence is
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_iff_pushforward_fullyFaithful`;
neither is therefore *derived* from the other here. Both come from the single affine input
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_isAffine`, assertion (2) being
read off (3) by the adjunction only after (3) has been proved from that input.

Assertion (1) is a genuinely different statement, and is not a formal consequence of (2) or (3):
a left adjoint with fully faithful right adjoint need not preserve limits. Its affine input is
the left adjoint `i^{Sh}_!` of Stacks 09BL (3),
`AlgebraicGeometry.ProEtale.isRightAdjoint_smallProetaleMorphism_inverseImage`.

The statements are for a closed immersion of objects of a chosen big pro-étale site, which is the
setting in which Stacks 09BL is available; the unrestricted small pro-étale site
`AlgebraicGeometry.Scheme.ProEt` of all weakly étale schemes over the base is a different site,
and the comparison of the two is not in the library — see the module docstring of
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.BaseChange`. Coefficients are sheaves of
sets, as in the source.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 04D6](https://stacks.math.columbia.edu/tag/04D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory.Limits

/-- **A limit-preserving functor out of the target detects the comparison map.** Let `F : A ⥤ D`,
let `K : J ⥤ A` have a limit after `F`, and let `c` be a limit cone over `K`. If `G : D ⥤ E`
commutes with limits of shape `J` and so does `F ⋙ G`, then `G` carries the canonical comparison
map from `F` applied to the limit to the limit of `F` applied to the diagram to an isomorphism.

Both `G` applied to the limit cone of `K ⋙ F` and `G` applied to `F.mapCone c` are limit cones
over the same diagram, the first because `G` commutes with limits of shape `J` and the second
because `F ⋙ G` does, and the image of the comparison map is a morphism of cones between them. -/
theorem isIso_map_lift_mapCone {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {J : Type w} [Category.{w'} J]
    (F : A ⥤ D) (G : D ⥤ E) {K : J ⥤ A} [HasLimit (K ⋙ F)] {c : Cone K} (hc : IsLimit c)
    [PreservesLimitsOfShape J G] [PreservesLimitsOfShape J (F ⋙ G)] :
    IsIso (G.map ((limit.isLimit (K ⋙ F)).lift (F.mapCone c))) := by
  have h1 : IsLimit (G.mapCone (limit.cone (K ⋙ F))) :=
    isLimitOfPreserves G (limit.isLimit (K ⋙ F))
  have h2 : IsLimit (G.mapCone (F.mapCone c)) := isLimitOfPreserves (F ⋙ G) hc
  have key : G.map ((limit.isLimit (K ⋙ F)).lift (F.mapCone c)) =
      (IsLimit.conePointUniqueUpToIso h2 h1).hom := by
    refine h1.hom_ext fun j => ?_
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    show G.map ((limit.isLimit (K ⋙ F)).lift (F.mapCone c)) ≫
      G.map ((limit.cone (K ⋙ F)).π.app j) = _
    rw [← Functor.map_comp, (limit.isLimit (K ⋙ F)).fac]
    rfl
  rw [key]
  infer_instance

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

/-- **Restriction to a localization commutes with limits.** Restriction of small pro-étale
sheaves of sets along composition with a weakly étale morphism `j` is a right adjoint, being the
direct image along the continuous functor "compose with `j`", and therefore commutes with limits.

It is also a left adjoint, by
`AlgebraicGeometry.ProEtale.smallProetaleRestrict_adj`; that is a different statement and gives
colimits, not limits. -/
theorem preservesLimits_smallProetaleRestrict {W T : B.Scheme} (j : W ⟶ T)
    (hj : WeaklyEtale (B.inclusion.map j)) :
    PreservesLimits (smallProetaleRestrict B j hj) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallProetaleCompose B j hj)
    (Type (u + 1)) (SmallProetale.topology B W.obj W.property)
    (SmallProetale.topology B T.obj T.property)).rightAdjoint_preservesLimits

variable {Z X : B.Scheme} (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]

/-- The base change of a closed immersion of a chosen big pro-étale site along an arbitrary
morphism is a closed immersion: the fibre product of the big site is the fibre product of
schemes, and closed immersions are stable under base change. -/
theorem isClosedImmersion_inclusion_map_pullback_fst {W : B.Scheme} (a : W ⟶ X) :
    IsClosedImmersion (B.inclusion.map (pullback.fst a i)) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    ((IsPullback.of_hasPullback a i).flip.map B.inclusion) ‹_›

/-- The base change of a closed immersion of a chosen big pro-étale site along a morphism with
affine source has affine source: it is a closed immersion, hence an affine morphism, into an
affine scheme. -/
theorem isAffine_pullback_obj_of_isClosedImmersion {W : B.Scheme} (a : W ⟶ X) [IsAffine W.obj] :
    IsAffine (pullback a i).obj := by
  have := isClosedImmersion_inclusion_map_pullback_fst B i a
  have : IsAffine (B.inclusion.obj W) := ‹IsAffine W.obj›
  exact isAffine_of_isAffineHom (f := B.inclusion.map (pullback.fst a i))

/-- The base change of a closed immersion along a morphism with affine source is a closed
immersion of affine objects. -/
private theorem isClosedImmersion_and_isAffine_pullback {W : B.Scheme} (a : W ⟶ X)
    [IsAffine W.obj] :
    IsClosedImmersion (B.inclusion.map (pullback.fst a i)) ∧ IsAffine (pullback a i).obj :=
  ⟨isClosedImmersion_inclusion_map_pullback_fst B i a,
    isAffine_pullback_obj_of_isClosedImmersion B i a⟩

omit [IsClosedImmersion (B.inclusion.map i)] in
/-- **Stacks 09AA (3).** For a closed immersion `i : Z ⟶ X` of objects of a chosen big pro-étale
site, the counit `i⁻¹ i_* ⟶ id` of the direct-image adjunction on small pro-étale sheaves of sets
is an isomorphism.

The assertion is Zariski local on `X` by
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_affineCounit`, which reduces it
to the affine objects of the small pro-étale site of `X`; over such an object the base change of
`i` is a closed immersion of affine objects, where the assertion is Stacks 09BL. -/
@[stacks 09AA "(3), the counit i^{-1} i_* -> id of the morphism of topoi of a closed immersion \
of objects of a chosen big pro-etale site is an isomorphism"]
theorem smallProetaleMorphism_counit_isIso_of_isClosedImmersion
    [IsClosedImmersion (B.inclusion.map i)] :
    IsIso (smallProetaleMorphism B Z X i).adj.counit := by
  refine smallProetaleMorphism_counit_isIso_of_affineCounit B Z X i fun Y hY => ?_
  have : IsAffine (Y.obj.left).obj := hY
  obtain ⟨_, _⟩ := isClosedImmersion_and_isAffine_pullback B i Y.obj.hom
  exact smallProetaleMorphism_counit_isIso_of_isAffine B (pullback.fst Y.obj.hom i)

/-- **Stacks 09AA (2).** For a closed immersion `i : Z ⟶ X` of objects of a chosen big pro-étale
site, the direct image `i_*` on small pro-étale sheaves of sets is fully faithful.

This is assertion (3) together with the equivalence of Sites 04D6: the right adjoint of an
adjunction whose counit is invertible is fully faithful. -/
@[stacks 09AA "(2), the direct image i_* of the morphism of topoi of a closed immersion of \
objects of a chosen big pro-etale site is fully faithful"]
def smallProetaleMorphism_pushforward_fullyFaithful_of_isClosedImmersion :
    (smallProetaleMorphism B Z X i).pushforward.FullyFaithful := by
  haveI := smallProetaleMorphism_counit_isIso_of_isClosedImmersion B i
  exact (smallProetaleMorphism B Z X i).adj.fullyFaithfulROfIsIsoCounit

/-- **Stacks 09AA (1).** For a closed immersion `i : Z ⟶ X` of objects of a chosen big pro-étale
site, the inverse image `i⁻¹` on small pro-étale sheaves of sets commutes with limits.

The base changes along `i` of the affine objects of the small pro-étale site of `X` cover the
final object of the small pro-étale site of `Z`, so the canonical comparison map from `i⁻¹` of a
limit to the limit of `i⁻¹` is invertible as soon as it is bijective on the sections over the
objects lying over one of them, and that is invertibility of its restriction to such a member.
Restriction commutes with limits, being a right adjoint, and exchanges with `i⁻¹` across the
base-change square by Beck–Chevalley, so the restricted comparison map is the comparison map for
the base-changed closed immersion of affine objects, whose inverse image commutes with limits by
Stacks 09BL (3). -/
@[stacks 09AA "(1), the inverse image i^{-1} of the morphism of topoi of a closed immersion of \
objects of a chosen big pro-etale site commutes with limits"]
theorem smallProetaleMorphism_inverseImage_preservesLimits_of_isClosedImmersion :
    PreservesLimits (smallProetaleMorphism B Z X i).inverseImage := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  intro c hc
  have hU := coversTop_smallProetaleBaseChange B Z X i (SmallProetale.coversTop_affine B X)
  have : IsIso ((limit.isLimit (K ⋙ (smallProetaleMorphism B Z X i).inverseImage)).lift
      ((smallProetaleMorphism B Z X i).inverseImage.mapCone c)) := by
    refine isIso_of_bijective_of_coversTop hU _ fun Y W q => ?_
    refine bijective_app_of_isIso_smallProetaleRestrict B Z
      ((smallProetaleBaseChange B Z X i).obj Y.1) _ ?_ q
    have : IsAffine (Y.1.obj.left).obj := Y.2
    obtain ⟨_, _⟩ := isClosedImmersion_and_isAffine_pullback B i Y.1.obj.hom
    have := preservesLimits_smallProetaleRestrict B Y.1.obj.hom Y.1.property
    have := preservesLimits_smallProetaleRestrict B
      ((smallProetaleBaseChange B Z X i).obj Y.1).obj.hom
      ((smallProetaleBaseChange B Z X i).obj Y.1).property
    let m := smallProetaleBaseChangeCounitMate B
      ((smallProetaleBaseChange B Z X i).obj Y.1).obj.hom (pullback.fst Y.1.obj.hom i) i
      Y.1.obj.hom Y.1.property ((smallProetaleBaseChange B Z X i).obj Y.1).property
      (isPullback_smallProetaleBaseChange B Z X i Y.1)
    have : IsIso m := isIso_smallProetaleBaseChangeCounitMate B _ _ _ _ _ _
      (isPullback_smallProetaleBaseChange B Z X i Y.1)
    have : (smallProetaleMorphism B ((smallProetaleBaseChange B Z X i).obj Y.1).obj.left
        Y.1.obj.left (pullback.fst Y.1.obj.hom i)).inverseImage.IsRightAdjoint :=
      isRightAdjoint_smallProetaleMorphism_inverseImage B (pullback.fst Y.1.obj.hom i)
    have := preservesLimitsOfShape_of_natIso (J := J) (asIso m)
    exact isIso_map_lift_mapCone _ _ hc
  exact ⟨IsLimit.ofPointIso
    (limit.isLimit (K ⋙ (smallProetaleMorphism B Z X i).inverseImage))⟩

end AlgebraicGeometry.ProEtale

end
