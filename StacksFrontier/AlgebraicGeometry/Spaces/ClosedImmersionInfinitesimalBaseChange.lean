module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction

/-!
# Closed immersions of algebraic spaces checked after an infinitesimal base change, outright

Let `f : X → Y` and `i : Y' → Y` be morphisms of algebraic spaces over a scheme `S`, with `i` a
closed immersion inducing a bijection on points. If the base change `X ×_Y Y' → Y'` is a closed
immersion and either `f` is of finite type or `i` is of finite presentation, then `f` is a closed
immersion. This is Stacks 08B2, with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_isClosedImmersion_pullback_snd_of_bijective`:
  **Stacks 08B2**, the form of the tag registered in this library. The twin
  `AlgebraicGeometry.Space.isClosedImmersion_of_infinitesimal_baseChange`, which carries the three
  hypotheses of Stacks 07VT, is not tagged.

## Implementation notes

The proof is that of `AlgebraicGeometry.Space.isClosedImmersion_of_infinitesimal_baseChange`
(`StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionInfinitesimal`), with one change. Over an
object `a` of the site, the base change `X ×_Y a` receives the corresponding base change of
`X ×_Y Y'`, a scheme, by a closed immersion bijective on points; the source of 08B2 concludes
that `X ×_Y a` is a scheme by Stacks 07VU. Here that step is
`AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`
(`StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction`), the closed-immersion case of
Stacks 07VV, which rests on the thickening case of Stacks 07VT
(`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`)
and needs nothing else. Representability of `f` then reduces the tag to its scheme form,
Stacks 0896.

## References

* [Stacks Project, Tag 08B2](https://stacks.math.columbia.edu/tag/08B2)
* [Stacks Project, Tag 0896](https://stacks.math.columbia.edu/tag/0896)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site of `S` times out
/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ClosedImmersionInfinitesimalBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ClosedImmersionInfinitesimalBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change of `f` along `i`, base changed along `hi.rep.snd g`, is the base change of `f`
along `yoneda.map (hi.rep.snd g) ≫ g`. -/
private theorem isPullback_baseChange_comp
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {i : Y' ⟶ Y}
    (hi : IsClosedImmersion B S hS i) (hbc : IsClosedImmersion B S hS (pullback.snd f i))
    {a : BigFppfOver B S hS} (g : yoneda.obj a ⟶ Y) :
    IsPullback (hbc.rep.fst (hi.rep.fst g) ≫ pullback.fst f i)
      (yoneda.map (hbc.rep.snd (hi.rep.fst g))) f (yoneda.map (hi.rep.snd g) ≫ g) := by
  have h := IsPullback.paste_horiz (hbc.rep.isPullback (hi.rep.fst g))
    (IsPullback.of_hasPullback f i)
  rwa [(hi.rep.isPullback g).w] at h

/-- A base change of `f` to an object of the site is representable, when `i` is a closed
immersion surjective on points along which the base change of `f` is a closed immersion.

It receives the corresponding base change of `X ×_Y Y' → X` by a closed immersion which is
surjective on points, and that base change is representable because `X ×_Y Y' → Y'` and `Y' → Y`
are closed immersions, hence representable. The target of a closed immersion bijective on points
out of a scheme is a scheme. -/
theorem isRepresentable_pullback_of_isClosedImmersion_pullback_snd
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} {i : Y' ⟶ Y} (hi : IsClosedImmersion B S hS i)
    (hsurj : Function.Surjective (pointsMap B S hS Y' i))
    (hbc : IsClosedImmersion B S hS (pullback.snd f i))
    (a : BigFppfOver B S hS) (g : yoneda.obj a ⟶ Y) :
    (pullback f g).IsRepresentable := by
  have sqV := hi.rep.isPullback g
  have big := isPullback_baseChange_comp B S hS hi hbc g
  have sqc := IsPullback.of_right' big (IsPullback.of_hasPullback f g)
  have hpVci : IsClosedImmersion B S hS (yoneda.map (hi.rep.snd g)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (hi.rep.snd g)).2 (hi.property_snd g)
  have hpVsurj : Function.Surjective (pointsMap B S hS
      (yoneda.obj (hi.rep.pullback g)) (yoneda.map (hi.rep.snd g))) :=
    surjective_pointsMap_of_isPullback B S hS sqV hsurj
  have hcci := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqc.flip hpVci
  have hcsurj := surjective_pointsMap_of_isPullback B S hS sqc.flip hpVsurj
  have hPalg : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_of_isPullback hX (isAlgebraicSpace_yoneda B S hS a)
      hY.isSheaf hY.diagonal_representable (IsPullback.of_hasPullback f g)
  have _ := mono_of_isClosedImmersion B S hS _ hcci
  exact isRepresentable_of_isClosedImmersion_of_bijective B S hS
    (isAlgebraicSpace_of_relativelyRepresentable B S hS _ hcci.rep hPalg) hPalg _ hcci
    ⟨pointsMap_injective_of_mono B S hS _, hcsurj⟩ inferInstance

/-- **Stacks 08B2.** Let `f : X ⟶ Y` and `i : Y' ⟶ Y` be morphisms of algebraic spaces over `S`.
If `i` is a closed immersion, bijective on points, if the base change of `f` along `i` is a
closed immersion, and if either `f` is of finite type or `i` is of finite presentation, then `f`
is a closed immersion.

This is the registered form of Stacks 08B2. The 07VU step of the source's proof is
`AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`. -/
@[stacks 08B2 "the whole lemma, with hypotheses (1)-(4) as in the source: `hi` (1), `hbij` (2), \
`hbc` (3) and `hfin` (4); the 07VU step of the proof is the proved \
`isRepresentable_of_isClosedImmersion_of_bijective`"]
theorem isClosedImmersion_of_isClosedImmersion_pullback_snd_of_bijective
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (i : Y' ⟶ Y) (hi : IsClosedImmersion B S hS i)
    (hbij : Function.Bijective (pointsMap B S hS Y' i))
    (hbc : IsClosedImmersion B S hS (pullback.snd f i))
    (hfin : IsFiniteType B S hS f ∨ IsFinitePresentation B S hS i) :
    IsClosedImmersion B S hS f := by
  -- `f` is relatively representable.
  have hrep : yoneda.relativelyRepresentable f := by
    intro a g
    have := isRepresentable_pullback_of_isClosedImmersion_pullback_snd B S hS hX hY hi
      hbij.2 hbc a g
    refine ⟨(pullback f g).reprX,
      yoneda.preimage ((pullback f g).reprW.hom ≫ pullback.snd f g),
      (pullback f g).reprW.hom ≫ pullback.fst f g, ?_⟩
    rw [yoneda.map_preimage]
    have hiso : IsPullback (pullback f g).reprW.hom
        ((pullback f g).reprW.hom ≫ pullback.snd f g) (pullback.snd f g)
        (𝟙 (yoneda.obj a)) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa using IsPullback.paste_horiz hiso (IsPullback.of_hasPullback f g)
  have hY'alg : IsAlgebraicSpace B S hS Y' :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS i hi.rep hY
  -- The finiteness hypothesis on the represented base changes.
  have hfinSch : ∀ (a : BigFppfOver B S hS) (g : yoneda.obj a ⟶ Y),
      ((_root_.AlgebraicGeometry.LocallyOfFiniteType
          ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) ∧
        _root_.AlgebraicGeometry.QuasiCompact
          ((BigFppfOver.toScheme B S hS).map (hrep.snd g))) ∨
       _root_.AlgebraicGeometry.FinitePresentation
          ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g))) := by
    intro a g
    rcases hfin with hft | hfp
    · have hft' := (holdsOnEveryEtaleChart_iff_relative B S hS
        (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u})
        _root_.AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
        hX hY f hrep).mp hft.1
      have hqc' := presheaf_quasiCompact_of_isQuasiCompact B S hS hrep hft.2
      exact Or.inl ⟨hft'.property g _ _ (hrep.isPullback g),
        hqc'.property g _ _ (hrep.isPullback g)⟩
    · have _ : MorphismProperty.IsLocalAtTarget
          (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
            MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
        Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fpqc.{u}
      have _ : MorphismProperty.IsLocalAtTarget
          (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
            MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
        MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
      have hfp' := (holdsOnEveryEtaleChart_iff_relative B S hS
        (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
        _root_.AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
        hY'alg hY i hi.rep).mp hfp.1
      have _ : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) := hi.property_snd g
      exact Or.inr ⟨hfp'.property g _ _ (hi.rep.isPullback g), inferInstance, inferInstance⟩
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    (BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _).respectsIso
  refine MorphismProperty.relative_of_snd hrep fun a g => ?_
  -- Stacks 0896 applied to the represented base changes.
  have key : ∀ (W : BigFppfOver B S hS) (ρ : W ⟶ hi.rep.pullback g)
      (c : yoneda.obj W ⟶ yoneda.obj (hrep.pullback g)),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ρ) →
      IsPullback c (yoneda.map ρ) (yoneda.map (hrep.snd g))
        (yoneda.map (hi.rep.snd g)) →
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) := by
    intro W ρ c hρ hsq
    obtain ⟨τ, rfl⟩ := yoneda.map_surjective c
    have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
    have _ : PreservesLimit (cospan (hrep.snd g) (hi.rep.snd g)) (BigFppfOver.toScheme B S hS) :=
      PreservesLimitsOfShape.preservesLimit
    have hschm := (IsPullback.of_map_of_faithful yoneda hsq).map
      (BigFppfOver.toScheme B S hS)
    have hg'ci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) := hi.property_snd g
    have hpVsurj : Function.Surjective (pointsMap B S hS
        (yoneda.obj (hi.rep.pullback g)) (yoneda.map (hi.rep.snd g))) :=
      surjective_pointsMap_of_isPullback B S hS (hi.rep.isPullback g) hbij.2
    have hsurjSch : _root_.AlgebraicGeometry.Surjective
        ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.Surjective.{u}) (hi.rep.snd g)).1
        ((surjective_yonedaMap_iff_surjective_pointsMap B S hS (hi.rep.snd g)).2 hpVsurj)
    have hbijSch : Function.Bijective
        ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)).base :=
      ⟨((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)).isClosedEmbedding.injective,
        hsurjSch.surj⟩
    have hpbci : _root_.AlgebraicGeometry.IsClosedImmersion
        (pullback.snd ((BigFppfOver.toScheme B S hS).map (hrep.snd g))
          ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g))) := by
      have heq : pullback.snd ((BigFppfOver.toScheme B S hS).map (hrep.snd g))
          ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) =
          hschm.isoPullback.inv ≫ (BigFppfOver.toScheme B S hS).map ρ :=
        (Iso.eq_inv_comp _).2 hschm.isoPullback_hom_snd
      rw [heq]
      exact MorphismProperty.RespectsIso.precomp
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _ hρ
    exact _root_.AlgebraicGeometry.isClosedImmersion_of_infinitesimal_baseChange _ _ hbijSch
      (hfinSch a g)
  exact key _ (hbc.rep.snd (hi.rep.fst g)) _ (hbc.property_snd (hi.rep.fst g))
    (IsPullback.of_right' (isPullback_baseChange_comp B S hS hi hbc g) (hrep.isPullback g))

end AlgebraicGeometry.Space

end
