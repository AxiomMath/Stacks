module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.ClosedImmersionInfinitesimal
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Closed immersions of algebraic spaces checked after an infinitesimal base change

Let `f : X → Y` and `i : Y' → Y` be morphisms of algebraic spaces over a scheme `S`, with `i` a
closed immersion inducing a bijection on points. If the base change `X ×_Y Y' → Y'` is a closed
immersion and either `f` is of finite type or `i` is of finite presentation, then `f` is a closed
immersion.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_infinitesimal_baseChange`: **Stacks 08B2**.

## Implementation notes

The base changes of `f` along the morphisms out of the objects of the site are representable:
such a base change receives a closed immersion, surjective on points, from the corresponding base
change of `X ×_Y Y'`, which is representable because `X ×_Y Y' → Y'` and `Y' → Y` are.
Representability of `f` reduces the tag to its scheme form, Stacks 0896.

A closed immersion surjective on points is integral by Stacks 081Y and injective on points,
being a monomorphism, so it is an integral bijection and the implication from the source of
Stacks 07VV turns a scheme source into a scheme target. The three hypotheses `h09YA`, `h07SQ`
and `hFinitePresentation` of that implication are exactly those of Stacks 07VT, on which
Stacks 07VU and Stacks 07VV are conditional in this library, and they are carried unchanged.
None is the universally quantified form of this conclusion, which is about closed immersions:
the first two conclude about inverse systems and the third about affineness of a target.

Over an object of the site, finite type of `f` and finite presentation of `i` are read on the
represented base changes through Stacks 03MJ and Stacks 03HD; the quasi-compact and
quasi-separated clauses of finite presentation are automatic there, a closed immersion of schemes
being affine and separated.

## References

* [Stacks Project, Tag 08B2](https://stacks.math.columbia.edu/tag/08B2)
* [Stacks Project, Tag 0896](https://stacks.math.columbia.edu/tag/0896)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site times out at the default
/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ClosedImmersionInfinitesimal :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ClosedImmersionInfinitesimal
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Representability of the base changes -/

/-- A presheaf on the big fppf site of `S` which receives a closed immersion from a scheme,
surjective on points, is a scheme.

A closed immersion is integral by Stacks 081Y and is a monomorphism, hence injective on points,
so a surjective one is an integral bijection and the implication from the source of Stacks 07VV
applies. -/
private theorem isRepresentable_of_isClosedImmersion_of_surjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (c : F ⟶ G) (hc : IsClosedImmersion B S hS c)
    (hcsurj : Function.Surjective (pointsMap B S hS F c)) (hF : F.IsRepresentable)
    (h09YA : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Z'),
      IsAlgebraicSpace B S hS Z → IsAlgebraicSpace B S hS Z' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Z' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Z'),
      IsAlgebraicSpace B S hS Z → IsAlgebraicSpace B S hS Z' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS Z →
      IsAffineSpace B S hS Z') :
    G.IsRepresentable := by
  have hmono : Mono c := mono_of_isClosedImmersion B S hS c hc
  exact isRepresentable_of_isIntegralHom_of_bijective B S hS
    (isAlgebraicSpace_of_relativelyRepresentable B S hS c hc.rep hG) hG c
    (isIntegralHom_of_isClosedImmersion B S hS c hc)
    ⟨pointsMap_injective_of_mono B S hS c, hcsurj⟩ hF h09YA h07SQ hFinitePresentation

/-- Pasting the base change of `f` along `i` with that of `i` along `g` gives a pullback square
over `f`. -/
private theorem isPullback_baseChange_paste
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {i : Y' ⟶ Y} {a : BigFppfOver B S hS}
    (hi : IsClosedImmersion B S hS i) (hbc : IsClosedImmersion B S hS (pullback.snd f i))
    (g : yoneda.obj a ⟶ Y) :
    IsPullback (hbc.rep.fst (hi.rep.fst g) ≫ pullback.fst f i)
      (yoneda.map (hbc.rep.snd (hi.rep.fst g))) f (yoneda.map (hi.rep.snd g) ≫ g) := by
  have h := IsPullback.paste_horiz (hbc.rep.isPullback (hi.rep.fst g))
    (IsPullback.of_hasPullback f i)
  rwa [(hi.rep.isPullback g).w] at h

/-- A base change of `f` to an object of the site is representable.

It receives the corresponding base change of `X ×_Y Y' → X` by a closed immersion which is
surjective on points, and that base change is representable because `X ×_Y Y' → Y'` and `Y' → Y`
are closed immersions, hence representable. Stacks 07VV concludes. -/
private theorem isRepresentable_pullback_of_baseChange
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} {i : Y' ⟶ Y} (hi : IsClosedImmersion B S hS i)
    (hsurj : Function.Surjective (pointsMap B S hS Y' i))
    (hbc : IsClosedImmersion B S hS (pullback.snd f i))
    (a : BigFppfOver B S hS) (g : yoneda.obj a ⟶ Y)
    (h09YA : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Z'),
      IsAlgebraicSpace B S hS Z → IsAlgebraicSpace B S hS Z' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Z' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Z'),
      IsAlgebraicSpace B S hS Z → IsAlgebraicSpace B S hS Z' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS Z →
      IsAffineSpace B S hS Z') :
    (pullback f g).IsRepresentable := by
  have sqV := hi.rep.isPullback g
  have sqc := IsPullback.of_right' (isPullback_baseChange_paste B S hS hi hbc g)
    (IsPullback.of_hasPullback f g)
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
  exact isRepresentable_of_isClosedImmersion_of_surjective B S hS hPalg _ hcci hcsurj
    inferInstance h09YA h07SQ hFinitePresentation

/-! ### Stacks 08B2 -/

/-- **Stacks 08B2.** Let `f : X ⟶ Y` and `i : Y' ⟶ Y` be morphisms of algebraic spaces over `S`.
If `i` is a closed immersion, bijective on points, if the base change of `f` along `i` is a
closed immersion, and if either `f` is of finite type or `i` is of finite presentation, then `f`
is a closed immersion. -/
@[stacks 08B2 "granted the three hypotheses of Stacks 07VT, carried unchanged from Stacks 07VV: \
`h09YA`, `h07SQ` and `hFinitePresentation`. None is the universally quantified form of this \
conclusion, which is about closed immersions"]
theorem isClosedImmersion_of_infinitesimal_baseChange
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (i : Y' ⟶ Y) (hi : IsClosedImmersion B S hS i)
    (hbij : Function.Bijective (pointsMap B S hS Y' i))
    (hbc : IsClosedImmersion B S hS (pullback.snd f i))
    (hfin : IsFiniteType B S hS f ∨ IsFinitePresentation B S hS i)
    (h09YA : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Z'),
      IsAlgebraicSpace B S hS Z → IsAlgebraicSpace B S hS Z' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Z' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Z'),
      IsAlgebraicSpace B S hS Z → IsAlgebraicSpace B S hS Z' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS Z →
      IsAffineSpace B S hS Z') :
    IsClosedImmersion B S hS f := by
  -- `f` is relatively representable.
  have hrep : yoneda.relativelyRepresentable f := by
    intro a g
    have hPrep := isRepresentable_pullback_of_baseChange B S hS hX hY hi hbij.2 hbc a g
      h09YA h07SQ hFinitePresentation
    have _ := hPrep
    refine ⟨(pullback f g).reprX,
      yoneda.preimage ((pullback f g).reprW.hom ≫ pullback.snd f g),
      (pullback f g).reprW.hom ≫ pullback.fst f g, ?_⟩
    rw [yoneda.map_preimage]
    have hiso : IsPullback (pullback f g).reprW.hom
        ((pullback f g).reprW.hom ≫ pullback.snd f g) (pullback.snd f g)
        (𝟙 (yoneda.obj a)) := IsPullback.of_horiz_isIso ⟨by simp⟩
    have h := IsPullback.paste_horiz hiso (IsPullback.of_hasPullback f g)
    simpa using h
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
    rcases hfin with hft | hfp
    · intro a g
      have hft' := (holdsOnEveryEtaleChart_iff_relative B S hS
        (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u})
        _root_.AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
        hX hY f hrep).mp hft.1
      have hqc' := presheaf_quasiCompact_of_isQuasiCompact B S hS hrep hft.2
      exact Or.inl ⟨hft'.property g _ _ (hrep.isPullback g),
        hqc'.property g _ _ (hrep.isPullback g)⟩
    · intro a g
      have _ : MorphismProperty.IsLocalAtTarget
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
  refine MorphismProperty.relative_of_snd hrep ?_
  intro a g
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
          hschm.isoPullback.inv ≫ (BigFppfOver.toScheme B S hS).map ρ := by
        rw [Iso.eq_inv_comp]
        exact hschm.isoPullback_hom_snd
      rw [heq]
      exact MorphismProperty.RespectsIso.precomp
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _ hρ
    have _ := hpbci
    exact _root_.AlgebraicGeometry.isClosedImmersion_of_infinitesimal_baseChange _ _ hbijSch
      (hfinSch a g)
  exact key _ (hbc.rep.snd (hi.rep.fst g)) _ (hbc.property_snd (hi.rep.fst g))
    (IsPullback.of_right' (isPullback_baseChange_paste B S hS hi hbc g) (hrep.isPullback g))

end AlgebraicGeometry.Space

end
