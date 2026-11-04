module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism

/-!
# Properness of a base change over a scheme of the site

Let `S` be a scheme contained in a big fppf site `B`. A morphism `a : F ⟶ Z` of algebraic
spaces over `S` whose target is the universe-lifted Yoneda presheaf of an object of the site
is proper in the sense of **Stacks 03ZM** exactly when it is proper as a morphism of formal
algebraic spaces in the sense of **Stacks 0AM6**: the second condition tests the first on
every base change along a scheme-valued point of `Z`, and properness of morphisms of algebraic
spaces is stable under such base changes.

That is the content of the reverse implication (4) ⇒ (3) of **Stacks 0ART**, whose other
implications live in `StacksFrontier.AlgebraicGeometry.FormalSpace.Proper`.

## Main results

* `AlgebraicGeometry.Space.isSeparatedULift_of_isPullback`,
  `AlgebraicGeometry.Space.isQuasiCompactULift_of_isPullback` and
  `AlgebraicGeometry.Space.universallyClosedULift_of_isPullback`: three of the four conjuncts
  of properness of a morphism of large-valued algebraic spaces are stable under base change.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_pullback_fst_uliftYoneda`: the
  every-étale-chart condition of **Stacks 03MJ** for a base-change stable property of
  morphisms of schemes is inherited by a base change along a morphism of universe-lifted
  Yoneda presheaves.
* `AlgebraicGeometry.Space.isProperULift_pullback_fst_uliftYoneda`: properness of a morphism
  of large-valued algebraic spaces over a universe-lifted Yoneda presheaf is inherited by its
  base changes along morphisms of universe-lifted Yoneda presheaves.
* `AlgebraicGeometry.FormalSpace.isProper_of_isAlgebraicSpaceULift`: a morphism of fppf
  sheaves whose target is a scheme of the site, whose source is an algebraic space over `S`
  and which is proper as a morphism of algebraic spaces is proper as a morphism of formal
  algebraic spaces.
* `FormalSpace.IsAlgebraicAndProperOnAffineBaseChanges.isProperOnAffineBaseChanges`:
  the implication (4) ⇒ (3) of **Stacks 0ART**.

## Implementation notes

Three of the four conjuncts of properness are stable under base change with no hypothesis on
the presheaves involved. Separatedness is the diagonal of a relative property, and both
constructions preserve base-change stability, so nothing beyond
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal` is needed. Quasi-compactness
and universal closedness are quantifications over base changes of the morphism, so a base
change of a base change is again one, by the horizontal pasting of cartesian squares; the
resulting fibre product is compared with the canonical one along
`CategoryTheory.IsPullback.isoPullback`, exactly as in
`AlgebraicGeometry.Space.universallyClosedULift_precomp`.

Being locally of finite type is not of either shape: it is the every-étale-chart condition of
Stacks 03MJ, and a chart of the target of a base change composes to an étale chart of the
original target only when the morphism base changed along is itself étale. It is proved here
for a base change along a morphism of universe-lifted Yoneda presheaves, which is the case the
implication (4) ⇒ (3) needs and the case in which the fibre product of an étale chart of the
source with the point of the target is again representable: by full faithfulness of the
universe-lifted Yoneda embedding both the point and the composite of the chart with the
morphism come from the site, so their fibre product does. The resulting representable is a
surjective étale chart of the base change, and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_of_surjectiveChart` — the implication
(2) ⇒ (1) of Stacks 03MJ — turns the one chart into all of them. The chart's morphism to the point
is a base change in the site of the chart's morphism for the original morphism, which is where
base-change stability of the property of morphisms of schemes enters.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0ART](https://stacks.math.columbia.edu/tag/0ART)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of the conjuncts of properness -/

section BaseChange

attribute [local instance] pointTopologyULift

variable {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {a : F ⟶ G} {g : G' ⟶ G} {k : F' ⟶ F} {a' : F' ⟶ G'}

/-- Separatedness of a morphism of algebraic spaces over `S` with values in `Type (max w u)`
is stable under base change: it is the diagonal of a relative property along the
universe-lifted Yoneda embedding, and both constructions preserve base-change stability. -/
theorem isSeparatedULift_of_isPullback (sq : IsPullback k a' a g)
    (ha : IsSeparatedULift.{w} B S hS a) : IsSeparatedULift.{w} B S hS a' := by
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (uliftYoneda.{w} (C := BigFppfOver B S hS)) |>.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{w}) _
  have := hbc.respectsIso
  exact hbc.diagonal.of_isPullback sq ha

/-- A base change of a base change of `a` along `h` is a base change of `a` along `h ≫ g`. -/
private theorem isPullback_pullback_fst_comp {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (sq : IsPullback k a' a g) (h : Z ⟶ G') :
    IsPullback (pullback.fst h a') (pullback.snd h a' ≫ k) (h ≫ g) a :=
  ((IsPullback.of_hasPullback h a').flip.paste_horiz sq).flip

/-- Quasi-compactness of a morphism of presheaves on the big fppf site of `S` with values in
`Type (max w u)` is stable under base change: a base change of the base change is a base
change of the morphism. -/
theorem isQuasiCompactULift_of_isPullback (sq : IsPullback k a' a g)
    (ha : IsQuasiCompactULift.{w} B S hS a) : IsQuasiCompactULift.{w} B S hS a' := by
  intro Z hZalg hZqc h
  have hpb := isPullback_pullback_fst_comp B S hS sq h
  exact isQuasiCompactSpaceULift_of_iso B S hS hpb.isoPullback.symm
    (ha Z hZalg hZqc (h ≫ g))

/-- Universal closedness of a morphism of presheaves on the big fppf site of `S` with values
in `Type (max w u)` is stable under base change: a base change of the base change is a base
change of the morphism. -/
theorem universallyClosedULift_of_isPullback (sq : IsPullback k a' a g)
    (ha : UniversallyClosedULift.{w} B S hS a) : UniversallyClosedULift.{w} B S hS a' := by
  intro Z hZalg h
  have hpb := isPullback_pullback_fst_comp B S hS sq h
  exact isClosedMap_pointsMapULift_of_comp_isIso B S hS hpb.isoPullback.hom
    hpb.isoPullback_hom_fst (ha Z hZalg (h ≫ g))

end BaseChange

/-! ### Base change of the every-étale-chart condition over a scheme of the site -/

/-- The every-étale-chart condition of **Stacks 03MJ** for a property `P` of morphisms of
schemes which is étale local on the source and the target and stable under base change is
inherited by the base change of a morphism of algebraic spaces over `S` with representable
target along a morphism of universe-lifted Yoneda presheaves.

A surjective étale chart of the source of the morphism has representable fibre product with
the point of the target, since both of the morphisms it is taken over come from the site; that
fibre product is a surjective étale chart of the base change, and its morphism to the point is
the base change in the site of the chart's morphism to the target. -/
theorem holdsOnEveryEtaleChartULift_pullback_fst_uliftYoneda (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPbc : P.IsStableUnderBaseChange)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    {Z U : BigFppfOver B S hS} (a : F ⟶ (uliftYoneda.{w}).obj Z)
    (ξ : (uliftYoneda.{w}).obj U ⟶ (uliftYoneda.{w}).obj Z)
    (ha : HoldsOnEveryEtaleChartULift.{w} B S hS P a) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P (pullback.fst ξ a) := by
  obtain ⟨UF, αF, hαFsurj, hαFet⟩ := hF.exists_atlas
  obtain ⟨m, hm⟩ : ∃ m : UF ⟶ Z, (uliftYoneda.{w}).map m = αF ≫ a :=
    ⟨(uliftYoneda.{w}).preimage (αF ≫ a), by simp⟩
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : U ⟶ Z, (uliftYoneda.{w}).map ξ₀ = ξ :=
    ⟨(uliftYoneda.{w}).preimage ξ, by simp⟩
  have hT : IsAlgebraicSpaceULift.{w} B S hS (pullback ξ a) :=
    isAlgebraicSpaceULift_pullback B S hS ξ a
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U) hF
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS Z)
  have hPm : P ((BigFppfOver.toScheme B S hS).map m) :=
    ha UF Z αF (𝟙 _) m hαFet (relative_id_etale.{w} B S hS Z)
      (by rwa [Category.comp_id])
  have hsitePB : IsPullback (pullback.fst m ξ₀) (pullback.snd m ξ₀) m ξ₀ :=
    IsPullback.of_hasPullback m ξ₀
  have hQ : P ((BigFppfOver.toScheme B S hS).map (pullback.snd m ξ₀)) :=
    (inverseImage_isStableUnderBaseChange B S hS hPbc).of_isPullback hsitePB hPm
  have hcond : (uliftYoneda.{w}).map (pullback.snd m ξ₀) ≫ ξ =
      ((uliftYoneda.{w}).map (pullback.fst m ξ₀) ≫ αF) ≫ a := by
    rw [Category.assoc, ← hm, ← hξ₀, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (uliftYoneda.{w}).map pullback.condition.symm
  let α₀ : (uliftYoneda.{w}).obj (pullback m ξ₀) ⟶ pullback ξ a :=
    pullback.lift ((uliftYoneda.{w}).map (pullback.snd m ξ₀))
      ((uliftYoneda.{w}).map (pullback.fst m ξ₀) ≫ αF) hcond
  have hα₀fst : α₀ ≫ pullback.fst ξ a = (uliftYoneda.{w}).map (pullback.snd m ξ₀) :=
    pullback.lift_fst _ _ _
  have houter : IsPullback ((uliftYoneda.{w}).map (pullback.snd m ξ₀))
      ((uliftYoneda.{w}).map (pullback.fst m ξ₀)) ξ (αF ≫ a) := by
    rw [← hm, ← hξ₀]
    exact (hsitePB.map (uliftYoneda.{w})).flip
  have hsqα₀ : IsPullback α₀ ((uliftYoneda.{w}).map (pullback.fst m ξ₀))
      (pullback.snd ξ a) αF :=
    IsPullback.of_right (by rw [hα₀fst]; exact houter) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback ξ a)
  exact holdsOnEveryEtaleChartULift_of_surjectiveChart B S hS P hP hT
    (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U) (pullback m ξ₀) U α₀ (𝟙 _)
    (pullback.snd m ξ₀) (relative_of_isPullback B S hS hsqα₀ hαFet)
    (relative_id_etale.{w} B S hS U) (relative_of_isPullback B S hS hsqα₀ hαFsurj)
    (by rw [Category.comp_id, hα₀fst]) hQ

/-- Being locally of finite type (**Stacks 03XF**, part (1)) for a morphism of algebraic
spaces over `S` with values in `Type (max w u)` whose target is the universe-lifted Yoneda
presheaf of an object of the site is inherited by its base changes along morphisms of
universe-lifted Yoneda presheaves. -/
theorem isLocallyOfFiniteTypeULift_pullback_fst_uliftYoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    {Z U : BigFppfOver B S hS} (a : F ⟶ (uliftYoneda.{w}).obj Z)
    (ξ : (uliftYoneda.{w}).obj U ⟶ (uliftYoneda.{w}).obj Z)
    (ha : IsLocallyOfFiniteTypeULift.{w} B S hS a) :
    IsLocallyOfFiniteTypeULift.{w} B S hS (pullback.fst ξ a) :=
  holdsOnEveryEtaleChartULift_pullback_fst_uliftYoneda B S hS _
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange hF a ξ ha

/-- **Stacks 03ZM** is stable under base change over a scheme of the site: a proper morphism
of algebraic spaces over `S` with values in `Type (max w u)` whose target is the
universe-lifted Yoneda presheaf of an object of the site stays proper after base change along
a morphism of universe-lifted Yoneda presheaves. -/
theorem isProperULift_pullback_fst_uliftYoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    {Z U : BigFppfOver B S hS} (a : F ⟶ (uliftYoneda.{w}).obj Z)
    (ξ : (uliftYoneda.{w}).obj U ⟶ (uliftYoneda.{w}).obj Z)
    (ha : IsProperULift.{w} B S hS a) :
    IsProperULift.{w} B S hS (pullback.fst ξ a) := by
  have sq : IsPullback (pullback.snd ξ a) (pullback.fst ξ a) a ξ :=
    (IsPullback.of_hasPullback ξ a).flip
  exact ⟨isSeparatedULift_of_isPullback B S hS sq ha.1,
    ⟨isLocallyOfFiniteTypeULift_pullback_fst_uliftYoneda B S hS hF a ξ ha.2.1.1,
      isQuasiCompactULift_of_isPullback B S hS sq ha.2.1.2⟩,
    universallyClosedULift_of_isPullback B S hS sq ha.2.2⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves on the big fppf site of `S` whose target is a scheme of the
site, whose source is an algebraic space over `S` and which is proper as a morphism of
algebraic spaces is proper in the sense of **Stacks 0AM6**: each of its base changes along a
scheme-valued point of its target is a fibre product of algebraic spaces over an algebraic
space, hence an algebraic space, and properness over a scheme of the site is stable under such
base changes. -/
theorem isProper_of_isAlgebraicSpaceULift {W : FppfSheaf B S hS} {Z : BigFppfOver B S hS}
    (p : W ⟶ schemeSheaf B S hS Z)
    (hW : Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj)
    (hp : Space.IsProperULift.{u + 1} B S hS p.hom) :
    IsProper B S hS p :=
  ⟨fun U ξ => Space.isAlgebraicSpaceULift_pullback B S hS ξ p.hom
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U) hW
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z),
    fun _ ξ => Space.isProperULift_pullback_fst_uliftYoneda B S hS hW p.hom ξ hp⟩

/-- **Stacks 0ART, (4) implies (3).** If every base change of a morphism of formal algebraic
spaces over `S` along an affine scheme `Z` over `S` in the site is an algebraic space over `S`
whose projection to `Z` is proper as a morphism of algebraic spaces, then every such base
change is proper as a morphism of formal algebraic spaces: over a scheme of the site the two
conditions agree, properness of morphisms of algebraic spaces being stable under base change
along a scheme-valued point. -/
@[stacks 0ART "(4) implies (3)"]
theorem IsAlgebraicAndProperOnAffineBaseChanges.isProperOnAffineBaseChanges
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsAlgebraicAndProperOnAffineBaseChanges B S hS f) :
    IsProperOnAffineBaseChanges B S hS f := fun Z hZ g W p q sq =>
  isProper_of_isAlgebraicSpaceULift B S hS p (h Z hZ g W p q sq).1 (h Z hZ g W p q sq).2

/-- **Stacks 0ART, (3) is equivalent to (4).** Over an affine scheme of the site, properness
of the base change as a morphism of formal algebraic spaces and the conjunction of being an
algebraic space with properness of the projection as a morphism of algebraic spaces are the
same condition. -/
@[stacks 0ART "(3) is equivalent to (4)"]
theorem isProperOnAffineBaseChanges_iff_isAlgebraicAndProper {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) :
    IsProperOnAffineBaseChanges B S hS f ↔
      IsAlgebraicAndProperOnAffineBaseChanges B S hS f :=
  ⟨fun h => h.isAlgebraicAndProper B S hS,
    fun h => h.isProperOnAffineBaseChanges B S hS⟩

end AlgebraicGeometry.FormalSpace

end
