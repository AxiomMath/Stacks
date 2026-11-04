module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OpenImmersionCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsInducingTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAtlasTest
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative

/-!
# Smooth monomorphisms are open immersions

A monomorphism of algebraic spaces over `S` which is smooth is an open immersion, and a
1-morphism of algebraic stacks over `S` which is a monomorphism in the sense of **Stacks 04ZW**
and smooth in the sense of **Stacks 04XB** is an open immersion in the sense of part (1) of
**Stacks 04YL**.

For schemes this is **Stacks 025G**: a flat monomorphism which is locally of finite presentation
is an open immersion. A smooth morphism is flat and locally of finite presentation, so the
scheme-level statement is immediate from that tag; the content of this file is the passage to
algebraic spaces and then to algebraic stacks.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_mono_of_isLocallyOfFiniteType`: a monomorphism of
  algebraic spaces over `S` which is locally of finite type and whose target is representable
  has representable source.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_mono_of_isLocallyOfFiniteType`: such a
  monomorphism is representable by schemes.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isSmooth_of_mono`: a smooth monomorphism of
  algebraic spaces over `S` is an open immersion.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_mono`: the same for an étale
  monomorphism, étaleness of a chart diagram implying smoothness.
* `Stack.AlgebraicStacks.isOpenImmersion_of_isRelativelySmooth_of_isMonomorphism`: a 1-morphism
  of algebraic stacks over `S` which is smooth in the sense of Stacks 04XB and a monomorphism is
  an open immersion.
* `Stack.AlgebraicStacks.isOpenImmersion_of_isSmooth_of_isMonomorphism`: the same with smoothness
  read as **Stacks 075U**, the smooth-diagram notion of smoothness of a 1-morphism of algebraic
  stacks.

## Implementation notes

The three inputs that make the space-level statement work are the following.

*Representability.* `AlgebraicGeometry.Space.IsOpenImmersion` (**Stacks 02YU**, part (1)) is the
relative morphism property of `CategoryTheory.MorphismProperty.presheaf` at open immersions of
schemes, so it asserts in particular that the morphism is representable by schemes. That is not
automatic for a morphism of algebraic spaces, and it is exactly where the monomorphism
hypothesis is used a first time: a monomorphism locally of finite type is separated and locally
quasi-finite (**Stacks 0463**), and a separated locally quasi-finite morphism of algebraic
spaces is representable by schemes (**Stacks 0418**). Smoothness supplies local finite type
(**Stacks 06MH**).

*Smoothness on every represented base change.* `AlgebraicGeometry.Space.IsSmooth`
(**Stacks 03ZC**, part (1)) is the every-étale-chart condition, which is not literally a
statement about represented base changes. The passage is **Stacks 02WZ**,
`AlgebraicGeometry.presheaf_inverseImage_iff_atlas_snd`: for a representable morphism, a
base-change stable, fppf local property holds on every represented base change as soon as it
holds on the base change along one surjective étale chart of the target. The chart used is the
one the representability provides: the represented base change of the morphism along a scheme
atlas of the target is a commuting square of étale charts, its left-hand leg being the base
change of the atlas, so the chart condition applies to it directly. Fppf locality of smoothness
is **Stacks 02VL** read through
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`.

*Monomorphy on every represented base change.* Monomorphy of a morphism of algebraic spaces is
monomorphy of the underlying morphism of presheaves, which passes to any base change, and the
Yoneda embedding reflects monomorphisms, so each represented base change is a monomorphism of
the big fppf category over `S`. To read it as a monomorphism of schemes one uses that
`AlgebraicGeometry.BigFppfOver.toScheme` preserves fibre products, hence monomorphisms.

At the level of algebraic stacks all three notions involved — smoothness in the sense of
Stacks 04XB, monomorphy in the sense of Stacks 04ZW, and open immersion in the sense of part (1)
of Stacks 04YL — quantify over the same data: a scheme-valued point of the target and an
algebraic space representing the base change along it. So the stack-level statement is the
space-level one applied to each of those algebraic spaces, the two readings of monomorphy being
exchanged by `AlgebraicGeometry.Space.mono_hom_iff_mono` (**Stacks 042M**).

Both readings of smoothness of a 1-morphism of algebraic stacks are covered. The Stacks 04XB
relative one, `AlgebraicGeometry.Stack.IsRelativelySmooth`, is what the proof consumes; the
smooth-diagram one of **Stacks 075U**,
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth`, reduces to it by **Stacks 06FM**, whose
hypotheses are discharged for smoothness — smooth locality on the source and target is
**Stacks 06FC** and the two instance hypotheses are **Stacks 03ZE** and **Stacks 0429**. So
neither statement carries a hypothesis on the property.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 02VL](https://stacks.math.columbia.edu/tag/02VL)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MH](https://stacks.math.columbia.edu/tag/06MH)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A monomorphism of algebraic spaces over `S` which is locally of finite type and whose target
is representable has representable source: such a monomorphism is separated and locally
quasi-finite by **Stacks 0463**, and **Stacks 03XX** then applies. -/
theorem isRepresentable_of_mono_of_isLocallyOfFiniteType (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) (hmono : Mono f)
    (hYrep : Y.IsRepresentable) :
    X.IsRepresentable :=
  have h := isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS f ⟨hft, hmono⟩
  isRepresentable_of_locallyQuasiFinite_separated B S hS X Y hX hY f hYrep h.2 h.1

/-- A monomorphism of algebraic spaces over `S` which is locally of finite type is representable
by schemes: it is separated and locally quasi-finite by **Stacks 0463**, and **Stacks 0418**
then applies. -/
theorem relativelyRepresentable_of_mono_of_isLocallyOfFiniteType (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) (hmono : Mono f) :
    yoneda.relativelyRepresentable f :=
  have h := isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS f ⟨hft, hmono⟩
  relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY h.2 h.1

/-- **A smooth monomorphism of algebraic spaces over `S` is an open immersion.**

The morphism is representable by schemes, being a monomorphism locally of finite type
(**Stacks 0463** and **Stacks 0418**). Every represented base change of it is then a smooth
morphism of schemes — the every-étale-chart form of smoothness gives this on the base change
along one scheme atlas of the target, and **Stacks 02WZ** spreads it to all of them, smoothness
being stable under base change and fppf local on the base — and is a monomorphism of schemes,
monomorphy of presheaves passing to base changes and the forgetful functor to schemes
preserving fibre products. A flat monomorphism of schemes which is locally of finite
presentation is an open immersion, **Stacks 025G**. -/
theorem isOpenImmersion_of_isSmooth_of_mono (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hsm : IsSmooth B S hS f) (hmono : Mono f) :
    IsOpenImmersion B S hS f := by
  have := hmono
  have hft : IsLocallyOfFiniteType B S hS f := isLocallyOfFiniteType_of_isSmooth B S hS hsm
  have hrep : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_mono_of_isLocallyOfFiniteType B S hS f hX hY hft hmono
  have _hlocal : MorphismProperty.IsLocalAtTarget
      (@Smooth.{u} : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have _hetbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  obtain ⟨U, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  have hsmrel : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Smooth.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f := by
    rw [presheaf_inverseImage_iff_atlas_snd B S hS
      (@Smooth.{u} : MorphismProperty Scheme.{u}) f hrep U q hqSurj hqEtale]
    refine hsm _ _ (hrep.fst q) q (hrep.snd q) ?_ hqEtale (hrep.isPullback q).w.symm
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hrep.isPullback q).flip hqEtale
  refine ⟨hrep, fun a b g fst snd sq => ?_⟩
  have _hsmg : Smooth ((BigFppfOver.toScheme B S hS).map snd) := hsmrel.property g fst snd sq
  have : Mono (yoneda.map snd) := sq.mono_snd_of_mono
  have : Mono snd := Functor.mono_of_mono_map yoneda inferInstance
  have : Mono ((BigFppfOver.toScheme B S hS).map snd) := mono_toScheme_map B S hS snd
  show _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map snd)
  exact IsOpenImmersion.of_flat_of_mono _

/-- **An étale monomorphism of algebraic spaces over `S` is an open immersion.** An étale
morphism of algebraic spaces is smooth, so this is
`AlgebraicGeometry.Space.isOpenImmersion_of_isSmooth_of_mono`. -/
theorem isOpenImmersion_of_isEtale_of_mono (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (het : IsEtale B S hS f) (hmono : Mono f) :
    IsOpenImmersion B S hS f :=
  isOpenImmersion_of_isSmooth_of_mono B S hS f hX hY (isSmooth_of_isEtale B S hS hY het) hmono

end Space

namespace Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **A 1-morphism of algebraic stacks over `S` which is smooth in the sense of Stacks 04XB and
a monomorphism is an open immersion.**

All three notions quantify over a scheme-valued point of the target and an algebraic space
representing the base change of the 1-morphism along it, and assert something about the
structural morphism of that algebraic space: that it is smooth, that it is a monomorphism, that
it is an open immersion. So the statement is
`AlgebraicGeometry.Space.isOpenImmersion_of_isSmooth_of_mono` applied to each such algebraic
space, monomorphy in the category of algebraic spaces and monomorphy of the underlying
presheaves being exchanged by **Stacks 042M**. Representability by algebraic spaces is the first
conjunct of both the hypothesis and the conclusion and is carried over unchanged. -/
theorem isOpenImmersion_of_isRelativelySmooth_of_isMonomorphism (f : 𝒳 ⟶ 𝒴)
    (hsm : Stack.IsRelativelySmooth B S hS f.hom)
    (hmono : IsMonomorphism B S hS f) :
    IsOpenImmersion B S hS f := by
  obtain ⟨_hfrep, hP⟩ := hsm
  refine ⟨hmono.1, fun U y hy F hF hne => ?_⟩
  have hmg := hmono.2 U y hy F hF hne
  exact Space.isOpenImmersion_of_isSmooth_of_mono B S hS _
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) (hP U y hy F hF hne)
    ((Space.mono_hom_iff_mono B S hS _).mpr hmg)

/-- **A smooth monomorphism of algebraic stacks over `S` is an open immersion.**

Smoothness is here the notion of **Stacks 075U**, the existential smooth-diagram test of
**Stacks 06FM**. Smoothness of morphisms of algebraic spaces is smooth local on the source and
target (**Stacks 06FC**), stable under base change (**Stacks 03ZE**) and fppf local on the
target (**Stacks 0429** through
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`), so Stacks 06FM identifies that test
with the relative property of **Stacks 04XB**, and
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_of_isRelativelySmooth_of_isMonomorphism`
applies. The representability by algebraic spaces that Stacks 06FM asks for is the first
conjunct of the monomorphism hypothesis. -/
theorem isOpenImmersion_of_isSmooth_of_isMonomorphism (f : 𝒳 ⟶ 𝒴)
    (hsm : IsSmooth B S hS f) (hmono : IsMonomorphism B S hS f) :
    IsOpenImmersion B S hS f := by
  let smoothP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ k => Space.IsSmooth B S hS k
  let _hbc : (Stack.spaceProperty B S hS smoothP).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  let _hfpqc : (Stack.spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u} B S hS) :=
    Space.smooth_isLocalAtTarget_fpqc B S hS
  let _hfppf : (Stack.spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact isOpenImmersion_of_isRelativelySmooth_of_isMonomorphism B S hS f
    ⟨hmono.1, (Stack.hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS smoothP
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) 𝒳.property 𝒴.property
      f.hom hmono.1).mp hsm⟩ hmono

end Stack.AlgebraicStacks

end AlgebraicGeometry

end
