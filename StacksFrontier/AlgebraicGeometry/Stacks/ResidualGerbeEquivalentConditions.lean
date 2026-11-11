module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFromMonomorphism

/-!
# The equivalent conditions of Stacks 06MT

Let `𝒳` be an algebraic stack over `S` and let `x` be a point of `|𝒳|` in the sense of
**Stacks 04XG**. **Stacks 06MT** offers three conditions on the pair `(𝒳, x)`:

1. there are an algebraic stack `𝒵` over `S` and a monomorphism `𝒵 ⟶ 𝒳` such that `|𝒵|` is a
   singleton whose image in `|𝒳|` is `x`;
2. the same, with `𝒵` reduced;
3. there are an algebraic stack `𝒵` over `S`, a monomorphism `f : 𝒵 ⟶ 𝒳` and a surjective flat
   1-morphism `z : Spec(k) ⟶ 𝒵` out of the spectrum of a field, with `x` the image of `z` under
   `f`;

and it asserts that the three are equivalent. This file proves that assertion. The three
conditions are the library's `AlgebraicGeometry.Stack.HasSingletonPointMonomorphism`,
`AlgebraicGeometry.Stack.HasReducedSingletonPointMonomorphism` and
`AlgebraicGeometry.Stack.HasFlatFieldCoverMonomorphism` of
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe`, where they are stated.

For the equivalence of (2) and (3): condition (2) says exactly that some
monomorphism to `𝒳` with image `x` has reduced source with a singleton space of points, which is
condition (1) of **Stacks 06MN**, and condition (3) says that the same source carries a
surjective flat 1-morphism from the spectrum of a field, which is condition (2) of Stacks 06MN.
So the two are the two sides of
`AlgebraicGeometry.Stack.isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover` applied to the
source, with the point of `𝒳` carried along: a point of `𝒵` over `x` pulls back through the
cover because the cover is surjective, and a point of the cover pushes forward to the unique
point of `𝒵` because `|𝒵|` is a subsingleton.

The implication (2) ⟹ (1) is `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_reduced`
and the implication (3) ⟹ (1) is
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_flatFieldCover`; both are available, and
both are used below rather than reproved.

The implication (1) ⟹ (2) is the source's own argument — replace `𝒵` by its reduction `𝒵_red`,
which is `AlgebraicGeometry.Stack.exists_reduction`, the reduced closed substack of
**Stacks 0509** on the whole of `|𝒵|`.

## Main results

* `AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_of_hasSingletonPointMonomorphism`:
  the implication (1) ⟹ (2) of **Stacks 06MT**.
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_iff_hasReducedSingletonPointMonomorphism`,
  `AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism`
  and `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism`:
  the three equivalences of **Stacks 06MT**.
* `AlgebraicGeometry.Stack.eq_of_isResidualGerbeAt_of_bootstrap`: the uniqueness of the residual
  gerbe, half of the final assertion of **Stacks 06MT**.

The complete statement of **Stacks 06MT** — the three equivalences together with the existence and
uniqueness of the residual gerbe — is
`AlgebraicGeometry.Stack.tfae_hasSingletonPointMonomorphism_and_existsUnique_isResidualGerbeAt` of
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeExistsUnique`, where the tag is registered.

## The passage to the reduction

The monomorphy of the inclusion `𝒵_red ⟶ 𝒵` is proved: the inclusion is representable by
algebraic spaces because it is a closed immersion,
which is the content of `AlgebraicGeometry.Stack.IsClosedSubstack` (**Stacks 04YM** part (2)),
and it satisfies the monomorphy clause of **Stacks 04ZW** because it is fully faithful, by the
implication (2) ⟹ (1) of **Stacks 04ZZ** in the form
`AlgebraicGeometry.Stack.AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion`. The
source instead quotes **Stacks 0504**, that an immersion is a monomorphism, which this library
also has as `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_isImmersion`; the two
routes prove the same statement and the one taken here needs no further import.

## The final assertion

Stacks 06MT has a final assertion beyond the equivalence of the three conditions: when they hold
there is a *unique* strictly full subcategory of `𝒳` which is a reduced, locally Noetherian
algebraic stack whose space of points is a singleton over `x` — the residual gerbe of
**Stacks 06MU**, specified by `AlgebraicGeometry.Stack.IsResidualGerbeAt`.

`AlgebraicGeometry.Stack.eq_of_isResidualGerbeAt_of_bootstrap` is the uniqueness, by the source's
argument. That argument needs the inclusion of a strictly full algebraic subcategory to be a
monomorphism, so representable by algebraic spaces, which is the implication (2) ⟹ (3) of
**Stacks 04Y5**; the library has that implication from the bootstrap theorem Stacks 04S6 part (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`. The existence passes
through the existence half of **Stacks 06MR**, `AlgebraicGeometry.Stack`
`.exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint`, and is
proved in `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeExistsUnique` as
`AlgebraicGeometry.Stack.existsUnique_isResidualGerbeAt`.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZY](https://stacks.math.columbia.edu/tag/04ZY)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0500](https://stacks.math.columbia.edu/tag/0500)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Conditions (1) and (2) -/

/-- **The implication (1) ⟹ (2) of Stacks 06MT.** Let `𝒳` be an algebraic stack over `S` and let
`x` be a point of `|𝒳|`. If some algebraic stack admits a monomorphism to `𝒳` whose space of
points is a singleton mapping to `x`, then some *reduced* one does.

The source replaces the given `𝒵` by its reduction, and so does this proof. The reduction is
`AlgebraicGeometry.Stack.exists_reduction`, the reduced closed substack of **Stacks 0509** on the
whole of `|𝒵|`; its inclusion `j : 𝒵_red ⟶ 𝒵` is a monomorphism, being representable
by algebraic spaces as a closed immersion and fully faithful as the inclusion of a full
subcategory, so `j` composed with the given monomorphism is one by **Stacks 04ZY**. The space
`|𝒵_red|` is a singleton because `j` is surjective on points by the choice of the reduction and
injective on them by **Stacks 0500**, `|𝒵|` being a singleton; and the unique point of `𝒵_red`
maps to the unique point of `𝒵`, hence to `x`. -/
theorem hasReducedSingletonPointMonomorphism_of_hasSingletonPointMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳)
    (h : HasSingletonPointMonomorphism B S hS 𝒳 x) :
    HasReducedSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨𝒵, f, hf, z, hz, hzx⟩ := h
  obtain ⟨P, hclosed, hspec⟩ := exists_reduction.{u, w} B S hS 𝒵
  obtain ⟨-, hPalg, hPimm⟩ := hclosed
  obtain ⟨hPred, hPsurj⟩ := hspec hPalg
  have hjmono : AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒵 P hPalg) :=
    ⟨hPimm.1, fun U y hy F hF he =>
      AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion B S hS 𝒵 P hPalg
        U y hy F hF he⟩
  have hjinj := pointsMap_injective_of_fullyFaithful B S hS (fullSubcategoryInclusion 𝒵 P hPalg)
  obtain ⟨q, hq⟩ := hPsurj z
  refine ⟨fullSubcategoryAlgebraicStack 𝒵 P hPalg, fullSubcategoryInclusion 𝒵 P hPalg ≫ f,
    hPred, AlgebraicStacks.isMonomorphism_comp B S hS _ f hjmono hf, q, fun q' => ?_, ?_⟩
  · exact hjinj ((hz _).trans hq.symm)
  · calc AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒵 P hPalg ≫ f) q
        = AlgebraicStacks.pointsMap B S hS f
            (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒵 P hPalg) q) :=
          congrFun (AlgebraicStacks.pointsMap_comp B S hS _ f) q
      _ = AlgebraicStacks.pointsMap B S hS f z := by rw [hq]
      _ = x := hzx

/-- **Conditions (1) and (2) of Stacks 06MT are equivalent.** A point of an algebraic stack over
`S` is the image of the singleton space of points of a monomorphism to it exactly when it is the
image of the singleton space of points of a monomorphism with reduced source.

The implication (2) ⟹ (1) is
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_reduced`, which the source calls
immediate; the implication (1) ⟹ (2) is
`AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_of_hasSingletonPointMonomorphism`,
which passes to the reduction of Stacks 0509. -/
theorem hasSingletonPointMonomorphism_iff_hasReducedSingletonPointMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    HasSingletonPointMonomorphism B S hS 𝒳 x ↔
      HasReducedSingletonPointMonomorphism B S hS 𝒳 x :=
  ⟨hasReducedSingletonPointMonomorphism_of_hasSingletonPointMonomorphism.{u, w}
      B S hS 𝒳 x,
    hasSingletonPointMonomorphism_of_reduced.{u, w} B S hS 𝒳 x⟩

/-! ### Conditions (2) and (3) -/

/-- **Conditions (2) and (3) of Stacks 06MT are equivalent.** A point of an algebraic stack over
`S` is the image of the singleton space of points of a monomorphism with reduced source exactly
when it is the image, under a monomorphism, of a point of the spectrum of a field covering the
source surjectively and flatly.

Both directions are the equivalence of conditions (1) and (2) of **Stacks 06MN**,
`AlgebraicGeometry.Stack.isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover`, applied to the
source of the monomorphism, which is left unchanged. Going forwards, the unique point of the
source has a preimage on the cover because the cover is surjective; going backwards, the image
of the chosen point of the cover is a point of the source, and the source has at most one
point. -/
theorem hasReducedSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    HasReducedSingletonPointMonomorphism B S hS 𝒳 x ↔
      HasFlatFieldCoverMonomorphism B S hS 𝒳 x := by
  constructor
  · rintro ⟨𝒵, f, hred, hf, z, hz, hzx⟩
    obtain ⟨F, g, hsurj, hflat⟩ :=
      (isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵).mp
        ⟨hred, ⟨z⟩, ⟨fun a b => (hz a).trans (hz b).symm⟩⟩
    obtain ⟨q, hq⟩ := hsurj z
    have hqx : AlgebraicStacks.pointsMap B S hS f (AlgebraicStacks.pointsMap B S hS g q) = x := by
      rw [hq]
      exact hzx
    exact ⟨𝒵, f, F, g, hf, hsurj, hflat, q, hqx⟩
  · rintro ⟨𝒵, f, F, g, hf, hsurj, hflat, q, hqx⟩
    obtain ⟨hred, -, hsub⟩ :=
      (isReducedWithUniquePoint_iff_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵).mpr
        ⟨F, g, hsurj, hflat⟩
    exact ⟨𝒵, f, hred, hf, AlgebraicStacks.pointsMap B S hS g q,
      fun z' => hsub.elim z' _, hqx⟩

/-! ### Conditions (1) and (3) -/

/-- **Conditions (1) and (3) of Stacks 06MT are equivalent.** The implication (1) ⟹ (3) is
(1) ⟹ (2) followed by (2) ⟹ (3); the implication (3) ⟹ (1) is
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_flatFieldCover`. -/
theorem hasSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    HasSingletonPointMonomorphism B S hS 𝒳 x ↔ HasFlatFieldCoverMonomorphism B S hS 𝒳 x :=
  ⟨fun h => (hasReducedSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism.{u, w}
      B S hS 𝒳 x).mp
    (hasReducedSingletonPointMonomorphism_of_hasSingletonPointMonomorphism.{u, w}
      B S hS 𝒳 x h),
    hasSingletonPointMonomorphism_of_flatFieldCover.{u, w} B S hS 𝒳 x⟩

/-! ### The residual gerbe: uniqueness and existence -/

/-- **The specification of the residual gerbe is condition (2) of Stacks 06MP for a substack.** An
object property of `𝒳` meeting `AlgebraicGeometry.Stack.IsResidualGerbeAt` cuts out a strictly
full algebraic subcategory admitting a surjective flat 1-morphism, locally of finite presentation,
from the spectrum of a field: its full subcategory is reduced, locally Noetherian and one-point,
which is condition (1) of **Stacks 06MP**. -/
theorem isReducedLocallyNoetherianUniquePointSubstack_of_isResidualGerbeAt
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {x : AlgebraicStacks.points B S hS 𝒳}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsResidualGerbeAt B S hS 𝒳 x P) :
    IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒳 P := by
  obtain ⟨hiso, hPalg, hred, hnoeth, z, hz, -⟩ := hP
  exact ⟨hiso, hPalg, hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian
    B S hS _ ⟨⟨hred, ⟨z⟩, ⟨fun a b => (hz a).trans (hz b).symm⟩⟩, hnoeth⟩⟩

/-- **Every point of a residual gerbe at `x` lies over `x`.** -/
theorem pointsMap_eq_of_isResidualGerbeAt
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {x : AlgebraicStacks.points B S hS 𝒳}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsResidualGerbeAt B S hS 𝒳 x P)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (z : AlgebraicStacks.points B S hS (fullSubcategoryAlgebraicStack 𝒳 P hPalg)) :
    AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hPalg) z = x := by
  obtain ⟨_, _, _, _, z₀, hz₀, hz₀x⟩ := hP
  exact (congrArg _ (hz₀ z)).trans hz₀x

/-- **The uniqueness assertion of Stacks 06MT.** Let `𝒳` be an
algebraic stack over `S` and `x` a point of `|𝒳|`. Two strictly full subcategories of `𝒳` which
are reduced, locally Noetherian algebraic stacks with a single point lying over `x` coincide.

This is the source's argument. Both subcategories satisfy condition (2) of **Stacks 06MP**, by its
implication (1) ⟹ (2); the first projection `𝒵_P ×_𝒳 𝒵_Q ⟶ 𝒵_P` is a monomorphism, as a base
change of the inclusion of `𝒵_Q`; its source has a point by **Stacks 04XH**, both points lying
over `x`; so it is an equivalence by **Stacks 06MQ**, and every object satisfying `P` satisfies
`Q`. That argument is `AlgebraicGeometry.Stack.imp_of_isReducedLocallyNoetherianUniquePointSubstack`.

The inclusion of `𝒵_Q` is a monomorphism of algebraic stacks only once it is known to be
representable by algebraic spaces, which the source takes from the implication (2) ⟹ (3) of
**Stacks 04Y5**; the library has that implication from the bootstrap theorem Stacks 04S6
part (3), `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`. -/
theorem eq_of_isResidualGerbeAt_of_bootstrap
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {x : AlgebraicStacks.points B S hS 𝒳}
    {P Q : ObjectProperty 𝒳.val.val.obj} (hP : IsResidualGerbeAt B S hS 𝒳 x P)
    (hQ : IsResidualGerbeAt B S hS 𝒳 x Q) : P = Q := by
  have hP' := isReducedLocallyNoetherianUniquePointSubstack_of_isResidualGerbeAt B S hS hP
  have hQ' := isReducedLocallyNoetherianUniquePointSubstack_of_isResidualGerbeAt B S hS hQ
  exact funext fun X => propext
    ⟨imp_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒳 hP' hQ'
        (fun a b zP zQ => (pointsMap_eq_of_isResidualGerbeAt B S hS hP a zP).trans
          (pointsMap_eq_of_isResidualGerbeAt B S hS hQ b zQ).symm) X,
      imp_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒳 hQ' hP'
        (fun a b zQ zP => (pointsMap_eq_of_isResidualGerbeAt B S hS hQ a zQ).trans
          (pointsMap_eq_of_isResidualGerbeAt B S hS hP b zP).symm) X⟩

end AlgebraicGeometry.Stack

end
