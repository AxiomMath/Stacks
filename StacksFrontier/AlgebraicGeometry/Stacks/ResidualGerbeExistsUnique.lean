module

public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackLocalImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFromMonomorphism

/-!
# The equivalent conditions of Stacks 06MT and the residual gerbe

Let `𝒳` be an algebraic stack over `S` and let `x` be a point of `|𝒳|` in the sense of
**Stacks 04XG**. **Stacks 06MT** offers three conditions on the pair `(𝒳, x)`:

1. there are an algebraic stack `𝒵` over `S` and a monomorphism `𝒵 ⟶ 𝒳` such that `|𝒵|` is a
   singleton whose image in `|𝒳|` is `x`;
2. the same, with `𝒵` reduced;
3. there are an algebraic stack `𝒵` over `S`, a monomorphism `f : 𝒵 ⟶ 𝒳` and a surjective flat
   1-morphism `z : Spec(k) ⟶ 𝒵` out of the spectrum of a field, with `x` the image of `z` under
   `f`;

and it asserts that the three are equivalent, and that when they hold there is a unique strictly
full subcategory `𝒵_x ⊂ 𝒳` which is a reduced, locally Noetherian algebraic stack whose space of
points is a singleton mapping to `x`. The three conditions are the library's
`AlgebraicGeometry.Stack.HasSingletonPointMonomorphism`,
`AlgebraicGeometry.Stack.HasReducedSingletonPointMonomorphism` and
`AlgebraicGeometry.Stack.HasFlatFieldCoverMonomorphism` of
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe`, and the specification of `𝒵_x` is
`AlgebraicGeometry.Stack.IsResidualGerbeAt` there.

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
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_flatFieldCover`; both are proved, and
both are used below rather than reproved.

The implication (1) ⟹ (2) is the source's own argument — replace `𝒵` by its reduction `𝒵_red`,
which is `AlgebraicGeometry.Stack.exists_reduction`, the reduced closed substack of
**Stacks 0509** on the whole of `|𝒵|`.

## Main results

* `AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_iff_hasSingletonPointMonomorphism`:
  the equivalence of conditions (1) and (2) of **Stacks 06MT**, with no hypothesis.
* `AlgebraicGeometry.Stack.tfae_hasSingletonPointMonomorphism`: the equivalence of the three
  conditions of **Stacks 06MT**.
* `AlgebraicGeometry.Stack.eq_of_isResidualGerbeAt_of_bootstrap`: the uniqueness half of the final
  assertion of **Stacks 06MT**.
* `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isMonomorphism_of_substack`: the existence
  half of the final assertion, from a monomorphism as in condition (2) and a substack of its
  source as in **Stacks 06MR**.
* `AlgebraicGeometry.Stack.existsUnique_isResidualGerbeAt`: the final assertion of
  **Stacks 06MT**, existence and uniqueness of the residual gerbe.

* `AlgebraicGeometry.Stack.tfae_hasSingletonPointMonomorphism_and_existsUnique_isResidualGerbeAt`:
  **Stacks 06MT** in full, the equivalence of the three conditions together with the final
  assertion.

The equivalence of conditions (2) and (3) is
`AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism`
of `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions`, which also states the
equivalences of (1) with (2) and with (3), both proved there through
`AlgebraicGeometry.Stack.exists_reduction`.

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

Both halves follow the source.

* Uniqueness: two strictly full subcategories meeting `AlgebraicGeometry.Stack.IsResidualGerbeAt`
  satisfy condition (2) of **Stacks 06MP**, and each fibre product of their inclusions projects
  by a monomorphism onto either factor, nonempty by **Stacks 04XH**, hence an equivalence by
  **Stacks 06MQ**. The monomorphy of the inclusion of a strictly full algebraic subcategory is the
  implication (2) ⟹ (3) of **Stacks 04Y5**, which the library has from the bootstrap theorem
  **Stacks 04S6** part (3), `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.
* Existence: a monomorphism `f : 𝒵 ⟶ 𝒳` as in condition (2) is fully faithful by the implication
  (1) ⟹ (2) of **Stacks 04ZZ**; a strictly full subcategory `𝒵' ⊂ 𝒵` as in **Stacks 06MR**
  includes fully faithfully into `𝒵`, so the composite is fully faithful with image `{x}` on
  points, and its essential image is the required subcategory of `𝒳`, by
  `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_full_of_faithful`. The source of `f` is
  reduced with one point but need not be locally Noetherian (Stacks 06MS is a reduced one-point
  algebraic space which is not), so the passage through Stacks 06MR cannot be skipped.

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
* [Stacks Project, Tag 06MS](https://stacks.math.columbia.edu/tag/06MS)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Conditions (1) and (2) -/

/-- **Conditions (1) and (2) of Stacks 06MT are equivalent.** Let `𝒳` be an algebraic stack over
`S` and let `x` be a point of `|𝒳|`. Some *reduced* algebraic stack admits a monomorphism to `𝒳`
whose space of points is a singleton mapping to `x` if and only if some algebraic stack does.

The forward implication is `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_reduced`,
which the source calls immediate. For the converse the source replaces the given `𝒵` by its
reduction, and so does this proof. The reduction is `AlgebraicGeometry.Stack.exists_reduction`,
the reduced closed substack of **Stacks 0509** on the whole of `|𝒵|`; its inclusion
`j : 𝒵_red ⟶ 𝒵` is a monomorphism, being representable by algebraic spaces as a closed immersion
and fully faithful as the inclusion of a full subcategory, so `j` composed with the given
monomorphism is one by **Stacks 04ZY**. The space `|𝒵_red|` is a singleton because `j` is
surjective on points by the choice of the reduction and injective on them by **Stacks 0500**,
`|𝒵|` being a singleton; and the unique point of `𝒵_red` maps to the unique point of `𝒵`, hence
to `x`. -/
theorem hasReducedSingletonPointMonomorphism_iff_hasSingletonPointMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    HasReducedSingletonPointMonomorphism B S hS 𝒳 x ↔
      HasSingletonPointMonomorphism B S hS 𝒳 x := by
  refine ⟨hasSingletonPointMonomorphism_of_reduced.{u, w} B S hS 𝒳 x, fun h => ?_⟩
  obtain ⟨𝒵, f, hf, z, hz, hzx⟩ := h
  obtain ⟨P, ⟨-, hPalg, hPimm⟩, hspec⟩ := exists_reduction.{u, w} B S hS 𝒵
  obtain ⟨hPred, hPsurj⟩ := hspec hPalg
  have hjmono : AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒵 P hPalg) :=
    ⟨hPimm.1, AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion B S hS 𝒵 P hPalg⟩
  obtain ⟨q, hq⟩ := hPsurj z
  exact ⟨fullSubcategoryAlgebraicStack 𝒵 P hPalg, fullSubcategoryInclusion 𝒵 P hPalg ≫ f,
    hPred, AlgebraicStacks.isMonomorphism_comp B S hS _ f hjmono hf, q, fun q' =>
      pointsMap_injective_of_fullyFaithful B S hS (fullSubcategoryInclusion 𝒵 P hPalg)
        ((hz _).trans hq.symm),
    (congrFun (AlgebraicStacks.pointsMap_comp B S hS _ f) q).trans
      ((congrArg (AlgebraicStacks.pointsMap B S hS f) hq).trans hzx)⟩

/-! ### The three conditions -/

/-- **Stacks 06MT, the equivalence of conditions (1), (2) and (3).** Let `𝒳` be an algebraic stack
over `S` and let `x` be a point of `|𝒳|`. The following are equivalent:

1. some algebraic stack admits a monomorphism to `𝒳` whose space of points is a singleton mapping
   to `x`;
2. some reduced algebraic stack does;
3. some algebraic stack `𝒵` admits a monomorphism `f : 𝒵 ⟶ 𝒳` and a surjective flat 1-morphism
   `z : Spec(k) ⟶ 𝒵` from the spectrum of a field, with `x = f(z)`.

The equivalence of (1) and (2) is
`AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_iff_hasSingletonPointMonomorphism`
and that of (2) and (3) is
`AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism`.
-/
theorem tfae_hasSingletonPointMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    List.TFAE
      [HasSingletonPointMonomorphism B S hS 𝒳 x,
        HasReducedSingletonPointMonomorphism B S hS 𝒳 x,
        HasFlatFieldCoverMonomorphism B S hS 𝒳 x] := by
  tfae_have 1 ↔ 2 :=
    (hasReducedSingletonPointMonomorphism_iff_hasSingletonPointMonomorphism.{u, w}
      B S hS 𝒳 x).symm
  tfae_have 2 ↔ 3 :=
    hasReducedSingletonPointMonomorphism_iff_hasFlatFieldCoverMonomorphism.{u, w} B S hS 𝒳 x
  tfae_finish

/-! ### The residual gerbe: uniqueness and existence -/

/-- **The existence half of the final assertion of Stacks 06MT, from a substack as in
Stacks 06MR.** Let `f : 𝒵 ⟶ 𝒳` be a monomorphism of algebraic stacks over `S` every point of
whose source lies over `x`, and let `P` cut out a strictly full subcategory of `𝒵` which is an
algebraic stack satisfying condition (2) of **Stacks 06MP**. Then some strictly full subcategory
of `𝒳` is a reduced, locally Noetherian algebraic stack with a single point lying over `x`.

This is the source's argument. The monomorphism `f` is fully faithful by the implication
(1) ⟹ (2) of **Stacks 04ZZ**, and the inclusion of the full subcategory cut out by `P` is fully
faithful, so the composite is. Its image on points is `{x}`: the subcategory has a point, by
condition (1) of **Stacks 06MP**, and every point of `𝒵` lies over `x`. The essential image of the
composite is the required subcategory, by
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_full_of_faithful`. -/
theorem exists_isResidualGerbeAt_of_isMonomorphism_of_substack
    {𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f) (x : AlgebraicStacks.points B S hS 𝒳)
    (hz : ∀ z, AlgebraicStacks.pointsMap B S hS f z = x) {P : ObjectProperty 𝒵.val.val.obj}
    (hP : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P) :
    ∃ Q : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x Q := by
  obtain ⟨-, hPalg, hcov⟩ := hP
  let i := fullSubcategoryInclusion 𝒵 P hPalg
  obtain ⟨hffull, hffaith⟩ :=
    AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism B S hS f hf
  have hifull : (CatFiberedInGroupoids.homFunctor i.hom).Full :=
    full_fullSubcategoryInclusion 𝒵 P hPalg
  have hifaith : (CatFiberedInGroupoids.homFunctor i.hom).Faithful :=
    faithful_fullSubcategoryInclusion 𝒵 P hPalg
  have hover : ∀ y, AlgebraicStacks.pointsMap B S hS (i ≫ f) y = x := fun y =>
    (congrFun (AlgebraicStacks.pointsMap_comp B S hS i f) y).trans (hz _)
  obtain ⟨y⟩ := (isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    B S hS _ hcov).1.2.1
  obtain ⟨Q, -, hQ, -⟩ := exists_isResidualGerbeAt_of_full_of_faithful B S hS 𝒳 _ (i ≫ f)
    (Functor.Full.comp (CatFiberedInGroupoids.homFunctor i.hom)
      (CatFiberedInGroupoids.homFunctor f.hom))
    (Functor.Faithful.comp (CatFiberedInGroupoids.homFunctor i.hom)
      (CatFiberedInGroupoids.homFunctor f.hom)) hcov x
    (Set.eq_singleton_iff_unique_mem.2 ⟨⟨y, hover y⟩, fun _ ⟨y', h⟩ => h.symm.trans (hover y')⟩)
  exact ⟨Q, hQ⟩

/-- Let `𝒳` be an algebraic stack over `S` and let `x` be a point of `|𝒳|` such that some
algebraic stack whose space of points is a singleton mapping to `x` admits a monomorphism to
`𝒳` (`HasSingletonPointMonomorphism`). Then there is exactly one strictly full subcategory
`𝒵_x ⊂ 𝒳` which is a reduced, locally Noetherian algebraic stack whose space of points is a
singleton mapping to `x`. -/
theorem existsUnique_isResidualGerbeAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳)
    (h : HasSingletonPointMonomorphism B S hS 𝒳 x) :
    ∃! P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P := by
  obtain ⟨𝒵, f, hred, hf, z, hz, hzx⟩ :=
    (hasReducedSingletonPointMonomorphism_iff_hasSingletonPointMonomorphism.{u, w}
      B S hS 𝒳 x).mpr h
  obtain ⟨P, hP⟩ :=
    exists_isReducedLocallyNoetherianUniquePointSubstack_of_isReducedWithUniquePoint.{u, w}
      B S hS 𝒵 ⟨hred, ⟨z⟩, ⟨fun a b => (hz a).trans (hz b).symm⟩⟩
  obtain ⟨Q, hQ⟩ := exists_isResidualGerbeAt_of_isMonomorphism_of_substack B S hS f hf x
    (fun z' => (congrArg _ (hz z')).trans hzx) hP
  exact ⟨Q, hQ, fun Q' hQ' => eq_of_isResidualGerbeAt_of_bootstrap B S hS hQ' hQ⟩

/-- **Stacks 06MT.** Let `𝒳` be an algebraic stack over `S` and let `x` be a point of `|𝒳|`. The
following are equivalent:

1. there exist an algebraic stack `𝒵` and a monomorphism `𝒵 ⟶ 𝒳` such that `|𝒵|` is a singleton
   whose image in `|𝒳|` is `x`;
2. there exist a reduced algebraic stack `𝒵` and a monomorphism `𝒵 ⟶ 𝒳` such that `|𝒵|` is a
   singleton whose image in `|𝒳|` is `x`;
3. there exist an algebraic stack `𝒵`, a monomorphism `f : 𝒵 ⟶ 𝒳` and a surjective flat
   1-morphism `z : Spec(k) ⟶ 𝒵` with `k` a field, such that `x = f(z)`.

Moreover, if these conditions hold, there is a unique strictly full subcategory `𝒵_x ⊂ 𝒳` which is
a reduced, locally Noetherian algebraic stack whose space of points is a singleton mapping to `x`.

The equivalence is `AlgebraicGeometry.Stack.tfae_hasSingletonPointMonomorphism` and the final
assertion is `AlgebraicGeometry.Stack.existsUnique_isResidualGerbeAt`. -/
@[stacks 06MT "the equivalence of conditions (1), (2) and (3), and the existence and uniqueness of \
the strictly full subcategory Z_x of X which is a reduced, locally Noetherian algebraic stack \
whose space of points is a singleton mapping to x"]
theorem tfae_hasSingletonPointMonomorphism_and_existsUnique_isResidualGerbeAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    List.TFAE
        [HasSingletonPointMonomorphism B S hS 𝒳 x,
          HasReducedSingletonPointMonomorphism B S hS 𝒳 x,
          HasFlatFieldCoverMonomorphism B S hS 𝒳 x] ∧
      (HasSingletonPointMonomorphism B S hS 𝒳 x →
        ∃! P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P) :=
  ⟨tfae_hasSingletonPointMonomorphism.{u, w} B S hS 𝒳 x,
    existsUnique_isResidualGerbeAt.{u, w} B S hS 𝒳 x⟩

end AlgebraicGeometry.Stack

end
