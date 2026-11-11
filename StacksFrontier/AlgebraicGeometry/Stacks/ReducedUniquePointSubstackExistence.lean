module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsEquivalenceHomeomorph
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative

/-!
# The reduced locally Noetherian one-point substack exists (Stacks 06MR)

Let `𝒵` be an algebraic stack over `S` satisfying the equivalent conditions of **Stacks 06MN**,
that is, reduced with a singleton space of points. **Stacks 06MR** asserts that there is a unique
strictly full subcategory `𝒵' ⊂ 𝒵` which is an algebraic stack satisfying the equivalent
conditions of **Stacks 06MP**. Uniqueness is
`AlgebraicGeometry.Stack.eq_of_isReducedLocallyNoetherianUniquePointSubstack`, in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack`. This file proves existence.

The source's construction is: choose a field `k` and a surjective flat 1-morphism `U = Spec(k) ⟶ 𝒵`
locally of finite type, which is condition (3) of **Stacks 06MN**; form `R = U ×_𝒵 U`, an algebraic
space by **Stacks 04T4 (1)**, whose two projections are locally of finite type, hence — the target
being the spectrum of a field — flat and locally of finite presentation; conclude that the quotient
stack `[U/R]` of the groupoid of **Stacks 04T4 (4)** and **(5)** is an algebraic stack by
**Stacks 06FI**, that `U ⟶ [U/R]` is surjective, flat and locally of finite presentation by
**Stacks 06FH**, and that the canonical 1-morphism `[U/R] ⟶ 𝒵` is fully faithful by
**Stacks 04T4 (6)**; and finally *replace `[U/R]` by its essential image in `𝒵`*.

What is proved here is that last step, together with the transport of condition (2) of
Stacks 06MP that it needs. The essential image of a fully faithful 1-morphism of algebraic stacks
is closed under isomorphism, so the full subcategory it cuts out is a strictly full subcategory of
`𝒵`; that full subcategory is equivalent to the source over the big fppf site, by **Stacks 003Z**
applied to the factorization through the essential image; it is therefore an algebraic stack by
**Stacks 03YQ**; and condition (2) of Stacks 06MP travels along that equivalence, which is proved
below for each of its three clauses. The cover of the first step is condition (3) of
**Stacks 06MN**, which the library proves from condition (1) in
`AlgebraicGeometry.Stack.tfae_isReducedWithUniquePoint`. The steps from the cover to the quotient
stack are packaged as the universally quantified proposition described next, which the theorems
here take as a hypothesis; it is proved as
`AlgebraicGeometry.Stack.hasFullyFaithfulFinitePresentationPresentations` in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackLocalImage`, where the
unconditional statements are assembled.

## Main definitions

* `AlgebraicGeometry.Stack.HasFullyFaithfulFinitePresentationPresentations`: the source's steps
  from the cover to the quotient stack, as a proposition — an algebraic stack receiving a
  surjective flat 1-morphism, locally of finite type, from the algebraic stack of the spectrum of a
  field receives a *fully faithful* 1-morphism from an algebraic stack satisfying condition (2) of
  **Stacks 06MP**.

## Main results

* `AlgebraicGeometry.Stack.isSurjective_of_isEquivalenceFunctor`: a 1-morphism of algebraic stacks
  whose underlying functor is an equivalence of categories is surjective.
* `AlgebraicGeometry.Stack`
  `.hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor`: condition (2)
  of **Stacks 06MP** is invariant under a 1-morphism whose underlying functor is an equivalence of
  categories.
* `AlgebraicGeometry.Stack.isEquivalence_toEssImageBased_of_full_of_faithful`: the factorization of
  a fully faithful 1-morphism of algebraic stacks through the full subcategory cut out by its
  essential image has underlying functor an equivalence of categories.
* `AlgebraicGeometry.Stack.exists_isReducedLocallyNoetherianUniquePointSubstack`: the existence
  assertion of **Stacks 06MR**, from `HasFullyFaithfulFinitePresentationPresentations`.
* `AlgebraicGeometry.Stack.existsUnique_isReducedLocallyNoetherianUniquePointSubstack`: existence
  and uniqueness together, from the same proposition.

## Implementation notes

The proposition `HasFullyFaithfulFinitePresentationPresentations` is quantified over *every*
algebraic stack over `S`, every field spectrum and every 1-morphism; it is the conjunction of
**Stacks 04T4 (1)**, **(4)**, **(5)** and **(6)** with **Stacks 06FI**, and is proved, from
`AlgebraicGeometry.Stack.hasFullyFaithfulFiniteTypeFieldPointPresentations`, as
`AlgebraicGeometry.Stack.hasFullyFaithfulFinitePresentationPresentations` in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackLocalImage`.

Condition (2) of Stacks 06MP is a conjunction of three clauses about a 1-morphism out of the
algebraic stack of a field spectrum, and each travels along the equivalence by a different route.
Surjectivity is surjectivity of the map on the spaces of points of **Stacks 04XG**, so it follows
from `AlgebraicGeometry.Stack.bijective_pointsMap_of_basedEquivalence` and functoriality of that
map. Flatness is the *existential* smooth-diagram test of **Stacks 06PW** and local finite
presentation the *universal* one of **Stacks 06Q2**; both are turned into the relative property of
**Stacks 03YK** by the two directions of **Stacks 06FM**, which apply because the source of the
cover is representable by an algebraic space, so that the cover is representable by algebraic
spaces by `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`, and the
relative property then transports by **Stacks 0459**,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalences`, across the square whose top
1-morphism is the identity of the cover's source and whose bottom one is the equivalence. Going
through Stacks 0459 rather than through the smooth-diagram tests directly is what avoids having to
know that an equivalence over the site is a smooth 1-morphism, which this library does not record:
`AlgebraicGeometry.Stack.isRelativelySmooth_id` is stated only for a category representable by an
algebraic space.

The essential-image construction is the one of **Stacks 0506** in
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack`, whose three ingredients
`AlgebraicGeometry.Stack.AlgebraicStacks.closedUnderStronglyCartesian_essImage`,
`.isFiberedInGroupoids_essImage` and `.toEssImageBased` carry no hypothesis at all. Only the step
from there to an equivalence is gated in that file, by an immersion hypothesis used exclusively to
supply full faithfulness; `isEquivalence_toEssImageBased_of_full_of_faithful` is the same step from
full faithfulness itself, which is what **Stacks 04T4 (6)** delivers and what an immersion
hypothesis would not be available to provide here.

Strict fullness of the essential image is the Mathlib instance
`CategoryTheory.Functor.essImage.IsClosedUnderIsomorphisms`, so the first clause of
`AlgebraicGeometry.Stack.IsReducedLocallyNoetherianUniquePointSubstack` is discharged by instance
search.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The presentation ingredient -/

/-- **Stacks 04T4 (1), (4), (5) and (6) together with Stacks 06FI, as a proposition.** An algebraic
stack over `S` receiving a 1-morphism from the algebraic stack of the spectrum of a field which is
locally of finite type, surjective and flat receives a fully faithful 1-morphism from an algebraic
stack satisfying condition (2) of **Stacks 06MP**.

In the source this is the quotient stack `[U/R]` of the self-intersection groupoid of the cover,
algebraic by Stacks 06FI, covered by `U` by Stacks 06FH, and mapping fully faithfully to the target
by Stacks 04T4 (6). It is proved as
`AlgebraicGeometry.Stack.hasFullyFaithfulFinitePresentationPresentations` in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackLocalImage`. -/
abbrev HasFullyFaithfulFinitePresentationPresentations : Prop :=
  ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒳),
    AlgebraicStacks.IsLocallyOfFiniteType B S hS f → IsSurjective B S hS f →
      AlgebraicStacks.IsFlat B S hS f →
        ∃ (𝒴 : AlgebraicStacks.{u, w} B S hS) (i : 𝒴 ⟶ 𝒳),
          (CatFiberedInGroupoids.homFunctor i.hom).Full ∧
            (CatFiberedInGroupoids.homFunctor i.hom).Faithful ∧
            HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒴

/-! ### Condition (2) of Stacks 06MP travels along an equivalence over the site -/

/-- **A 1-morphism of algebraic stacks whose underlying functor is an equivalence of categories is
surjective.** Such a 1-morphism is the forward 1-morphism of an equivalence over the big fppf site,
by **Stacks 003Z**, and an equivalence over the site induces a bijection on the spaces of points of
**Stacks 04XG**. -/
theorem isSurjective_of_isEquivalenceFunctor {𝒴 𝒲 : AlgebraicStacks.{u, w} B S hS} (e : 𝒴 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom)) :
    IsSurjective B S hS e := by
  classical
  obtain ⟨e', he'⟩ := exists_basedEquivalence_functor_eq B S hS 𝒴.val 𝒲.val e.hom.hom he
  have hb := bijective_pointsMap_of_basedEquivalence B S hS
    (Classical.choose 𝒴.property) (Classical.choose 𝒲.property) e'
  rw [he'] at hb
  exact hb.2

/-- **Condition (2) of Stacks 06MP is invariant under a 1-morphism whose underlying functor is an
equivalence of categories.** A 1-morphism from the algebraic stack of the spectrum of a field which
is locally of finite presentation, surjective and flat stays so after composition with such a
1-morphism `e`.

Surjectivity is `AlgebraicGeometry.Stack.isSurjective_of_isEquivalenceFunctor` and functoriality of
the map on points. For the other two clauses the cover is representable by algebraic spaces, its
source being representable by an algebraic space, so the two directions of **Stacks 06FM** turn the
smooth-diagram tests of **Stacks 06PW** and **Stacks 06Q2** into the relative property of
**Stacks 03YK**, which transports across the square with the identity on top and `e` along the
bottom by **Stacks 0459**. -/
theorem hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor
    {𝒴 𝒲 : AlgebraicStacks.{u, w} B S hS} (e : 𝒴 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (h : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒴) :
    HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒲 := by
  classical
  obtain ⟨F, g, hlfp, hsurj, hflat⟩ := h
  have h𝒰rep : IsRepresentableByAlgebraicSpace B S hS (schemeStack.{u, w} B S hS F.base).val :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS F.base
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property h𝒰rep g.hom
  have hge : IsRepresentableByAlgebraicSpaces B S hS (g ≫ e).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒲.property h𝒰rep (g ≫ e).hom
  let iflat1 : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let iflat2 : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let ilfp1 : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let ilfp2 : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hbe : Functor.IsEquivalence e.hom.hom.toFunctor := he
  have hid : Functor.IsEquivalence
      (BasedFunctor.id (schemeStack.{u, w} B S hS F.base).val.val).toFunctor :=
    AlgebraicStacks.isEquivalence_basedFunctorId (𝒳 := schemeStack.{u, w} B S hS F.base)
  have α : BasedFunctor.comp (BasedFunctor.id (schemeStack.{u, w} B S hS F.base).val.val)
      (g ≫ e).hom.hom ≅ BasedFunctor.comp g.hom.hom e.hom.hom := Iso.refl _
  have hflatRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ k => Space.IsFlat B S hS k)) g.hom hg :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) g.hom hg
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).1 hflat)
  have hlfpRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS
        (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)) g.hom hg :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) g.hom hg
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        (schemeStack.{u, w} B S hS F.base).property 𝒴.property g.hom).1 hlfp)
  have key : ∀ (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      [(spaceProperty B S hS P).IsStableUnderBaseChange]
      [(spaceProperty B S hS P).IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      HasRelativeProperty.{u, u, u + 1, u} B S hS (spaceProperty B S hS P) g.hom hg →
        HasPropertyOnSomeSmoothDiagram B S hS P (g ≫ e).hom := fun P _ _ h =>
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS _ 𝒲.property (g ≫ e).hom hge
      ((hasRelativeProperty_iff_of_equivalences B S hS _ g.hom (g ≫ e).hom
        (BasedFunctor.id (schemeStack.{u, w} B S hS F.base).val.val) e.hom.hom α hge).2 h)
  refine ⟨F, g ≫ e, ?_, ?_, ?_⟩
  · exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS F.base).property 𝒲.property (g ≫ e).hom).2
      (key _ hlfpRel)
  · show Function.Surjective (AlgebraicStacks.pointsMap B S hS (g ≫ e))
    rw [AlgebraicStacks.pointsMap_comp B S hS g e]
    exact Function.Surjective.comp (isSurjective_of_isEquivalenceFunctor B S hS e he) hsurj
  · exact (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (g ≫ e)).2
      (key _ hflatRel)

/-! ### The essential image of a fully faithful 1-morphism -/

/-- **The factorization of a fully faithful 1-morphism of algebraic stacks through the full
subcategory cut out by its essential image has underlying functor an equivalence of categories.**

This is `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_toEssImageBased` with the immersion
hypothesis replaced by the full faithfulness it was used to produce: the factorization is full and
faithful because the 1-morphism is, and essentially surjective by construction. -/
theorem isEquivalence_toEssImageBased_of_full_of_faithful
    {𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (i : 𝒴 ⟶ 𝒵)
    (hfull : (CatFiberedInGroupoids.homFunctor i.hom).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i.hom).Faithful) :
    Functor.IsEquivalence (AlgebraicStacks.toEssImageBased i).toFunctor := by
  show Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor i.hom).toEssImage
  have _hfull : (CatFiberedInGroupoids.homFunctor i.hom).Full := hfull
  have _hfaithful : (CatFiberedInGroupoids.homFunctor i.hom).Faithful := hfaithful
  have : (CatFiberedInGroupoids.homFunctor i.hom).toEssImage.Full :=
    Functor.Full.toEssImage _
  have : (CatFiberedInGroupoids.homFunctor i.hom).toEssImage.Faithful :=
    Functor.Faithful.toEssImage _
  have : (CatFiberedInGroupoids.homFunctor i.hom).toEssImage.EssSurj :=
    Functor.EssSurj.toEssImage
  exact Functor.IsEquivalence.mk

/-! ### Existence -/

/-- **Stacks 06MR, the existence assertion, from the presentation proposition.** Let
`HasFullyFaithfulFinitePresentationPresentations` hold and let `𝒵` be an algebraic stack over `S`
which is reduced with a singleton space of points, that is, which satisfies condition (1) of
**Stacks 06MN**. Then some strictly full subcategory of `𝒵` is an algebraic stack satisfying
condition (2) of **Stacks 06MP**.

The subcategory is the essential image of the fully faithful 1-morphism supplied by
`AlgebraicGeometry.Stack.HasFullyFaithfulFinitePresentationPresentations` out of the surjective
flat cover, locally of finite type, by the spectrum of a field that condition (3) of
**Stacks 06MN** supplies
(`AlgebraicGeometry.Stack.tfae_isReducedWithUniquePoint`). It is closed under
isomorphism; the source factors through it by an equivalence of categories, hence by an equivalence
over the big fppf site by **Stacks 003Z**; so it is an algebraic stack by **Stacks 03YQ** and
inherits condition (2) of Stacks 06MP by `AlgebraicGeometry.Stack`
`.hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor`. -/
theorem exists_isReducedLocallyNoetherianUniquePointSubstack
    (hpres : HasFullyFaithfulFinitePresentationPresentations.{u, w} B S hS)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃ P : ObjectProperty 𝒵.val.val.obj,
      IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P := by
  classical
  obtain ⟨F, f, hlft, hsurj, hflat⟩ :=
    hasLocallyOfFiniteTypeFlatFieldSpectrumCover_of_hasFlatFieldSpectrumCover.{u, w} B S hS 𝒵
      (hasFlatFieldSpectrumCover_of_isReducedWithUniquePoint.{u, w} B S hS 𝒵 h𝒵)
  obtain ⟨𝒴, i, hfull, hfaithful, hcov⟩ := hpres 𝒵 F f hlft hsurj hflat
  have hequiv : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased i).toFunctor :=
    isEquivalence_toEssImageBased_of_full_of_faithful B S hS i hfull hfaithful
  obtain ⟨e, he⟩ := exists_basedEquivalence_functor_eq B S hS 𝒴.val
    (AlgebraicStacks.essImageFibered i) (AlgebraicStacks.toEssImageBased i) hequiv
  have hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒵 (CatFiberedInGroupoids.homFunctor i.hom).essImage) :=
    (isAlgebraicStack_iff_of_equivalence B S hS e).mp 𝒴.property
  refine ⟨(CatFiberedInGroupoids.homFunctor i.hom).essImage, inferInstance, hP, ?_⟩
  exact hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor B S hS
    (Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (AlgebraicStacks.toEssImageBased i))) hequiv hcov

/-- **Stacks 06MR, the first assertion, from the presentation proposition.** Let
`HasFullyFaithfulFinitePresentationPresentations` hold and let `𝒵` be an algebraic stack over `S`
which is reduced with a singleton space of points. Then exactly one strictly full subcategory of
`𝒵` is an algebraic stack satisfying condition (2) of **Stacks 06MP**.

Existence is `AlgebraicGeometry.Stack.exists_isReducedLocallyNoetherianUniquePointSubstack` and
uniqueness is `AlgebraicGeometry.Stack.eq_of_isReducedLocallyNoetherianUniquePointSubstack`. -/
theorem existsUnique_isReducedLocallyNoetherianUniquePointSubstack
    (hpres : HasFullyFaithfulFinitePresentationPresentations.{u, w} B S hS)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵) :
    ∃! P : ObjectProperty 𝒵.val.val.obj,
      IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P := by
  obtain ⟨P, hP⟩ :=
    exists_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS hpres 𝒵 h𝒵
  exact ⟨P, hP, fun Q hQ =>
    eq_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 h𝒵 hQ hP⟩

end AlgebraicGeometry.Stack

end
