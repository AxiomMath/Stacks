module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe

/-!
# A monomorphism onto a point produces the residual gerbe there (Stacks 06MX)

Let `𝒳` be an algebraic stack over `S` and `x ∈ |𝒳|` a point of it. **Stacks 06MX** says that if
`𝒵` is an algebraic stack satisfying the equivalent conditions of **Stacks 06MP** and
`f : 𝒵 ⟶ 𝒳` is a monomorphism whose image on points is exactly `{x}`, then the residual gerbe
`𝒵_x` of `𝒳` at `x` exists and `f` factors as `𝒵 ⟶ 𝒵_x ⟶ 𝒳` with the first 1-morphism an
equivalence.

The source's construction is to take for `𝒵_x` the strictly full subcategory of `𝒳` on the
essential image of the functor underlying `f`. That is what is done here. A monomorphism of
algebraic stacks is fully faithful by **Stacks 05UK**, the implication (1) ⟹ (2) of
**Stacks 04ZZ**, so `𝒵 ⟶ 𝒵_x` is an equivalence of categories; the essential image is closed
under isomorphism and under strongly cartesian pullbacks, so `𝒵_x` is a category fibred in
groupoids over the big fppf site of `S`, and an algebraic stack by **Stacks 03YQ** because `𝒵`
is one; condition (2) of **Stacks 06MP** travels along the equivalence; and by the implication
(2) ⟹ (1) of **Stacks 06MP** the subcategory `𝒵_x` is therefore reduced, locally Noetherian and
has exactly one point, which lies over `x` because the factorization 2-commutes and the image of
`|f|` is `{x}`. Those are precisely the clauses of
`AlgebraicGeometry.Stack.IsResidualGerbeAt`, the specification of **Stacks 06MT**.

## Main results

* `AlgebraicGeometry.Stack.exists_isEquivalence_to_essImage_of_full_of_faithful`: a 1-morphism of
  algebraic stacks over `S` whose underlying functor is full and faithful factors as a
  1-morphism onto the full subcategory cut out by its essential image whose underlying functor
  is an equivalence of categories, followed by the inclusion of that full subcategory.
* `AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isMonomorphism`: **Stacks 06MX**.
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_isMonomorphism`: condition (1) of
  **Stacks 06MT** holds at `x` under the hypotheses of Stacks 06MX.

## Implementation notes

The equivalent conditions of **Stacks 06MP** are read as its condition (2), the existence of a
1-morphism from the algebraic stack of the spectrum of a field which is locally of finite
presentation, surjective and flat. Condition (1) — reduced, locally Noetherian, one point — is
not available as an equivalent hypothesis here. The library proves only (2) ⟹ (1) of
Stacks 06MP, in `AlgebraicGeometry.Stack`
`.isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation`; its (1) ⟹ (2) rests
on fppf descent of flatness, **Stacks 05VY** and **Stacks 06Q0**, which this library does not
carry. Starting from condition (1) would in addition require transporting
`AlgebraicGeometry.Stack.IsReducedStack` and
`AlgebraicGeometry.Stack.IsLocallyNoetherianStack` — both of which are the *existential* scheme
atlas criterion `AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of **Stacks 04YF** —
along an equivalence over the big fppf site, and no such transport is recorded. With condition
(2) as the hypothesis the statement is otherwise unconditional: the three ingredients used are
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`
(**Stacks 05UK**), the essential-image construction of **Stacks 0506** in
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack`, and the transport of condition (2) of
Stacks 06MP in `StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence`, none
of which carries a hypothesis.

What is *not* claimed is the uniqueness of the subcategory. That is **Stacks 06MR**, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack` as
`AlgebraicGeometry.Stack.eq_of_isReducedLocallyNoetherianUniquePointSubstack`, which takes the
representability of the substack inclusions (the implication (2) ⟹ (3) of **Stacks 04Y5**) from
the bootstrap theorem Stacks 04S6 part (3).

Strict fullness of the essential image is the Mathlib instance
`CategoryTheory.Functor.essImage.IsClosedUnderIsomorphisms`, so that clause of
`AlgebraicGeometry.Stack.IsResidualGerbeAt` is discharged by instance search. The unique point of
the subcategory is produced as the image under `𝒵 ⟶ 𝒵_x` of a point of `𝒵` over `x`, which the
hypothesis on the image of `|f|` provides; that it lies over `x` is functoriality of the map on
points of **Stacks 04XG** together with its invariance under a 2-morphism, applied to the
factorization 2-isomorphism `AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBasedSquareIso`.

## References

* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MX](https://stacks.math.columbia.edu/tag/06MX)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The factorization of a fully faithful 1-morphism through its essential image.** A
1-morphism `f` of algebraic stacks over `S` whose underlying functor is full and faithful factors
as a 1-morphism onto the full subcategory of its target cut out by its essential image whose
underlying functor is an equivalence of categories, followed by the inclusion of that full
subcategory.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isEquivalence_to_essImage`
(**Stacks 0506**) with the immersion hypothesis replaced by the full faithfulness it was used to
produce; the factorizing 1-morphism is
`AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBased` and the 2-isomorphism is
`AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBasedSquareIso`. -/
theorem exists_isEquivalence_to_essImage_of_full_of_faithful
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵 ⟶ 𝒳)
    (hfull : (CatFiberedInGroupoids.homFunctor f.hom).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f.hom).Faithful)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor f.hom).essImage)) :
    ∃ g : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳
        (CatFiberedInGroupoids.homFunctor f.hom).essImage hP,
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor g.hom) ∧
        Nonempty (g ≫ fullSubcategoryInclusion 𝒳
          (CatFiberedInGroupoids.homFunctor f.hom).essImage hP ≅ f) :=
  ⟨Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (AlgebraicStacks.toEssImageBased f)),
    isEquivalence_toEssImageBased_of_full_of_faithful B S hS f hfull hfaithful,
    ⟨Bicategory.InducedBicategory.isoMk
      (Bicategory.InducedBicategory.isoMk (AlgebraicStacks.toEssImageBasedSquareIso f))⟩⟩

/-- **A fully faithful 1-morphism onto a point produces the residual gerbe there.** Let `𝒳` be an
algebraic stack over `S`, let `x` be a point of its space of points of **Stacks 04XG**, let `𝒵` be
an algebraic stack over `S` satisfying condition (2) of **Stacks 06MP**, and let `f : 𝒵 ⟶ 𝒳` be a
1-morphism whose underlying functor is full and faithful and whose image on points is exactly
`{x}`. Then some object property of `𝒳` satisfies the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**, and `f` factors through the
inclusion of that full subcategory by a 1-morphism whose underlying functor is an equivalence of
categories.

The object property is the essential image of the functor underlying `f`. The factorization
through the essential image is an equivalence of categories, hence an equivalence over the big
fppf site by **Stacks 003Z**; the full subcategory is therefore an algebraic stack by
**Stacks 03YQ** and inherits condition (2) of Stacks 06MP, which makes it reduced, locally
Noetherian and one-point by the implication (2) ⟹ (1) of Stacks 06MP. Its point lies over `x`
because the factorization 2-commutes and the image of `|f|` is `{x}`. This is the argument of
**Stacks 06MX**, which only uses of its monomorphism that it is fully faithful. -/
theorem exists_isResidualGerbeAt_of_full_of_faithful
    (𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳)
    (hfull : (CatFiberedInGroupoids.homFunctor f.hom).Full)
    (hfaith : (CatFiberedInGroupoids.homFunctor f.hom).Faithful)
    (h𝒵 : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (himg : Set.range (AlgebraicStacks.pointsMap B S hS f) = {x}) :
    ∃ (P : ObjectProperty 𝒳.val.val.obj)
      (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)),
      IsResidualGerbeAt B S hS 𝒳 x P ∧
        ∃ g : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP,
          Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor g.hom) ∧
            Nonempty (g ≫ fullSubcategoryInclusion 𝒳 P hP ≅ f) := by
  classical
  have hequiv : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased f).toFunctor :=
    isEquivalence_toEssImageBased_of_full_of_faithful B S hS f hfull hfaith
  obtain ⟨e, -⟩ := exists_basedEquivalence_functor_eq B S hS 𝒵.val
    (AlgebraicStacks.essImageFibered f) (AlgebraicStacks.toEssImageBased f) hequiv
  have hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor f.hom).essImage) :=
    (isAlgebraicStack_iff_of_equivalence B S hS e).mp 𝒵.property
  obtain ⟨g, hge, ⟨α⟩⟩ :=
    exists_isEquivalence_to_essImage_of_full_of_faithful B S hS f hfull hfaith hP
  have hcov : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS
      (fullSubcategoryAlgebraicStack 𝒳
        (CatFiberedInGroupoids.homFunctor f.hom).essImage hP) :=
    hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor B S hS g hge h𝒵
  obtain ⟨⟨hred, -, hsub⟩, hnoeth⟩ :=
    isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation B S hS
      (fullSubcategoryAlgebraicStack 𝒳
        (CatFiberedInGroupoids.homFunctor f.hom).essImage hP) hcov
  obtain ⟨z₀, hz₀⟩ := himg.ge (Set.mem_singleton x)
  refine ⟨(CatFiberedInGroupoids.homFunctor f.hom).essImage, hP,
    ⟨inferInstance, hP, hred, hnoeth, AlgebraicStacks.pointsMap B S hS g z₀,
      fun z' => hsub.allEq z' _, ?_⟩, g, hge, ⟨α⟩⟩
  have hpm : AlgebraicStacks.pointsMap B S hS
      (g ≫ fullSubcategoryInclusion 𝒳
        (CatFiberedInGroupoids.homFunctor f.hom).essImage hP) =
      AlgebraicStacks.pointsMap B S hS f :=
    AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS α.hom
  rw [AlgebraicStacks.pointsMap_comp] at hpm
  exact (congrFun hpm z₀).trans hz₀

/-- **Stacks 06MX.** Let `𝒳` be an algebraic stack over `S`, let `x` be a point of its space of
points of **Stacks 04XG**, let `𝒵` be an algebraic stack over `S` satisfying condition (2) of
**Stacks 06MP**, and let `f : 𝒵 ⟶ 𝒳` be a monomorphism whose image on points is exactly `{x}`.
Then the residual gerbe of `𝒳` at `x` exists — some object property of `𝒳` satisfies the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT** — and `f` factors
through the inclusion of that full subcategory by a 1-morphism whose underlying functor is an
equivalence of categories.

The object property is the essential image of the functor underlying `f`. The monomorphism `f`
is fully faithful by **Stacks 05UK**, so the factorization through the essential image is an
equivalence of categories, hence an equivalence over the big fppf site by **Stacks 003Z**; the
full subcategory is therefore an algebraic stack by **Stacks 03YQ** and inherits condition (2)
of Stacks 06MP, which makes it reduced, locally Noetherian and one-point by the implication
(2) ⟹ (1) of Stacks 06MP. Its point lies over `x` because the factorization 2-commutes and the
image of `|f|` is `{x}`. -/
@[stacks 06MX "with the equivalent conditions of Stacks 06MP read as its CONDITION (2), \
`Dualizing`-style condition (1) being unavailable here: the library proves only (2) => (1) of \
06MP, its (1) => (2) resting on fppf descent of flatness (05VY, 06Q0) which is not carried, and \
there is no transport of `IsReducedStack`/`IsLocallyNoetherianStack` — both \
`HasPropertyOnSomeSchemeAtlas` — along an equivalence over the site. Otherwise unconditional. \
The uniqueness of the subcategory is NOT claimed: that is Stacks 06MR, which carries the \
representability hypothesis of 04Y5 (2) => (3)"]
theorem exists_isResidualGerbeAt_of_isMonomorphism
    (𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f)
    (h𝒵 : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (himg : Set.range (AlgebraicStacks.pointsMap B S hS f) = {x}) :
    ∃ (P : ObjectProperty 𝒳.val.val.obj)
      (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)),
      IsResidualGerbeAt B S hS 𝒳 x P ∧
        ∃ g : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳 P hP,
          Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor g.hom) ∧
            Nonempty (g ≫ fullSubcategoryInclusion 𝒳 P hP ≅ f) := by
  obtain ⟨hfull, hfaith⟩ := full_and_faithful_homFunctor_of_mono_representingMaps B S hS f.hom
    hf.1 fun U z hz H hH he => (Space.mono_hom_iff_mono B S hS _).2 (hf.2 U z hz H hH he)
  exact exists_isResidualGerbeAt_of_full_of_faithful B S hS 𝒳 𝒵 f hfull hfaith h𝒵 x himg

/-- **Condition (1) of Stacks 06MT under the hypotheses of Stacks 06MX.** A monomorphism to `𝒳`
from an algebraic stack satisfying condition (2) of **Stacks 06MP** whose image on points is
exactly `{x}` is a monomorphism from a one-point algebraic stack lying over `x`.

The source of the monomorphism has exactly one point by the implication (2) ⟹ (1) of
Stacks 06MP, and the hypothesis on the image of the map on points puts it over `x`. -/
theorem hasSingletonPointMonomorphism_of_isMonomorphism
    (𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f)
    (h𝒵 : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (himg : Set.range (AlgebraicStacks.pointsMap B S hS f) = {x}) :
    HasSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨⟨-, -, hsub⟩, -⟩ :=
    isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation B S hS 𝒵 h𝒵
  obtain ⟨z₀, hz₀⟩ := himg.ge (Set.mem_singleton x)
  exact ⟨𝒵, f, hf, z₀, fun z' => hsub.allEq z' z₀, hz₀⟩

end AlgebraicGeometry.Stack

end
