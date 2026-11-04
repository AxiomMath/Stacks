module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.RestrictionCoverings
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBigSiteAlgebraicStack

/-!
# Which algebraic stacks over an enlarged big fppf site come from the smaller one (Stacks 04X3)

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and write
`f` for the morphism of sites that the localized inclusion determines. Stacks 04X3 describes the
rule `𝒳 ↦ f⁻¹𝒳` of Stacks 04X2 and characterizes its essential image: a category `𝒳'` over the
enlarged localized big fppf site is equivalent to `f⁻¹𝒳` for an algebraic stack `𝒳` over the
smaller one exactly when it has a presentation `𝒳' = [U'/R']` with `U'`, `R'` isomorphic to
`f⁻¹U`, `f⁻¹R` for some `U, R` over the smaller site.

The route is the source's. An algebraic stack is the quotient stack of a smooth groupoid in
algebraic spaces (Stacks 04T5), the inverse image of that groupoid is again smooth, and the
inverse image of a quotient stack is the quotient stack of the inverse image (Stacks 04WX).
Conversely, a smooth presentation isomorphic to an inverse image `f⁻¹G` has the quotient stack
of `f⁻¹G` (Stacks 046T), `f⁻¹G` is smooth, and smoothness descends from the enlarged site to
`G`, whose quotient stack is algebraic (Stacks 04TK).

## Main definitions

* `AlgebraicGeometry.Stack.IsPullbackOfAlgebraicStack`: `𝒳'` is equivalent over the enlarged
  localized big fppf site to the inverse image of an algebraic stack over the smaller one.
* `AlgebraicGeometry.Stack.HasChangeBigSitePresentation`: `𝒳'` has a presentation `[U'/R']` by
  a smooth groupoid in algebraic spaces isomorphic to the inverse image `(f⁻¹U, f⁻¹R)` of a
  groupoid in algebraic spaces over the smaller site.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_quotientStack_of_isIso` and
  `AlgebraicGeometry.Stack.isSmooth_of_hom_of_isIso`: a morphism of groupoids in algebraic spaces
  whose maps on objects and arrows are isomorphisms identifies the quotient stacks and transports
  smoothness.
* `AlgebraicGeometry.Stack.hasChangeBigSitePresentation_of_isPullbackOfAlgebraicStack`:
  **Stacks 04X3, the "only if" half of the characterization of the essential image**.
* `AlgebraicGeometry.Stack.isPullbackOfAlgebraicStack_of_hasChangeBigSitePresentation`:
  **Stacks 04X3, the "if" half**.
* `AlgebraicGeometry.Stack.isPullbackOfAlgebraicStack_iff_hasChangeBigSitePresentation`:
  **Stacks 04X3, the characterization of the essential image** as an iff.

## Implementation notes

**Universes.** `AlgebraicGeometry.Stack.AlgebraicStacks` is pinned to
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, while
`AlgebraicGeometry.Stack.pullbackStack` of such an object is a stackification and lands in
`CategoryTheory.BasedCategory.{u + 1, u + 1}`. `IsPullbackOfAlgebraicStack` therefore quantifies
`𝒳` over the objects of `AlgebraicStacks.{u, w} B S hS` and compares `f⁻¹𝒳` with `𝒳'` by an
equivalence over the enlarged site, which `StacksRepresentableCFG.EquivalenceOver` permits between
categories in independent universes. The object of `AlgebraicStacks` over the enlarged site that
`f⁻¹𝒳` determines is its small model `AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`, and
the 2-functor of Stacks 04X3 built on it is
`AlgebraicGeometry.Stack.ChangeOfBigSite.pullbackPseudofunctor`.

**The presentation.** The source asks for a presentation `𝒳' = [U'/R']` with `U'` and `R'`
isomorphic to `f⁻¹U` and `f⁻¹R` for some `U, R` over the smaller site; a presentation is by a
smooth groupoid (Stacks 04T3), and `[U/R]` names a groupoid `(U, R, s, t, c)`.
`HasChangeBigSitePresentation` asks for a smooth groupoid `G'` in algebraic spaces on the enlarged
site with `𝒳' ≃ [G']`, together with a groupoid `G` over the smaller site and a morphism of
groupoids `G' ⟶ f⁻¹G` whose maps on objects and on arrows are isomorphisms `U' ≅ f⁻¹U` and
`R' ≅ f⁻¹R`. Only `G'` is assumed smooth, not `G`: smoothness of `G` is proved, by descending
it from `f⁻¹G` (`AlgebraicGeometry.isSmooth_of_changeBigSiteGroupoid_isSmooth`). The groupoid
`G'` is read over the base `f⁻¹A` of `f⁻¹G`, which is where a morphism to `f⁻¹G` lives; the
quotient stack does not see the base.

## The rest of Stacks 04X3

The "if" half uses Stacks 04TK,
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`, over the smaller site. The
object of the 2-category of Stacks 03YP is the small model of the quotient stack,
`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`.

The first two assertions of Stacks 04X3 — that `𝒳 ↦ f⁻¹𝒳` is a functor of 2-categories and that
it induces equivalences of morphism categories — are
`AlgebraicGeometry.Stack.ChangeOfBigSite.pullbackPseudofunctor` and
`AlgebraicGeometry.Stack.ChangeOfBigSite.isEquivalence_mapFunctor_pullbackPseudofunctor`.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T3](https://stacks.math.columbia.edu/tag/04T3)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
* [Stacks Project, Tag 04X2](https://stacks.math.columbia.edu/tag/04X2)
* [Stacks Project, Tag 04X3](https://stacks.math.columbia.edu/tag/04X3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v t

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- `𝒳'` **is the inverse image of an algebraic stack over the smaller site**: there is an
algebraic stack `𝒳` in the 2-category of Stacks 03YP over `S` for `B` with `f⁻¹𝒳` equivalent to
`𝒳'` over the enlarged localized big fppf site. -/
abbrev IsPullbackOfAlgebraicStack
    (𝒳' : BasedCategory.{v, t} (BigFppfOver B' S (largerContains h hS))) : Prop :=
  ∃ 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS),
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    IsAlgebraicStack.{u, w} B S hS 𝒳.val ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (pullbackStack h S hS 𝒳.val).p 𝒳'.p)

/-- `𝒳'` **has a presentation `[U'/R']` with `U'`, `R'` the inverse images of `U`, `R`**: it is
equivalent, over the enlarged localized big fppf site, to the quotient stack of a smooth groupoid
`G' = (U', R', s', t', c')` in algebraic spaces on the enlarged site which is isomorphic to the
inverse image `(f⁻¹U, f⁻¹R, f⁻¹s, f⁻¹t, f⁻¹c)` of a groupoid in algebraic spaces over the smaller
site. The isomorphism is a morphism of groupoids `G' ⟶ f⁻¹G` whose maps on objects and on arrows
are isomorphisms `U' ≅ f⁻¹U` and `R' ≅ f⁻¹R`. -/
abbrev HasChangeBigSitePresentation
    (𝒳' : BasedCategory.{v, t} (BigFppfOver B' S (largerContains h hS))) : Prop :=
  ∃ (A : AlgebraicSpaces B S hS) (G : GroupoidInAlgebraicSpaces B S hS A)
    (G' : GroupoidInAlgebraicSpaces B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj A))
    (φ : GroupoidInAlgebraicSpaces.Hom G' (changeBigSiteGroupoid B B' h S hS G)),
    IsIso φ.toGroupoidHom.mapObjects ∧ IsIso φ.toGroupoidHom.mapArrows ∧
      GroupoidInAlgebraicSpaces.IsSmooth B' S (largerContains h hS) G' ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver (quotientStack G').p 𝒳'.p)

/-- **A morphism of groupoids in algebraic spaces whose maps on objects and on arrows are
isomorphisms induces an equivalence of quotient stacks over the site.** This is the criterion of
Stacks 046T: the square of the arrow map over the two source–target maps is cartesian, its
horizontal sides being isomorphisms, and the saturation map is surjective, the map on objects
being so. -/
theorem nonempty_equivalenceOver_quotientStack_of_isIso {B₀ : BigFppfSite.{u}} {S₀ : Scheme.{u}}
    {hS₀ : B₀.Contains S₀} {A₀ : AlgebraicSpaces B₀ S₀ hS₀}
    {G₁ G₂ : GroupoidInAlgebraicSpaces B₀ S₀ hS₀ A₀} (φ : GroupoidInAlgebraicSpaces.Hom G₁ G₂)
    (hO : IsIso φ.toGroupoidHom.mapObjects) (hA : IsIso φ.toGroupoidHom.mapArrows) :
    Nonempty
      (StacksRepresentableCFG.EquivalenceOver (quotientStack G₁).p (quotientStack G₂).p) := by
  have hs : φ.toGroupoidHom.mapArrows ≫ G₂.toGroupoidInFunctors.source =
      G₁.toGroupoidInFunctors.source ≫ φ.toGroupoidHom.mapObjects := by
    ext T a
    exact φ.toGroupoidHom.map_source T a
  have ht : φ.toGroupoidHom.mapArrows ≫ G₂.toGroupoidInFunctors.target =
      G₁.toGroupoidInFunctors.target ≫ φ.toGroupoidHom.mapObjects := by
    ext T a
    exact φ.toGroupoidHom.map_target T a
  have hsq : IsPullback φ.toGroupoidHom.mapArrows
      (Limits.prod.lift G₁.toGroupoidInFunctors.source G₁.toGroupoidInFunctors.target)
      (Limits.prod.lift G₂.toGroupoidInFunctors.source G₂.toGroupoidInFunctors.target)
      (Limits.prod.map φ.toGroupoidHom.mapObjects φ.toGroupoidHom.mapObjects) :=
    IsPullback.of_horiz_isIso ⟨Limits.prod.hom_ext (by simp [hs]) (by simp [ht])⟩
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B₀ S₀ hS₀)
      φ.toGroupoidHom.mapObjects := inferInstance
  obtain ⟨E⟩ := (quotientStackMap_isEquivalenceOver_iff φ).2
    ⟨hsq, Space.isLocallySurjective_source_pullback_snd φ hsurj⟩
  exact ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (quotientStackMap φ).w E⟩

/-- **Smoothness of groupoids in algebraic spaces passes along a morphism whose maps on objects
and on arrows are isomorphisms**: the source and target maps of the target groupoid are those of
the source groupoid conjugated by these isomorphisms. -/
theorem isSmooth_of_hom_of_isIso {B₀ : BigFppfSite.{u}} {S₀ : Scheme.{u}}
    {hS₀ : B₀.Contains S₀} {A₀ : AlgebraicSpaces B₀ S₀ hS₀}
    {G₁ G₂ : GroupoidInAlgebraicSpaces B₀ S₀ hS₀ A₀} (φ : GroupoidInAlgebraicSpaces.Hom G₁ G₂)
    (hO : IsIso φ.toGroupoidHom.mapObjects) (hA : IsIso φ.toGroupoidHom.mapArrows)
    (hG : GroupoidInAlgebraicSpaces.IsSmooth B₀ S₀ hS₀ G₁) :
    GroupoidInAlgebraicSpaces.IsSmooth B₀ S₀ hS₀ G₂ := by
  let eA : G₁.arrows.obj ≅ G₂.arrows.obj := @asIso _ _ _ _ φ.toGroupoidHom.mapArrows hA
  let eO : G₁.objects.obj ≅ G₂.objects.obj := @asIso _ _ _ _ φ.toGroupoidHom.mapObjects hO
  have key : ∀ (m₁ : G₁.arrows ⟶ G₁.objects) (m₂ : G₂.arrows ⟶ G₂.objects),
      eA.hom ≫ m₂.hom = m₁.hom ≫ eO.hom →
      Space.IsSmooth B₀ S₀ hS₀ m₁.hom → Space.IsSmooth B₀ S₀ hS₀ m₂.hom := by
    intro m₁ m₂ hm hsm
    rw [(Iso.eq_inv_comp eA).2 hm]
    exact Space.isSmooth_comp B₀ S₀ hS₀ G₂.arrows.property G₁.arrows.property
      G₂.objects.property _ _
      (Space.isSmooth_of_isIso B₀ S₀ hS₀ G₂.arrows.property G₁.arrows.property eA.inv)
      (Space.isSmooth_comp B₀ S₀ hS₀ G₁.arrows.property G₁.objects.property
        G₂.objects.property _ _ hsm
        (Space.isSmooth_of_isIso B₀ S₀ hS₀ G₁.objects.property G₂.objects.property eO.hom))
  exact ⟨key G₁.source G₂.source (by ext T a; exact φ.toGroupoidHom.map_source T a) hG.1,
    key G₁.target G₂.target (by ext T a; exact φ.toGroupoidHom.map_target T a) hG.2⟩

/-- **Stacks 04X3, the "only if" half of the characterization of the essential image.** If `𝒳'`
is equivalent over the enlarged localized big fppf site to the inverse image of an algebraic stack
`𝒳` over the smaller site, then `𝒳'` has a presentation `[U'/R']` with `U'`, `R'` the inverse
images of `U`, `R`.

Stacks 04T5 presents `𝒳` as the quotient stack `[U/R]` of a smooth groupoid, Stacks 04WX
identifies `f⁻¹[U/R]` with `[f⁻¹U / f⁻¹R]`, the inverse image of an equivalence over the
smaller site is an equivalence over the enlarged one, and the inverse image of a smooth groupoid
is smooth. The presentation is the inverse-image groupoid itself, with the identity morphism. -/
@[stacks 04X3 "the characterization of the essential image, 'only if' half: a category over the \
enlarged localized big fppf site equivalent to the inverse image of an algebraic stack over the \
smaller one has a presentation by the inverse image of a smooth groupoid in algebraic spaces over \
the smaller site"]
theorem hasChangeBigSitePresentation_of_isPullbackOfAlgebraicStack
    (𝒳' : BasedCategory.{v, t} (BigFppfOver B' S (largerContains h hS)))
    (h𝒳' : IsPullbackOfAlgebraicStack.{u, w} h S hS 𝒳') :
    HasChangeBigSitePresentation h S hS 𝒳' := by
  obtain ⟨𝒳, halg, ⟨e⟩⟩ := h𝒳'
  have hfib𝒳 : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨_hfib, _hst, _hdiag, V, f, hf, hAtlas⟩ := id halg
  obtain ⟨A, G, hGsm, -, ⟨eSmall⟩⟩ := exists_groupoid_equivalenceOver_quotientStack_of_atlas 𝒳 halg
    (Bicategory.InducedBicategory.mkHom (X := schemeFibredCategory B S hS V) (Y := 𝒳) f) hf
    (fun T y hy F hF hE => (hAtlas T y hy F hF hE).1)
    (fun T y hy F hF hE => (hAtlas T y hy F hF hE).2)
  obtain ⟨E04WX⟩ := nonempty_equivalenceOver_changeBigSiteQuotient h S hS G
  obtain ⟨ePB⟩ :=
    nonempty_equivalenceOver_pullbackStack_of_quotient h S hS (quotientStack G) 𝒳.val eSmall
  exact ⟨A, G, changeBigSiteGroupoid B B' h S hS G,
    GroupoidInAlgebraicSpaces.Hom.id _, inferInstanceAs (IsIso (𝟙 _)),
    inferInstanceAs (IsIso (𝟙 _)), changeBigSiteGroupoid_isSmooth B B' h S hS G hGsm,
    ⟨(E04WX.trans ePB).trans e⟩⟩

/-- **Stacks 04X3, the "if" half of the characterization of the essential image.** If `𝒳'` has a
presentation `[U'/R']` with `U'`, `R'` the inverse images of `U`, `R`, then `𝒳'` is equivalent
over the enlarged localized big fppf site to the inverse image of an algebraic stack over the
smaller site.

The isomorphism `G' ≅ f⁻¹G` identifies the quotient stacks (Stacks 046T) and makes `f⁻¹G` smooth;
smoothness then descends to `G`
(`AlgebraicGeometry.isSmooth_of_changeBigSiteGroupoid_isSmooth`). The quotient stack of `G` is
an algebraic stack by Stacks 04TK; its small model
`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel` is an object of the 2-category of Stacks 03YP
equivalent to it over the site; and Stacks 04WX identifies the inverse image of the quotient stack
with the quotient stack of the inverse image. -/
@[stacks 04X3 "the characterization of the essential image, 'if' half: a category over the \
enlarged localized big fppf site with a presentation by the inverse image of a smooth groupoid in \
algebraic spaces over the smaller site is equivalent to the inverse image of an algebraic stack \
over the smaller site"]
theorem isPullbackOfAlgebraicStack_of_hasChangeBigSitePresentation
    (𝒳' : BasedCategory.{v, t} (BigFppfOver B' S (largerContains h hS)))
    (h𝒳' : HasChangeBigSitePresentation h S hS 𝒳') :
    IsPullbackOfAlgebraicStack.{u, w} h S hS 𝒳' := by
  obtain ⟨A, G, G', φ, hO, hA, hG'sm, ⟨e⟩⟩ := h𝒳'
  have hGsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G :=
    isSmooth_of_changeBigSiteGroupoid_isSmooth B B' h S hS G
      (isSmooth_of_hom_of_isIso φ hO hA hG'sm)
  obtain ⟨eφ⟩ := nonempty_equivalenceOver_quotientStack_of_isIso φ hO hA
  have halgQ : IsAlgebraicStack.{u, w} B S hS (quotientStack G) :=
    isAlgebraicStack_quotientStack_of_isSmooth.{u, w} hGsm
  let 𝒴 := AlgebraicStacks.smallModel B S hS (quotientStack G) halgQ
  have hfib𝒴 : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  obtain ⟨E04WX⟩ := nonempty_equivalenceOver_changeBigSiteQuotient h S hS G
  obtain ⟨ePB⟩ := nonempty_equivalenceOver_pullbackStack_of_quotient h S hS (quotientStack G)
    𝒴.val.val (AlgebraicStacks.smallModelEquivalenceOver B S hS (quotientStack G) halgQ)
  exact ⟨𝒴.val, 𝒴.property, ⟨(ePB.symm.trans E04WX.symm).trans (eφ.symm.trans e)⟩⟩

/-- **Stacks 04X3, the characterization of the essential image.** A category `𝒳'` over the
enlarged localized big fppf site is equivalent to the inverse image `f⁻¹𝒳` of an algebraic stack
`𝒳` over the smaller site if and only if it has a presentation `[U'/R']` with `U'`, `R'` the
inverse images of `U`, `R` for a groupoid `(U, R, s, t, c)` in algebraic spaces over the smaller
site. -/
@[stacks 04X3 "the characterization of the essential image"]
theorem isPullbackOfAlgebraicStack_iff_hasChangeBigSitePresentation
    (𝒳' : BasedCategory.{v, t} (BigFppfOver B' S (largerContains h hS))) :
    IsPullbackOfAlgebraicStack.{u, w} h S hS 𝒳' ↔ HasChangeBigSitePresentation h S hS 𝒳' :=
  ⟨hasChangeBigSitePresentation_of_isPullbackOfAlgebraicStack h S hS 𝒳',
    isPullbackOfAlgebraicStack_of_hasChangeBigSitePresentation h S hS 𝒳'⟩

end AlgebraicGeometry.Stack

end
