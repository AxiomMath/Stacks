module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmoothEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteQuotientUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBigSitePullbackStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# Algebraic and Deligne-Mumford stacks under an enlargement of the big fppf site (Stacks 04X2)

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and write `f`
for the morphism of sites that the localized inclusion determines. Stacks 04X2 says that the
inverse image `f⁻¹𝒳` of an algebraic stack `𝒳` over the localized big fppf site of `S` is again an
algebraic stack (part (3)), and a Deligne-Mumford stack when `𝒳` is (part (4)). Parts (1) and (2)
are in `StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBigSiteRepresentableStack`.

The route is the source's. An algebraic stack is the quotient stack of a smooth groupoid in
algebraic spaces (Stacks 04T5), the inverse image of that groupoid is again a smooth groupoid in
algebraic spaces, the inverse image of its quotient stack is the quotient stack of the inverse
image (Stacks 04WX), and the quotient stack of a smooth groupoid in algebraic spaces is an
algebraic stack (Stacks 04TK). Algebraicity is invariant under equivalence over the site
(Stacks 03YQ), which closes the circle. For part (4) the atlas is étale, so the source map of the
groupoid is étale (Stacks 04XC at étaleness), so is the source map of its inverse image, and the
scheme presentation of the quotient stack built for Stacks 04TK — a scheme atlas of the object
space followed by the canonical projection — is then étale as well (Stacks 04X0 at étaleness).

## Main results

* `AlgebraicGeometry.Stack.exists_groupoid_equivalenceOver_quotientStack_of_atlas`: Stacks 04T5 in
  existential form, recording étaleness of the source map for an étale atlas.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_changeBigSiteQuotient`: Stacks 04WX in the
  bundled form `[f⁻¹U/f⁻¹R] ≃ f⁻¹[U/R]`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_pullbackStack`: **Stacks 04X2, part (3).**
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_pullbackStack`: **Stacks 04X2, part (4).**

## Implementation notes

**The inputs.** Stacks 04TK,
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth`, is applied over the
*enlarged* site, because the groupoid this proof feeds to it is produced inside it. Stacks 04TB,
`AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, over the enlarged site also gives the
representability of the canonical projection `𝒮_{f⁻¹U} ⟶ [f⁻¹U/f⁻¹R]` that the étale presentation
of part (4) is built on.

Stacks 04WX is
`AlgebraicGeometry.Stack.isEquivalenceOver_changeBigSiteQuotientEquivalence`, unconditionally, and
the smoothness and étaleness of the inverse-image groupoid are
`AlgebraicGeometry.changeBigSiteGroupoid_isSmooth` and `AlgebraicGeometry.changeBigSite_isEtale`.

**Universes.** `𝒳` is taken at the universes of
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, which is where Stacks 04T5 lives and
which is the 2-category Stacks 03YP forms the algebraic stacks in. The inverse image is a
stackification, so its morphisms are not small and it is *not* at those universes; algebraicity
and the Deligne-Mumford property are therefore read at the universes `f⁻¹𝒳` lands in, through
`AlgebraicGeometry.Stack.IsAlgebraicStack` and `AlgebraicGeometry.Stack.IsDeligneMumfordStackUniv`,
which allow the total category any universes (on `𝒳` itself the latter is
`AlgebraicGeometry.Stack.IsDeligneMumfordStack`, by
`AlgebraicGeometry.Stack.isDeligneMumfordStackUniv_iff_isDeligneMumfordStack`). The comparison
with the quotient stack of the inverse-image groupoid uses
`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver` and
`AlgebraicGeometry.Stack.isDeligneMumfordStackUniv_of_equivalenceOver`, which are Stacks 03YQ
with the two categories in independent universes.

## References

* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 04X2](https://stacks.math.columbia.edu/tag/04X2)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 04T5 in existential form, for a given atlas.** A surjective smooth atlas
`f : (Sch/V)_fppf ⟶ 𝒳` of an algebraic stack presents `𝒳` as the quotient stack of a smooth
groupoid in algebraic spaces: the scheme `V` and the algebraic space representing the
self-intersection of `f` build the groupoid (Stacks 04T4), part (1) of Stacks 04T5 makes it
smooth and part (2) identifies its quotient stack with `𝒳`. When the atlas is moreover étale, so
is the source map of the groupoid, by Stacks 04XC at étaleness. -/
theorem exists_groupoid_equivalenceOver_quotientStack_of_atlas
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) {V : BigFppfOver B S hS}
    (f : schemeFibredCategory B S hS V ⟶ 𝒳)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) f hf)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) f hf) :
    ∃ (A : AlgebraicSpaces B S hS) (G : GroupoidInAlgebraicSpaces B S hS A),
      GroupoidInAlgebraicSpaces.IsSmooth B S hS G ∧
        (HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.etaleMorphisms B S hS) f hf →
          Space.IsEtale B S hS G.source.hom) ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.p) := by
  classical
  have hfib𝒳 : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  -- condition (3) of Stacks 045G, from the diagonal clause
  have h₃ : IsRepresentableFromSchemes B S hS 𝒳 :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp h𝒳.2.2.1)
  -- the self-intersection of the atlas is representable by an algebraic space
  obtain ⟨RF, hRF, ⟨eR⟩⟩ :=
    (isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).mp h₃ V V
      f.hom f.hom
  let Uspace : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let Rspace : AlgebraicSpaces B S hS := ⟨RF, hRF⟩
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver V
  obtain ⟨eSmall, -⟩ := SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
    (f := f) (U := Uspace) (R := Rspace) eU eR h𝒳 hsmooth hsurj
  refine ⟨_, (SelfIntersection.selfIntersectionPresentation
      (f := f.hom) (U := Uspace) (R := Rspace) eU eR h𝒳).groupoid,
    ⟨SelfIntersection.isSmooth_selfIntersectionPresentation_source
        (F := f) (U := Uspace) (R := Rspace) eU eR hf hsmooth h𝒳,
      SelfIntersection.isSmooth_selfIntersectionPresentation_target
        (F := f) (U := Uspace) (R := Rspace) eU eR hf hsmooth h𝒳⟩,
    fun het => ?_, ⟨eSmall⟩⟩
  -- the source map is the base change of the atlas along itself, after the leg exchange
  exact (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.etaleMorphisms B S hS) f hf).mp het
    (schemeFibredCategory B S hS V) ⟨Uspace.obj, Uspace.property, ⟨eU⟩⟩ f
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f f))
    Rspace.obj Uspace.obj Rspace.property Uspace.property eR eU

/-- **The inverse image of a quotient stack is the quotient stack of the inverse image**, as an
equivalence over the enlarged localized big fppf site in the bundled sense: Stacks 04WX read
through `AlgebraicGeometry.Stack.pullbackStack_quotientStack`. -/
theorem nonempty_equivalenceOver_changeBigSiteQuotient {B B' : BigFppfSite.{u}}
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
      (pullbackStack h S hS (quotientStack G)).p) := by
  obtain ⟨E⟩ := isEquivalenceOver_changeBigSiteQuotientEquivalence B B' h S hS G
  exact ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (changeBigSiteQuotientEquivalenceFunctor_comp B B' h S hS G _) E⟩

/-- An equivalence `[U/R] ≃ 𝒳` induces one from the quotient stack of the inverse-image groupoid
to `f⁻¹𝒳`: Stacks 04WX followed by the congruence of inverse images. -/
private theorem nonempty_equivalenceOver_changeBigSiteQuotient_pullbackStack
    {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
    (hS : B.Contains S) (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    [𝒳.val.p.IsFibered] {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack G).p 𝒳.val.p) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
      (pullbackStack h S hS 𝒳.val).p) := by
  obtain ⟨E04WX⟩ := nonempty_equivalenceOver_changeBigSiteQuotient h S hS G
  obtain ⟨ePB⟩ := nonempty_equivalenceOver_pullbackStack_of_quotient h S hS (quotientStack G)
    𝒳.val e
  exact ⟨E04WX.trans ePB⟩

/-- **Stacks 04X2, part (3).** Let `B` be a big fppf site contained in a larger one `B'`, let `S`
be a scheme of `B` and let `f` be the morphism of sites determined by the localized inclusion.
The inverse image `f⁻¹𝒳` of an algebraic stack `𝒳` over the localized big fppf site of `S` is an
algebraic stack over the enlarged localized big fppf site. -/
@[stacks 04X2 "part (3)"]
theorem isAlgebraicStack_pullbackStack {B B' : BigFppfSite.{u}}
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    IsAlgebraicStack.{u, w} B' S (largerContains h hS) (pullbackStack h S hS 𝒳.val) := by
  classical
  have hfib𝒳 : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨_hfib, _hst, _hdiag, V, f, hf, hAtlas⟩ := id h𝒳
  -- Stacks 04T5: the atlas presents `𝒳` as the quotient stack of a smooth groupoid
  obtain ⟨A, G, hGsm, -, ⟨eSmall⟩⟩ := exists_groupoid_equivalenceOver_quotientStack_of_atlas 𝒳 h𝒳
    (Bicategory.InducedBicategory.mkHom (X := schemeFibredCategory B S hS V) (Y := 𝒳) f) hf
    (fun T y hy F hF hE => (hAtlas T y hy F hF hE).1)
    (fun T y hy F hF hE => (hAtlas T y hy F hF hE).2)
  -- the inverse-image groupoid is smooth, so its quotient stack is algebraic by Stacks 04TK
  have halg := isAlgebraicStack_quotientStack_of_isSmooth.{u, w}
    (changeBigSiteGroupoid_isSmooth B B' h S hS G hGsm)
  -- Stacks 04WX, and the congruence of inverse images
  obtain ⟨e⟩ := nonempty_equivalenceOver_changeBigSiteQuotient_pullbackStack h S hS 𝒳 G eSmall
  exact isAlgebraicStack_of_equivalenceOver B' S (largerContains h hS) e halg

/-- **Stacks 04X2, part (4).** Let `B` be a big fppf site contained in a larger one `B'`, let `S`
be a scheme of `B` and let `f` be the morphism of sites determined by the localized inclusion.
The inverse image `f⁻¹𝒳` of a Deligne-Mumford stack `𝒳` over the localized big fppf site of `S`
is a Deligne-Mumford stack over the enlarged localized big fppf site.
The inverse image is a stackification, whose morphisms are not small, so the conclusion is read
with `AlgebraicGeometry.Stack.IsDeligneMumfordStackUniv`, the definition of Stacks 03YO for a
total category in arbitrary universes.

The source's route: a surjective étale atlas of `𝒳` presents it as the quotient stack `[U/R]` of a
groupoid whose source map is étale (Stacks 04T5, and Stacks 04XC at étaleness), the inverse image
of that groupoid has étale source map, `f⁻¹[U/R] = [f⁻¹U/f⁻¹R]` (Stacks 04WX), and the quotient
stack of a groupoid in algebraic spaces with étale source map is presented étale-ly by a scheme
atlas of its object space followed by the canonical projection (Stacks 04X0 at étaleness). -/
@[stacks 04X2 "part (4)"]
theorem isDeligneMumfordStack_pullbackStack {B B' : BigFppfSite.{u}}
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    IsDeligneMumfordStackUniv.{u, w} B' S (largerContains h hS) (pullbackStack h S hS 𝒳.val) := by
  classical
  have hfib𝒳 : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨halg𝒳, _hfib, V, f, hf, hAtlas⟩ :=
    (isDeligneMumfordStackUniv_iff_isDeligneMumfordStack B S hS 𝒳.val).2 h𝒳
  -- Stacks 04T5 at the étale atlas: the source map of the presenting groupoid is étale
  obtain ⟨A, G, hGsm, hGet, ⟨eSmall⟩⟩ :=
    exists_groupoid_equivalenceOver_quotientStack_of_atlas 𝒳 halg𝒳
      (Bicategory.InducedBicategory.mkHom (X := schemeFibredCategory B S hS V) (Y := 𝒳) f) hf
      (fun T y hy F hF hE => (hAtlas T y hy F hF hE).1)
      (fun T y hy F hF hE => Space.isSmooth_of_isEtale B S hS
        (isAlgebraicSpace_yoneda B S hS _) (hAtlas T y hy F hF hE).2)
  -- the inverse-image groupoid, its quotient stack, and the presentation of its projection
  set G' := changeBigSiteGroupoid B B' h S hS G with hG'
  let Pres := QuotientAtlas.presentation G'
    (representable_quotientStackProjectionHom_of_isomPresheafAlgebraic G'
      fun T x y => isAlgebraicSpace_isomPresheaf B' S (largerContains h hS) _ G' T x y)
  -- a surjective étale scheme atlas of the object space, followed by the projection
  obtain ⟨W, α, hαsurjp, hαetp⟩ := G'.objects.property.exists_atlas
  have hαsurj : Space.IsSurjective B' S (largerContains h hS) α :=
    (Space.surjective_iff_surjective_pointsMap B' S (largerContains h hS) _
      G'.objects.property W α).1 hαsurjp
  have hαet : Space.IsEtale B' S (largerContains h hS) α :=
    (Space.isEtale_iff_presheaf_of_yoneda B' S (largerContains h hS) α).2 hαetp
  have : (Space.etaleMorphisms B' S (largerContains h hS)).IsStableUnderBaseChange :=
    Space.etaleMorphisms_isStableUnderBaseChange B' S (largerContains h hS)
  have : (Space.surjectiveMorphismProperty B' S (largerContains h hS)).IsStableUnderBaseChange :=
    Space.surjectiveMorphismProperty_isStableUnderBaseChange B' S (largerContains h hS)
  have : (Space.surjectiveMorphismProperty B' S (largerContains h hS)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B' S (largerContains h hS)) :=
    Space.surjective_isLocalAtTarget_fppf B' S (largerContains h hS)
  have : (Space.etaleMorphisms B' S (largerContains h hS)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B' S (largerContains h hS)) :=
    Space.etaleMorphisms_isLocalAtTarget_fppf B' S (largerContains h hS)
  have : (Space.surjectiveMorphismProperty B' S (largerContains h hS)).IsStableUnderComposition :=
    Space.surjectiveMorphismProperty_isStableUnderComposition B' S (largerContains h hS)
  have : (Space.etaleMorphisms B' S (largerContains h hS)).IsStableUnderComposition :=
    (Space.etaleMorphisms_isMultiplicative B' S (largerContains h hS)).toIsStableUnderComposition
  have hDMQ : IsDeligneMumfordStackUniv.{u, w} B' S (largerContains h hS) (quotientStack G') :=
    ⟨isAlgebraicStack_quotientStack_of_isSmooth.{u, w}
        (changeBigSiteGroupoid_isSmooth B B' h S hS G hGsm),
      isFiberedInGroupoids_quotientStack G', W, schemePresentationHom α,
      isRepresentableByAlgebraicSpaces_schemePresentationHom α Pres.representable,
      fun T y hy F hF hE => ⟨relativeProperty_schemePresentationHom.{u, u}
          (Space.surjectiveMorphismProperty B' S (largerContains h hS)) Pres α hαsurj
          (QuotientAtlas.isSurjective_source G') T y hy F hF hE,
        relativeProperty_schemePresentationHom.{u, u}
          (Space.etaleMorphisms B' S (largerContains h hS)) Pres α hαet
          (changeBigSite_isEtale B B' h S hS G.source
            (hGet fun T y hy F hF hE => (hAtlas T y hy F hF hE).2)) T y hy F hF hE⟩⟩
  -- Stacks 04WX, the congruence of inverse images, and Stacks 03YQ
  obtain ⟨e⟩ := nonempty_equivalenceOver_changeBigSiteQuotient_pullbackStack h S hS 𝒳 G eSmall
  exact isDeligneMumfordStackUniv_of_equivalenceOver B' S (largerContains h hS) e hDMQ

end AlgebraicGeometry.Stack

end
