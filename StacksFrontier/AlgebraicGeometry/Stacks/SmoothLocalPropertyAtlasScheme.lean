module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The two scheme criteria of Stacks 04YF agree, and read the scheme case

Let `P` be a property of schemes local in the smooth topology (**Stacks 0348**) and let `𝒳` be an
algebraic stack over `S`. Two of the four conditions of **Stacks 04YF** are about scheme charts:
that *some* smooth surjective 1-morphism from the algebraic stack of a scheme over `S` has source
with `P`, and that *every* smooth one does. This module proves those two equivalent, and
identifies both with `P` itself when `𝒳` is the algebraic stack of a scheme.

The proof is the source's, with `U' = U` and `V' = V` since the charts are already schemes. Given
an atlas `a : U ⟶ 𝒳` with `P` and a chart `b : V ⟶ 𝒳`, the apex of the canonical 2-fibre-product
square of `(a, b)` (**Stacks 04T2**) is an algebraic stack representable by an algebraic space
(**Stacks 0300**), both of its projections are smooth (**Stacks 075W**), and the projection to `V`
is surjective (**Stacks 04ZU**). A smooth surjective scheme presentation `W ⟶ U ×_𝒳 V` then gives
morphisms of schemes `W ⟶ U`, smooth, and `W ⟶ V`, smooth and surjective, whence
`P(U) ⇒ P(W) ⇒ P(V)` by smooth locality.

## Main results

* `AlgebraicGeometry.Stack.exists_scheme_atlas_iff_forall_scheme`: the two scheme criteria of
  Stacks 04YF agree.
* `AlgebraicGeometry.Stack.exists_scheme_atlas_iff_scheme`: on the algebraic stack of a scheme
  over `S` they are `P` of that scheme.

## Implementation notes

Both results need smoothness of morphisms of algebraic spaces to be smooth local on the
source-and-target — `AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget` at smoothness,
which is **Stacks 06FC** at the smooth case. That is genuinely used: turning smoothness of a
1-morphism of algebraic stacks between two objects representable by algebraic spaces into
smoothness of the induced morphism of those algebraic spaces is the forward half of
**Stacks 06FM**, which is descent along a smooth surjection. It is supplied by
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth`, so both statements are
Stacks 04YF verbatim and carry the tag; the lemmas of
`StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges` take it as the explicit
hypothesis `hsm`, since nothing there is about smoothness in particular.

No composition law for smooth 1-morphisms of algebraic stacks is needed, although the source's
argument composes `W ⟶ U ×_𝒳 V ⟶ U`. Every object in that chain is representable by an algebraic
space, so the two 1-morphisms are read on representing presheaves first and composed there, by
**Stacks 03ZD** and **Stacks 03MG**; that is what
`AlgebraicGeometry.Stack.exists_schemeMap_of_representable` packages. It returns the morphism of
the site together with both of its properties, rather than the properties separately, so that
they are properties of the *same* morphism: the morphism is `yoneda.preimage` of a composite of
two applications of Stacks 04SW, and two separate existentials would not be known to agree.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0348](https://stacks.math.columbia.edu/tag/0348)
* [Stacks Project, Tag 03MG](https://stacks.math.columbia.edu/tag/03MG)
* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading a two-step chain of representable 1-morphisms on schemes -/

/-- A smooth morphism of the representable presheaves of `W` and `U` is `yoneda.map` of a morphism
of the site, smooth, and surjective whenever `p` forces the presheaf morphism to be. -/
private theorem exists_schemeMap_of_yonedaHom {W U : BigFppfOver B S hS} {p : Prop}
    {φ : yoneda.obj W ⟶ yoneda.obj U} (hφ : Space.IsSmooth B S hS φ)
    (hp : p → Space.IsSurjective B S hS φ) :
    ∃ g : W ⟶ U, Smooth ((BigFppfOver.toScheme B S hS).map g) ∧
      (p → Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base) :=
  ⟨yoneda.preimage φ,
    Space.smooth_of_isSmooth_yonedaMap B S hS _ (by rwa [yoneda.map_preimage]),
    fun h => Space.surjective_of_isSurjective_yonedaMap B S hS _
      (by rw [yoneda.map_preimage]; exact hp h)⟩

/-- **A chain `W ⟶ 𝒵 ⟶ U` of 1-morphisms of algebraic stacks whose ends are algebraic stacks of
schemes over `S` and whose middle is representable by an algebraic space is a morphism of the
site**, smooth when both links are and surjective when both links are.

The two links are read on representing presheaves by Stacks 04SW and composed there, which is
Stacks 03ZD for smoothness and Stacks 03MG for surjectivity; the composite is a morphism of
representable presheaves, hence `yoneda.map` of a morphism of the site. Both conclusions are
about that one morphism. -/
theorem exists_schemeMap_of_representable
    (hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsSmooth B S hS k))
    {W U : BigFppfOver B S hS} {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵.val)
    (c : schemeStack.{u, w} B S hS W ⟶ 𝒵) (q : 𝒵 ⟶ schemeStack.{u, w} B S hS U)
    (hc : AlgebraicStacks.IsSmooth B S hS c) (hq : AlgebraicStacks.IsSmooth B S hS q) :
    ∃ g : W ⟶ U, Smooth ((BigFppfOver.toScheme B S hS).map g) ∧
      (IsSurjective B S hS c → IsSurjective B S hS q →
        Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base) := by
  obtain ⟨R, hR, ⟨eR⟩⟩ := h𝒵
  have hm := isSmooth_representingMap_of_isSmooth B S hS hsm (yoneda.obj W) R
    (isAlgebraicSpace_yoneda B S hS W) hR
    (PresheafOfCategories.sliceElementsEquivalenceOver W) eR c hc
  have hn := isSmooth_representingMap_of_isSmooth B S hS hsm R (yoneda.obj U) hR
    (isAlgebraicSpace_yoneda B S hS U) eR
    (PresheafOfCategories.sliceElementsEquivalenceOver U) q hq
  have hcomp := Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS W) hR
    (isAlgebraicSpace_yoneda B S hS U) _ _ hm hn
  exact (exists_schemeMap_of_yonedaHom B S hS
    (p := IsSurjective B S hS c ∧ IsSurjective B S hS q) hcomp
    fun h => Space.isSurjective_comp B S hS
    (isSurjective_representingMap_of_isSurjective B S hS _ _ _ eR c h.1)
    (isSurjective_representingMap_of_isSurjective B S hS _ _ eR _ q h.2)).imp
    fun _ => And.imp_right fun h hc hq => h ⟨hc, hq⟩

/-- **A 1-morphism between the algebraic stacks of two schemes over `S` is a morphism of the
site**, smooth when it is and surjective when it is. This is Stacks 04SW at the slice
presentations of source and target, with Stacks 06FM reading the two properties on the
representing presheaves. -/
theorem exists_schemeMap_of_schemeStackHom
    (hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsSmooth B S hS k))
    {W U : BigFppfOver B S hS}
    (q : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS U)
    (hq : AlgebraicStacks.IsSmooth B S hS q) :
    ∃ g : W ⟶ U, Smooth ((BigFppfOver.toScheme B S hS).map g) ∧
      (IsSurjective B S hS q →
        Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base) := by
  have hn := isSmooth_representingMap_of_isSmooth B S hS hsm (yoneda.obj W) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) q hq
  exact exists_schemeMap_of_yonedaHom B S hS hn
    (isSurjective_representingMap_of_isSurjective B S hS _ _ _ _ q)

/-! ### The two scheme criteria -/

variable (P : ObjectProperty Scheme.{u})
  [P.IsLocal (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]

/-- **Stacks 04YF, the two scheme criteria.** For a property `P` of schemes local in the smooth
topology, an algebraic stack over `S` admits some smooth surjective 1-morphism from the algebraic
stack of a scheme over `S` with `P` exactly when every smooth 1-morphism from the algebraic stack
of a scheme over `S` has source with `P`. -/
@[stacks 04YF "scheme criteria"]
theorem exists_scheme_atlas_iff_forall_scheme
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasPropertyOnSomeSchemeAtlas B S hS P 𝒳 ↔
      HasPropertyOnEverySchemeChart B S hS P 𝒳 := by
  have hsm := Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  refine ⟨fun ⟨U, a, haSurj, haSmooth, hU⟩ V b hb => ?_, fun h => ?_⟩
  · have hQ : Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS a b) :=
      isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b
    have hbrep : IsRepresentableByAlgebraicSpaces B S hS b.hom.hom :=
      isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) b.hom
    have hrep : IsRepresentableByAlgebraicSpace B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a b).pt.val :=
      isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
        (schemeStack.{u, w} B S hS U).val (schemeStack.{u, w} B S hS V).val
        a.hom.hom b.hom.hom hbrep
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
    obtain ⟨W, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a b).pt
    obtain ⟨g₁, hg₁, -⟩ := exists_schemeMap_of_representable B S hS hsm hrep c
      (twoFibreProductSquareAlgebraicStacks B S hS a b).fst hcSmooth
      (AlgebraicStacks.isSmooth_baseChange B S hS b a
        (twoFibreProductSquareAlgebraicStacks B S hS a b) hQ hb)
    obtain ⟨g₂, hg₂, hg₂Surj⟩ := exists_schemeMap_of_representable B S hS hsm hrep c
      (twoFibreProductSquareAlgebraicStacks B S hS a b).snd hcSmooth
      (AlgebraicStacks.isSmooth_baseChange B S hS a b
        (twoFibreProductSquareAlgebraicStacks B S hS a b).swap
        (Bicategory.isTwoFibreProduct_swap hQ) haSmooth)
    exact prop_of_smooth_surjective P _ hg₂
      (hg₂Surj hcSurj
        (isSurjective_of_isTwoFibreProduct B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS a b) hQ haSurj))
      (prop_of_smooth P _ hg₁ hU)
  · obtain ⟨U, a, haSmooth, haSurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒳
    exact ⟨U, a, haSurj, haSmooth, h U a haSmooth⟩

/-- **Stacks 04YF, the scheme case.** On the algebraic stack of a scheme `U` over `S`, the
existential scheme criterion for a smooth-local property `P` is `P` of the scheme underlying `U`.

One direction is smooth surjective descent along the presentation; the other tests the universal
criterion, which the identity presentation satisfies, at an arbitrary chart. -/
@[stacks 04YF "scheme case"]
theorem exists_scheme_atlas_iff_scheme
    (U : BigFppfOver B S hS) :
    HasPropertyOnSomeSchemeAtlas B S hS P (schemeStack.{u, w} B S hS U) ↔
      P ((BigFppfOver.toScheme B S hS).obj U) := by
  have hsm := Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  refine ⟨fun ⟨V, a, haSurj, haSmooth, hV⟩ => ?_, fun hU =>
    (exists_scheme_atlas_iff_forall_scheme B S hS P _).mpr fun V a ha => ?_⟩
  · obtain ⟨g, hg, hgSurj⟩ := exists_schemeMap_of_schemeStackHom B S hS hsm a haSmooth
    exact prop_of_smooth_surjective P _ hg (hgSurj haSurj) hV
  · obtain ⟨g, hg, -⟩ := exists_schemeMap_of_schemeStackHom B S hS hsm a ha
    exact prop_of_smooth P _ hg hU

/-- **The 1-morphism of algebraic stacks induced by a smooth morphism of the site is smooth.** A
smooth morphism of the site has smooth morphism of representable algebraic spaces (Stacks 03MJ),
so the induced 1-morphism has the relative property of Stacks 03YK at smoothness, and its target
is an algebraic stack, so that relative property is smoothness in the sense of Stacks 075U. -/
theorem isSmooth_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Smooth ((BigFppfOver.toScheme B S hS).map g)) :
    AlgebraicStacks.IsSmooth B S hS (schemeStackMap.{u, w} B S hS g) := by
  have hBC : (spaceProperty B S hS (fun _ _ k => Space.IsSmooth B S hS k)).IsStableUnderBaseChange
      := Space.isSmooth_isStableUnderBaseChange B S hS
  have hLT : (spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS
    (fun _ _ k => Space.IsSmooth B S hS k)
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS V)
    (schemeFibredCategoryMap B S hS g)
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)
    (hasRelativeProperty_schemeFibredCategoryMap B S hS
      (spaceProperty B S hS (fun _ _ k => Space.IsSmooth B S hS k)) g
      ((Space.isSmooth_yoneda_map_iff B S hS g).mpr hg))

end AlgebraicGeometry.Stack

end
