module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenaryAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone

/-!
# Pseudo-catenary algebraic stacks (Stacks 0DRU)

A locally Noetherian algebraic stack is *pseudo-catenary* when it admits a smooth surjective
morphism from a scheme whose source is universally catenary. This is the hypothesis under which
the dimension theory of an algebraic stack behaves like that of a scheme.

Two sources of pseudo-catenarity are recorded. An algebraic stack locally of finite type over a
locally Noetherian universally catenary scheme is pseudo-catenary (**Stacks 0DRV**), and the
source of a 1-morphism locally of finite type onto a pseudo-catenary algebraic stack is again
pseudo-catenary (**Stacks 0DRW**). Both rest on the scheme statement that a scheme locally of
finite type over a locally Noetherian universally catenary scheme is universally catenary
(**Stacks 02J9**).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsPseudoCatenary`: the pseudo-catenary condition,
  **Stacks 0DRU** — existence of a universally catenary smooth surjective scheme atlas.

## Main results

* `AlgebraicGeometry.Stack.isUniversallyCatenary_of_isSmooth_schemeStack`: every smooth scheme
  chart of an algebraic stack locally of finite type over a locally Noetherian universally
  catenary scheme has universally catenary source.
* `AlgebraicGeometry.Stack.isPseudoCatenary_of_isLocallyOfFiniteType_over_scheme`:
  **Stacks 0DRV** — an algebraic stack locally of finite type over a locally Noetherian
  universally catenary scheme is pseudo-catenary.
* `AlgebraicGeometry.Stack.isPseudoCatenary_of_isLocallyOfFiniteType`: **Stacks 0DRW** —
  pseudo-catenarity passes to the source of a 1-morphism locally of finite type.
* `AlgebraicGeometry.Space.locallyOfFiniteType_of_isLocallyOfFiniteType_yonedaMap` and
  `AlgebraicGeometry.Stack.exists_schemeMap_locallyOfFiniteType_of_schemeStackHom`: a 1-morphism
  locally of finite type between the algebraic stacks of two schemes over `S` comes from a
  morphism of the site which is locally of finite type.

## Implementation notes

The atlas is an object `U` of the big fppf category over `S`, read as an algebraic stack through
`AlgebraicGeometry.Stack.schemeStack`, so that smoothness and surjectivity of the atlas are the
library's notions `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` (**Stacks 075U**) and
`AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**) for a 1-morphism of algebraic stacks,
rather than a separate notion for scheme atlases.

`AlgebraicGeometry.Scheme.IsUniversallyCatenary` (**Stacks 02J8**) is stated only for a scheme
already known to be locally Noetherian, so the local Noetherianity of the source is carried as
part of the existential rather than as a hypothesis on `𝒳`. The source states the definition for
a locally Noetherian algebraic stack; since local Noetherianity of a stack is tested on a smooth
scheme atlas, the atlas produced here witnesses it, and so the condition as stated entails the
standing hypothesis instead of assuming it. This keeps the definition usable without first
having to exhibit the stack's local Noetherianity separately.

The predicate is an `abbrev`, so a consumer can destructure the atlas directly.

Being locally of finite type over `S` is local finite type of the canonical 1-morphism
`AlgebraicGeometry.Stack.structureMorphism` to the algebraic stack of `S` (**Stacks 050D**),
taken canonically rather than as a hypothesis, so that the composite `U ⟶ 𝒳 ⟶ S` of Stacks 0DRV
is `AlgebraicGeometry.Stack.comp_structureMorphism` and needs no compatibility argument.

Reading such a composite on schemes is **Stacks 06FM** twice: the universal smooth-diagram test
of Stacks 06FS is turned into the existential one, which is then evaluated at the slice
presentations `CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver` of the two
scheme stacks; the resulting morphism of representing algebraic spaces is `yoneda.map` of a
morphism of the site, whose chart condition (**Stacks 03MJ**) at the identity charts is local
finite type of the underlying morphism of schemes. Only the existence of that morphism of the
site is recorded, since its sole use is to carry local Noetherianity (**Stacks 01T6**) and
universal catenarity to the source scheme.

For Stacks 0DRW the stack `𝒴 ×_𝒳 U` is the apex of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` (**Stacks 04T2**). Its projection
to `𝒴` is smooth and surjective and its projection to `U` is locally of finite type; the latter
two use the leg exchange `CategoryTheory.Bicategory.TwoCommSq.swap` (**Stacks 003Q**), the
base-change statements being phrased for the first projection of a square over the reversed
cospan.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 02J8](https://stacks.math.columbia.edu/tag/02J8)
* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
* [Stacks Project, Tag 0DRU](https://stacks.math.columbia.edu/tag/0DRU)
* [Stacks Project, Tag 0DRV](https://stacks.math.columbia.edu/tag/0DRV)
* [Stacks Project, Tag 0DRW](https://stacks.math.columbia.edu/tag/0DRW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local finite type of a morphism of representable algebraic spaces is local finite type of
the morphism of schemes.** The chart condition of Stacks 03MJ, tested at the identity charts of
source and target, is the conclusion. -/
theorem locallyOfFiniteType_of_isLocallyOfFiniteType_yonedaMap {U V : BigFppfOver B S hS}
    (g : U ⟶ V) (hg : IsLocallyOfFiniteType B S hS (yoneda.map g)) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
  hg U V (yoneda.map (𝟙 U)) (yoneda.map (𝟙 V)) g
    ((presheaf_yoneda_map_etale_iff B S hS (𝟙 U)).2
      (by simpa using inferInstanceAs (Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj U)))))
    ((presheaf_yoneda_map_etale_iff B S hS (𝟙 V)).2
      (by simpa using inferInstanceAs (Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj V)))))
    (by simp)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism locally of finite type between the algebraic stacks of two schemes over `S`
comes from a morphism of the site which is locally of finite type.** The universal
smooth-diagram test of Stacks 06FS becomes the existential one by Stacks 06FM, which read at
the slice presentations of source and target is local finite type of a morphism of representing
algebraic spaces of the form `yoneda.map`. -/
theorem exists_schemeMap_locallyOfFiniteType_of_schemeStackHom
    {W U : BigFppfOver B S hS}
    (q : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS U)
    (hq : AlgebraicStacks.IsLocallyOfFiniteType B S hS q) :
    ∃ g : W ⟶ U, LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := by
  have hft := Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS
  have hsome := (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k) hft
    (schemeStack.{u, w} B S hS W).property (schemeStack.{u, w} B S hS U).property q.hom).mp hq
  have hn := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k) hft
    (schemeStack.{u, w} B S hS W).property (schemeStack.{u, w} B S hS U).property
    (yoneda.obj W) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) q.hom).mp hsome
  refine ⟨yoneda.preimage
    (representingMap B S hS (schemeStack.{u, w} B S hS W).val
      (schemeStack.{u, w} B S hS U).val (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) q.hom), ?_⟩
  exact Space.locallyOfFiniteType_of_isLocallyOfFiniteType_yonedaMap B S hS _
    (by rwa [yoneda.map_preimage])

/-- A smooth scheme chart followed by a 1-morphism locally of finite type into a scheme stack
comes from a morphism of the site which is locally of finite type. -/
private theorem exists_schemeMap_locallyOfFiniteType_of_isSmooth_comp
    {W U : BigFppfOver B S hS} {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    (c : schemeStack.{u, w} B S hS W ⟶ 𝒳) (d : 𝒳 ⟶ schemeStack.{u, w} B S hS U)
    (hc : AlgebraicStacks.IsSmooth B S hS c) (hd : AlgebraicStacks.IsLocallyOfFiniteType B S hS d) :
    ∃ g : W ⟶ U, LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
  exists_schemeMap_locallyOfFiniteType_of_schemeStackHom B S hS (c ≫ d)
    (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS c d
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hc)) hd)

/-- **Every smooth scheme chart of an algebraic stack locally of finite type over a locally
Noetherian universally catenary scheme is locally Noetherian and universally catenary.** The
chart `U ⟶ 𝒳` is locally of finite type, hence so is the composite `U ⟶ 𝒳 ⟶ S`, and Stacks 02J9
applies.

Surjectivity of the chart plays no part: only local finite type of the composite is used. -/
theorem isUniversallyCatenary_of_isSmooth_schemeStack [IsLocallyNoetherian S]
    (hcat : Scheme.IsUniversallyCatenary S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳))
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (ha : AlgebraicStacks.IsSmooth B S hS a) :
    ∃ hU : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U),
      @Scheme.IsUniversallyCatenary _ hU := by
  obtain ⟨g, hg⟩ := exists_schemeMap_locallyOfFiniteType_of_isSmooth_comp B S hS a
    (structureMorphism B S hS 𝒳) ha h𝒳
  let : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) :=
    inferInstanceAs (IsLocallyNoetherian S)
  have hU : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map g)
  exact ⟨hU, Scheme.isUniversallyCatenary_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map g) hcat⟩

/-- **Stacks 0DRV.** An algebraic stack locally of finite type over a locally Noetherian
universally catenary scheme `S` is pseudo-catenary.

Any smooth surjective scheme atlas serves as the witness, its source being universally catenary
by `AlgebraicGeometry.Stack.isUniversallyCatenary_of_isSmooth_schemeStack`. -/
@[stacks 0DRV]
theorem isPseudoCatenary_of_isLocallyOfFiniteType_over_scheme [IsLocallyNoetherian S]
    (hcat : Scheme.IsUniversallyCatenary S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳)) :
    AlgebraicStacks.IsPseudoCatenary B S hS 𝒳 := by
  obtain ⟨U, a, haSmooth, haSurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒳
  obtain ⟨hU, hUcat⟩ :=
    isUniversallyCatenary_of_isSmooth_schemeStack B S hS hcat 𝒳 h𝒳 U a haSmooth
  exact ⟨U, a, haSurj, haSmooth, hU, hUcat⟩

/-- **Stacks 0DRW.** The source of a 1-morphism of algebraic stacks over `S` which is locally of
finite type and whose target is pseudo-catenary is pseudo-catenary.

For a universally catenary smooth surjective scheme atlas `U ⟶ 𝒳` and a smooth surjective scheme
atlas `V ⟶ 𝒴 ×_𝒳 U`, the composite `V ⟶ 𝒴 ×_𝒳 U ⟶ 𝒴` is smooth and surjective while
`V ⟶ 𝒴 ×_𝒳 U ⟶ U` is locally of finite type, so `V` is universally catenary by Stacks 02J9. -/
@[stacks 0DRW]
theorem isPseudoCatenary_of_isLocallyOfFiniteType {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒴 ⟶ 𝒳) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒳 : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳) :
    AlgebraicStacks.IsPseudoCatenary B S hS 𝒴 := by
  obtain ⟨U, a, haSurj, haSmooth, hU, haCat⟩ := h𝒳
  set Q : Bicategory.TwoCommSq f a := twoFibreProductSquareAlgebraicStacks B S hS f a
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f a
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a f Q hQ haSmooth
  have hfstSurj : IsSurjective B S hS Q.fst :=
    isSurjective_of_isTwoFibreProduct B S hS Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) haSurj
  have hsndType : AlgebraicStacks.IsLocallyOfFiniteType B S hS Q.snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f a Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hf
  obtain ⟨V, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS Q.pt
  obtain ⟨g, hg⟩ :=
    exists_schemeMap_locallyOfFiniteType_of_isSmooth_comp B S hS c Q.snd hcSmooth hsndType
  have hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map g)
  exact ⟨V, c ≫ Q.fst,
    isSurjective_comp B S hS c Q.fst hcSurj hfstSurj,
    AlgebraicStacks.isSmooth_comp B S hS c Q.fst hcSmooth hfstSmooth,
    hV,
    Scheme.isUniversallyCatenary_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map g) haCat⟩

end AlgebraicGeometry.Stack

end
