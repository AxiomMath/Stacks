module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The common refinement of two smooth charts of an algebraic stack

Let `𝒳` be an algebraic stack over `S` and let `f : U ⟶ 𝒳` and `f' : U' ⟶ 𝒳` be smooth
1-morphisms from schemes of the site. Given *closed* points `u ∈ U` and `u' ∈ U'` with the same
image in `|𝒳|`, this file produces a third scheme `W` of the site which is a smooth chart of `𝒳`
refining both: morphisms `p : W ⟶ U` and `p' : W ⟶ U'` of the site, smooth, with a
2-isomorphism identifying the two composites `W ⟶ 𝒳`, and a *closed* point `w ∈ W` carried to
`u` by `p` and to `u'` by `p'`.

This is the first geometric step of the proof of **Stacks 0DS9** — the reduction, in the source's
words, to "a surjective étale `W ⟶ U ×_𝒳 U'`" and "a closed point `w ∈ W` over both". The
hypothesis that `u` and `u'` have the same image in `|𝒳|` enters in exactly one place: it is what
makes the fibre of `U ×_𝒳 U'` over the pair `(u, u')` nonempty, by **Stacks 04XH**.

## Main results

* `AlgebraicGeometry.Stack.exists_smoothChart_refining_two_smoothCharts`: the refinement, with
  its closed point.

## Implementation notes

The 2-fibre product `U ×_𝒳 U'` is taken in the 2-category of algebraic stacks, as
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`. Its apex is representable by an
algebraic space `P` (**Stacks 04ZP**, through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`), because `𝒳` is
an algebraic stack and the two charts are representable by algebraic spaces; the two projections
become morphisms `pr : P ⟶ h_U` and `pr' : P ⟶ h_{U'}` of algebraic spaces by **Stacks 04SW**,
and they are smooth because they are base changes of `f'` and of `f` (**Stacks 075W**, read off
representing presheaves by `AlgebraicGeometry.Stack.isSmooth_representingMap_of_isSmooth`).

`W` is *not* taken to be a surjective étale atlas of `P`, as the source's wording suggests.
Surjectivity is not what the argument needs — what it needs is one étale scheme chart carrying a
*closed* point above a chosen point of `P`, and that is exactly **Stacks 06EF**
(`AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart`) applied to a finite
type point of `P` over `(u, u')`. Such a finite type point exists because the set of points of
`P` over `(u, u')` is nonempty — this is the one use of the hypothesis on the images, by
Stacks 04XH — and closed, being the intersection of the preimages of the closed singletons
`{u}` and `{u'}` under the continuous maps on points of `pr` and `pr'`; a nonempty locally
closed set of points of an algebraic space contains a finite type point by **Stacks 06EK**
(`AlgebraicGeometry.Space.inter_finiteTypePoints_nonempty`). That is where closedness of `u` and
of `u'` is used, and it is the only place. The fibre argument is isolated as
`AlgebraicGeometry.Stack.exists_isClosed_etaleChart_over_pair`, which knows nothing about
stacks.

The refinement morphisms come out as honest morphisms `p : W ⟶ U` of the site rather than as
abstract 1-morphisms `W ⟶ U` of algebraic stacks: the composite `h_W ⟶ P ⟶ h_U` is a morphism of
*representable* presheaves, so the Yoneda embedding, being fully faithful, returns a morphism of
the site. The 2-isomorphism of the two composites `W ⟶ 𝒳` is then obtained by lifting the étale
chart `h_W ⟶ P` to a 1-morphism `W ⟶ U ×_𝒳 U'` — the surjectivity clause of Stacks 04SW,
`AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq` — identifying each of its two
legs with the 1-morphism of `p` resp. `p'` through the uniqueness clause of the same tag
(`AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq`), and pasting the filler
of the 2-fibre product square between them.

The conclusion carries the 2-isomorphism as data inside the existential rather than as a
`Nonempty`, so that a consumer transporting an invariant along it is not forced through a choice
at every use site.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale scheme chart with a closed point over a prescribed pair of closed points.** Let
`P` be an algebraic space over `S` with two morphisms `pr : P ⟶ X` and `pr' : P ⟶ Y`, let
`x ∈ |X|` and `y ∈ |Y|` be closed points, and suppose some point of `P` lies over both. Then
there are a scheme `W` of the site, an étale morphism `φ : h_W ⟶ P` and a field-valued point `q`
of `h_W` whose underlying point of `W` is closed and whose image in `P` still lies over `x` and
over `y`.

The set of points of `P` over the pair is closed, being the intersection of the preimages of the
closed singletons `{x}` and `{y}` under two continuous maps, and nonempty by hypothesis, so
**Stacks 06EK** finds a finite type point of `P` in it and **Stacks 06EF** exhibits that point as
the image of a closed point of an étale scheme chart. -/
theorem exists_isClosed_etaleChart_over_pair
    {P X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (pr : P ⟶ X) (pr' : P ⟶ Y)
    {x : Space.points B S hS X} {y : Space.points B S hS Y}
    (hx : IsClosed ({x} : Set (Space.points B S hS X)))
    (hy : IsClosed ({y} : Set (Space.points B S hS Y)))
    (z : Space.points B S hS P)
    (hzx : Space.pointsMap B S hS P pr z = x) (hzy : Space.pointsMap B S hS P pr' z = y) :
    ∃ (W : BigFppfOver B S hS) (φ : yoneda.obj W ⟶ P)
      (q : Space.FieldValuedPoint B S hS (yoneda.obj W)),
      Space.IsEtale B S hS φ ∧
        IsClosed ({Space.schemePoint B S hS W q} :
          Set ((BigFppfOver.toScheme B S hS).obj W)) ∧
        Space.pointsMap B S hS P pr
            (Space.pointsMap B S hS (yoneda.obj W) φ (q.class B S hS (yoneda.obj W))) = x ∧
          Space.pointsMap B S hS P pr'
            (Space.pointsMap B S hS (yoneda.obj W) φ (q.class B S hS (yoneda.obj W))) = y := by
  obtain ⟨ρ, ⟨hρx, hρy⟩, hρft⟩ := Space.inter_finiteTypePoints_nonempty B S hS P hP
    (((hx.preimage (Space.continuous_pointsMap B S hS pr)).inter
      (hy.preimage (Space.continuous_pointsMap B S hS pr'))).isLocallyClosed)
    ⟨z, hzx, hzy⟩
  obtain ⟨W, φ, q, hφ, hqclosed, hqρ⟩ :=
    (Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart B S hS P hP ρ).1 hρft
  exact ⟨W, φ, q, hφ, hqclosed, by rw [hqρ]; exact hρx, by rw [hqρ]; exact hρy⟩

/-- **A morphism of the site whose morphism of representable presheaves is smooth induces a
smooth 1-morphism of algebraic stacks.** This is the criterion
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented` read backwards at
smoothness, with the representing presheaves being the representable ones and the induced
morphism being `yoneda.map` by `AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`
(Stacks 04SW). -/
theorem isSmooth_schemeAlgebraicStackMap {W V : BigFppfOver B S hS} (p : W ⟶ V)
    (hp : Space.IsSmooth B S hS (yoneda.map p)) :
    AlgebraicStacks.IsSmooth B S hS (schemeAlgebraicStackMap.{u, w} B S hS p) := by
  refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ k => Space.IsSmooth B S hS k)
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS W)
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS V)
    (yoneda.obj W) (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS V)
    (representedChart B S hS W) (representedChart B S hS V)
    (schemeFibredCategoryMap B S hS p)).mpr ?_
  exact Eq.mpr (congrArg (fun t => Space.IsSmooth B S hS t)
    (representingMap_schemeFibredCategoryMap B S hS p)) hp

/-- **A point of a represented 1-morphism's target, computed on representing presheaves.** Let
`g : 𝒴 ⟶ V` be a 1-morphism of algebraic stacks into a scheme of the site, with `𝒴` represented
by a presheaf `P`. A point `z` of `P` whose image in `|𝒴|` is carried by `g` to the chart point
of `v ∈ V` is carried by the morphism of representing presheaves of Stacks 04SW to `v`.

This is naturality of the chart on points
(`AlgebraicGeometry.Stack.spacePointMap_representing_naturality`), the chart being bijective. -/
theorem pointsMap_representingMap_eq_of_pointsMap_eq
    {𝒴 : AlgebraicStacks.{u, w} B S hS} {V : BigFppfOver B S hS}
    (g : 𝒴 ⟶ schemeStack.{u, w} B S hS V)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eP : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (z : Space.points B S hS P) (v : Space.points B S hS (yoneda.obj V))
    (hz : pointsMap B S hS 𝒴.val.val 𝒴.val.property
        (schemeFibredCategory B S hS V).property g.hom.hom
        (spacePointMap B S hS P 𝒴.val (representingEquivalence B S hS P 𝒴.val eP).functor z) =
      representedChartPointMap B S hS V v) :
    Space.pointsMap B S hS P
        (representingMap B S hS 𝒴.val (schemeStack.{u, w} B S hS V).val P (yoneda.obj V) eP
          (representedChart B S hS V) g.hom) z = v := by
  refine (bijective_spacePointMap_representing B S hS (yoneda.obj V)
    (schemeFibredCategory B S hS V) (representedChart B S hS V)).injective ?_
  refine Eq.trans ?_ hz
  exact spacePointMap_representing_naturality B S hS P (yoneda.obj V) 𝒴.val
    (schemeFibredCategory B S hS V) eP (representedChart B S hS V) g.hom z

/-- **A 1-morphism into a represented algebraic stack, composed with a leg landing in a scheme,
is 2-isomorphic to the 1-morphism of a morphism of the site.** If the morphism of representing
presheaves of Stacks 04SW attached to `h : W ⟶ 𝒴` followed by the one attached to
`g : 𝒴 ⟶ V` is `yoneda.map p`, then `h ≫ g` is 2-isomorphic to the 1-morphism of `p`.

Functoriality of Stacks 04SW (`AlgebraicGeometry.Stack.representingMap_comp`) makes the morphism
of representing presheaves attached to `h ≫ g` equal to the one attached to the 1-morphism of
`p`, and the uniqueness clause of Stacks 04SW
(`AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq`) turns that equality into
a 2-isomorphism. -/
theorem nonempty_twoIso_comp_schemeAlgebraicStackMap
    {𝒴 : AlgebraicStacks.{u, w} B S hS} {W V : BigFppfOver B S hS}
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eP : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (h : schemeStack.{u, w} B S hS W ⟶ 𝒴) (g : 𝒴 ⟶ schemeStack.{u, w} B S hS V) (p : W ⟶ V)
    (hpg : representingMap B S hS (schemeFibredCategory B S hS W) 𝒴.val (yoneda.obj W) P
          (representedChart B S hS W) eP h.hom ≫
        representingMap B S hS 𝒴.val (schemeFibredCategory B S hS V) P (yoneda.obj V) eP
          (representedChart B S hS V) g.hom = yoneda.map p) :
    Nonempty (h ≫ g ≅ schemeAlgebraicStackMap.{u, w} B S hS p) := by
  have key : representingMap B S hS (schemeFibredCategory B S hS W)
        (schemeFibredCategory B S hS V) (yoneda.obj W) (yoneda.obj V)
        (representedChart B S hS W) (representedChart B S hS V) (h ≫ g).hom =
      representingMap B S hS (schemeFibredCategory B S hS W)
        (schemeFibredCategory B S hS V) (yoneda.obj W) (yoneda.obj V)
        (representedChart B S hS W) (representedChart B S hS V)
        (schemeAlgebraicStackMap.{u, w} B S hS p).hom := by
    refine Eq.trans ?_ (representingMap_schemeFibredCategoryMap B S hS p).symm
    refine Eq.trans ?_ hpg
    exact representingMap_comp B S hS (yoneda.obj W) P (yoneda.obj V)
      (representedChart B S hS W) eP (representedChart B S hS V) h.hom g.hom
  obtain ⟨hUniq⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    (schemeFibredCategory B S hS W) (schemeFibredCategory B S hS V)
    (yoneda.obj W) (yoneda.obj V) (representedChart B S hS W) (representedChart B S hS V) key
  exact ⟨Bicategory.InducedBicategory.isoMk hUniq.default⟩

/-- **The 2-fibre product of two scheme charts of an algebraic stack is representable by an
algebraic space.** This is **Stacks 04ZP**: a 1-morphism from a category representable by an
algebraic space into an algebraic stack is representable by algebraic spaces, so the first
projection of the 2-fibre product is, and its source is therefore representable by an algebraic
space. -/
theorem isRepresentableByAlgebraicSpace_twoFibreProductSquareAlgebraicStacks_pt
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (f' : schemeStack.{u, w} B S hS U' ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f').pt.val :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    (schemeStack.{u, w} B S hS U').val 𝒳.val (schemeStack.{u, w} B S hS U).val
    f'.hom f.hom (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom f'.hom)
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U', ⟨representedChart B S hS U'⟩⟩ f'.hom)
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, ⟨representedChart B S hS U⟩⟩

/-- **The first projection of the 2-fibre product of two scheme charts is smooth**, read as a
morphism of algebraic spaces. It is a base change of `f'` (**Stacks 075W**), and
`AlgebraicGeometry.Stack.isSmooth_representingMap_of_isSmooth` reads that off on representing
presheaves (**Stacks 06FM**). -/
theorem isSmooth_representingMap_twoFibreProductFst
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {f' : schemeStack.{u, w} B S hS U' ⟶ 𝒳}
    (hf' : AlgebraicStacks.IsSmooth B S hS f')
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS f f').pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    Space.IsSmooth B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS f f').pt.val
        (schemeFibredCategory B S hS U) P (yoneda.obj U) eP (representedChart B S hS U)
        (twoFibreProductSquareAlgebraicStacks B S hS f f').fst.hom) :=
  isSmooth_representingMap_of_isSmooth.{u, w}
    (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS f f').pt)
    (𝒴 := schemeStack.{u, w} B S hS U) B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P (yoneda.obj U) hP
    (isAlgebraicSpace_yoneda B S hS U) eP (representedChart B S hS U)
    (twoFibreProductSquareAlgebraicStacks B S hS f f').fst
    (AlgebraicStacks.isSmooth_baseChange B S hS f' f
      (twoFibreProductSquareAlgebraicStacks B S hS f f')
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f f') hf')

/-- **The second projection of the 2-fibre product of two scheme charts is smooth**, read as a
morphism of algebraic spaces: the same argument as
`AlgebraicGeometry.Stack.isSmooth_representingMap_twoFibreProductFst` applied to the swapped
square, where the second projection is the first. -/
theorem isSmooth_representingMap_twoFibreProductSnd
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {f' : schemeStack.{u, w} B S hS U' ⟶ 𝒳}
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS f f').pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    Space.IsSmooth B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS f f').pt.val
        (schemeFibredCategory B S hS U') P (yoneda.obj U') eP (representedChart B S hS U')
        (twoFibreProductSquareAlgebraicStacks B S hS f f').snd.hom) :=
  isSmooth_representingMap_of_isSmooth.{u, w}
    (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS f f').pt)
    (𝒴 := schemeStack.{u, w} B S hS U') B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P (yoneda.obj U') hP
    (isAlgebraicSpace_yoneda B S hS U') eP (representedChart B S hS U')
    (twoFibreProductSquareAlgebraicStacks B S hS f f').snd
    (AlgebraicStacks.isSmooth_baseChange B S hS f f'
      (twoFibreProductSquareAlgebraicStacks B S hS f f').swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f f')) hf)

/-- The stack-free half of
`AlgebraicGeometry.Stack.exists_smoothChart_refining_two_smoothCharts`: with the 2-fibre product
already presented by an algebraic space `P` whose two projections `pr`, `pr'` are smooth, and
with a point `z` of `P` over the pair `(u, u')` already in hand, the refinement is produced.

Nothing here uses that `Q` is a *2-fibre* product; only its filler `Q.iso` is used, to paste the
two comparisons into the 2-isomorphism of the two composites. -/
private theorem exists_smoothChart_refining_aux
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {f' : schemeStack.{u, w} B S hS U' ⟶ 𝒳}
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (Q : Bicategory.TwoCommSq f f')
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    {pr : P ⟶ yoneda.obj U} {pr' : P ⟶ yoneda.obj U'}
    (hpr : representingMap B S hS Q.pt.val (schemeFibredCategory B S hS U) P (yoneda.obj U) eP
      (representedChart B S hS U) Q.fst.hom = pr)
    (hpr' : representingMap B S hS Q.pt.val (schemeFibredCategory B S hS U') P (yoneda.obj U')
      eP (representedChart B S hS U') Q.snd.hom = pr')
    (hprsm : Space.IsSmooth B S hS pr) (hpr'sm : Space.IsSmooth B S hS pr')
    {u : Space.points B S hS (yoneda.obj U)} {u' : Space.points B S hS (yoneda.obj U')}
    (hu : IsClosed ({Space.pointsToScheme B S hS U u} :
      Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hu' : IsClosed ({Space.pointsToScheme B S hS U' u'} :
      Set ((BigFppfOver.toScheme B S hS).obj U')))
    (z : Space.points B S hS P)
    (hzu : Space.pointsMap B S hS P pr z = u) (hzu' : Space.pointsMap B S hS P pr' z = u') :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U) (p' : W ⟶ U')
      (w : Space.points B S hS (yoneda.obj W))
      (_η : schemeAlgebraicStackMap.{u, w} B S hS p ≫ f ≅
        schemeAlgebraicStackMap.{u, w} B S hS p' ≫ f'),
      Space.IsSmooth B S hS (yoneda.map p) ∧
        Space.IsSmooth B S hS (yoneda.map p') ∧
        AlgebraicStacks.IsSmooth B S hS (schemeAlgebraicStackMap.{u, w} B S hS p ≫ f) ∧
        IsClosed ({Space.pointsToScheme B S hS W w} :
          Set ((BigFppfOver.toScheme B S hS).obj W)) ∧
        Space.pointsMap B S hS (yoneda.obj W) (yoneda.map p) w = u ∧
        Space.pointsMap B S hS (yoneda.obj W) (yoneda.map p') w = u' := by
  obtain ⟨W, phi, qpt, hphietale, hqclosed, hqu, hqu'⟩ :=
    exists_isClosed_etaleChart_over_pair B S hS hP pr pr'
      ((Space.isClosed_singleton_iff_isClosed_singleton_pointsToScheme B S hS U u).2 hu)
      ((Space.isClosed_singleton_iff_isClosed_singleton_pointsToScheme B S hS U' u').2 hu')
      z hzu hzu'
  have hWy : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  have hphism : Space.IsSmooth B S hS phi := Space.isSmooth_of_isEtale B S hS hP hphietale
  obtain ⟨hlift, hhlift⟩ := exists_oneMorphism_representingMap_eq
    (𝒳 := schemeStack.{u, w} B S hS W) (𝒴 := Q.pt) B S hS (yoneda.obj W) P
    (representedChart B S hS W) eP phi
  have leg : ∀ {V : BigFppfOver B S hS} (g : Q.pt ⟶ schemeStack.{u, w} B S hS V)
      (r : P ⟶ yoneda.obj V)
      (hr : representingMap B S hS Q.pt.val (schemeFibredCategory B S hS V) P (yoneda.obj V) eP
        (representedChart B S hS V) g.hom = r) (hrsm : Space.IsSmooth B S hS r),
      ∃ (p : W ⟶ V), Nonempty (hlift ≫ g ≅ schemeAlgebraicStackMap.{u, w} B S hS p) ∧
        Space.IsSmooth B S hS (yoneda.map p) ∧ yoneda.map p = phi ≫ r := by
    intro V g r hr hrsm
    obtain ⟨p, hp⟩ : ∃ p : W ⟶ V, yoneda.map p = phi ≫ r :=
      ⟨yoneda.preimage (phi ≫ r), yoneda.map_preimage _⟩
    refine ⟨p, nonempty_twoIso_comp_schemeAlgebraicStackMap (𝒴 := Q.pt) B S hS P eP hlift g p
      (by rw [hhlift, hr]; exact hp.symm), ?_, hp⟩
    rw [hp]
    exact Space.isSmooth_comp B S hS hWy hP (isAlgebraicSpace_yoneda B S hS V) phi r hphism hrsm
  obtain ⟨p, ⟨etaFst⟩, hpsmooth, hp⟩ := leg Q.fst pr hpr hprsm
  obtain ⟨p', ⟨etaSnd⟩, hp'smooth, hp'⟩ := leg Q.snd pr' hpr' hpr'sm
  exact ⟨W, p, p', qpt.class B S hS (yoneda.obj W),
    (Bicategory.whiskerRightIso etaFst.symm f).trans
      ((Bicategory.associator hlift Q.fst f).trans ((Bicategory.whiskerLeftIso hlift Q.iso).trans
        ((Bicategory.associator hlift Q.snd f').symm.trans
          (Bicategory.whiskerRightIso etaSnd f')))),
    hpsmooth, hp'smooth,
    AlgebraicStacks.isSmooth_comp B S hS (schemeAlgebraicStackMap.{u, w} B S hS p) f
      (isSmooth_schemeAlgebraicStackMap B S hS p hpsmooth) hf,
    hqclosed, by rw [hp, Space.pointsMap_comp]; exact hqu,
    by rw [hp', Space.pointsMap_comp]; exact hqu'⟩

/-- **The common refinement of two smooth charts, at a pair of closed points with the same image
in `|𝒳|`.** Let `𝒳` be an algebraic stack over `S`, let `f : U ⟶ 𝒳` and `f' : U' ⟶ 𝒳` be smooth
1-morphisms from schemes of the site, and let `u ∈ U` and `u' ∈ U'` be closed points with the
same image in `|𝒳|`. Then there are a scheme `W` of the site, morphisms `p : W ⟶ U` and
`p' : W ⟶ U'` of the site and a closed point `w ∈ W` such that `p` and `p'` are smooth, the two
composites `W ⟶ 𝒳` are 2-isomorphic and smooth, and `p(w) = u`, `p'(w) = u'`.

This is the reduction step of **Stacks 0DS9**. The hypothesis `hx`, that `u` and `u'` have the
same image in `|𝒳|`, is used exactly once: it makes the fibre of `U ×_𝒳 U'` over `(u, u')`
nonempty, by Stacks 04XH. Closedness of `u` and of `u'` is used exactly once too: it makes that
fibre a closed, hence locally closed, set of points of `U ×_𝒳 U'`, so that Stacks 06EK finds a
finite type point in it and Stacks 06EF turns that into a closed point of an étale scheme
chart. -/
theorem exists_smoothChart_refining_two_smoothCharts
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (U U' : BigFppfOver B S hS)
    (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (f' : schemeStack.{u, w} B S hS U' ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hf' : AlgebraicStacks.IsSmooth B S hS f')
    (u : Space.points B S hS (yoneda.obj U)) (u' : Space.points B S hS (yoneda.obj U'))
    (hu : IsClosed ({Space.pointsToScheme B S hS U u} :
      Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hu' : IsClosed ({Space.pointsToScheme B S hS U' u'} :
      Set ((BigFppfOver.toScheme B S hS).obj U')))
    (hx : pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom
          (representedChartPointMap B S hS U u) =
        pointsMap B S hS (schemeFibredCategory B S hS U').val
          (schemeFibredCategory B S hS U').property 𝒳.val.property f'.hom.hom
          (representedChartPointMap B S hS U' u')) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U) (p' : W ⟶ U')
      (w : Space.points B S hS (yoneda.obj W))
      (_η : schemeAlgebraicStackMap.{u, w} B S hS p ≫ f ≅
        schemeAlgebraicStackMap.{u, w} B S hS p' ≫ f'),
      Space.IsSmooth B S hS (yoneda.map p) ∧
        Space.IsSmooth B S hS (yoneda.map p') ∧
        AlgebraicStacks.IsSmooth B S hS (schemeAlgebraicStackMap.{u, w} B S hS p ≫ f) ∧
        IsClosed ({Space.pointsToScheme B S hS W w} :
          Set ((BigFppfOver.toScheme B S hS).obj W)) ∧
        Space.pointsMap B S hS (yoneda.obj W) (yoneda.map p) w = u ∧
        Space.pointsMap B S hS (yoneda.obj W) (yoneda.map p') w = u' := by
  classical
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    id (isRepresentableByAlgebraicSpace_twoFibreProductSquareAlgebraicStacks_pt B S hS f f')
  obtain ⟨zeta, hzeta, hzeta'⟩ := exists_point_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom f'.hom)
    (representedChartPointMap B S hS U u) (representedChartPointMap B S hS U' u') hx
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS P
    (twoFibreProductSquareAlgebraicStacks B S hS f f').pt.val eP).surjective zeta
  refine exists_smoothChart_refining_aux B S hS hf
    (twoFibreProductSquareAlgebraicStacks B S hS f f') hP eP rfl rfl
    (isSmooth_representingMap_twoFibreProductFst B S hS hf' P hP eP)
    (isSmooth_representingMap_twoFibreProductSnd B S hS hf P hP eP) hu hu' z ?_ ?_
  · exact pointsMap_representingMap_eq_of_pointsMap_eq B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f').fst P eP z u (by rw [hz]; exact hzeta)
  · exact pointsMap_representingMap_eq_of_pointsMap_eq B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f').snd P eP z u' (by rw [hz]; exact hzeta')

end AlgebraicGeometry.Stack
