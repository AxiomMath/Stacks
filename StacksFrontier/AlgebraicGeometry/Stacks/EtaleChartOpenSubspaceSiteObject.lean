module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingOpenSubspaceSpacePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartFamilySizeBound
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteNotionsAgree
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeChartAsAlgebraicSpaceChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented

/-!
# The étale chart of Stacks 06N2, read on a scheme of the site

**Stacks 06N2** shrinks the algebraic space `U` of a flat, locally finitely presented
1-morphism `f : U ⟶ 𝒳` to an open subspace `V ⊆ U` over which `f` is étale. The chart
construction of **Stacks 06N3** cannot use that conclusion as it stands: the family assembly
`AlgebraicGeometry.Stack.exists_etaleChartFamily_of_forall_isFiniteTypePoint` consumes a chart
`c : S_Z ⟶ 𝒳` out of the algebraic stack of an **object of the site** which is *relatively*
étale in the sense of **Stacks 04XB**, while Stacks 06N2 delivers étaleness in the sense of
**Stacks 0CIL** of a 1-morphism out of the algebraic stack of the *presheaf* `V`. This file
crosses that last step.

Nothing here is the passage from an open substack to an open subspace: **that passage is
already proved, in both directions.** An open subspace of `U` becomes an open substack of `S_U`
by `AlgebraicGeometry.Stack.exists_openSubstack_algebraicSpaceStack_of_isOpenImmersion`, and
every open substack of `S_U` arises from an open subspace of `U`, with the same point set, by
`AlgebraicGeometry.Stack.exists_isOpenSubspace_property_eq_essImage` of
`StacksFrontier/AlgebraicGeometry/Stacks/PointsAlgebraicSpaceStack.lean`; the conclusion of
Stacks 06N2 read through the second of those is
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale` of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingOpenSubspace.lean`, with its point-set
clause moved onto the algebraic space in
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι`. That the open
subspace so produced is a scheme of the site, with a monomorphism into the representing chart
and of size at most `2 ^ 2 ^ size U₀`, is
`AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace`. What was missing is the
reading of the *chart* on that scheme of the site, which is what this file supplies.

## The comparison

A scheme `V₀` of the site presents two algebraic stacks: the slice of the site over `V₀`,
`AlgebraicGeometry.Stack.schemeStack`, and the category of elements of a presheaf `F`
isomorphic to `h_{V₀}`, `AlgebraicGeometry.Stack.algebraicSpaceStack`.
`StacksFrontier/AlgebraicGeometry/Stacks/SchemeChartAsAlgebraicSpaceChart.lean` crosses from the
second to the first, which is the direction the chart of **Stacks 06FX** is handed to the
slicing lemma **Stacks 06MD** in. Here the *opposite* direction is needed, because the chart
whose étaleness is known is the one out of `algebraicSpaceStack F` and the chart Stacks 06N3
wants is the one out of `schemeStack V₀`. So the forward 1-morphism of a representing
equivalence is built, mirroring
`AlgebraicGeometry.Stack.equivalenceOverInvMap` of
`StacksFrontier/AlgebraicGeometry/Stacks/SmoothLocalMorphismRepresented.lean`, which is the
backward one; and the equivalence it is taken at is the slice-as-elements equivalence
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver` composed with the one a
presheaf isomorphism `h_{V₀} ≅ F` induces,
`CategoryTheory.PresheafOfCategories.equivalenceOverOfPointwiseEquiv`.

Across that comparison nothing has to be transported by hand. Its underlying functor is an
equivalence of categories outright — it *is* the forward functor of the equivalence over the
site — so relative étaleness of the composite is **Stacks 04XB** invariance under
precomposition with an equivalence,
`AlgebraicGeometry.Stack.isRelativelyEtale_of_isEquivalence_comp`; and no representability
hypothesis on the comparison is needed for that. The étaleness of Stacks 0CIL is turned into
the relative property of Stacks 04XB by the universal étale-smooth diagram test
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_relative` — étaleness being
étale-smooth local on source and target by **Stacks 0CG3** — read at the representability the
chart has because its source is the algebraic stack of an algebraic space
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source`).
The comparison is also surjective on objects in the sense of **Stacks 06D4**, hence on points,
so crossing does not change the image of the chart on `|𝒳|`.

## Main definitions

* `AlgebraicGeometry.Stack.equivalenceOverHomMap`: the 1-morphism from a category fibred in
  groupoids to the category of elements of a presheaf representing it — the forward 1-morphism
  of the representing equivalence, where
  `AlgebraicGeometry.Stack.equivalenceOverInvMap` is the backward one.
* `AlgebraicGeometry.Stack.siteObjectAlgebraicSpaceStackMap`: the comparison
  `S_{V₀} ⟶ S_F` attached to a presheaf isomorphism `h_{V₀} ≅ F`, for `V₀` an object of the
  site and `F` an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_homFunctor_equivalenceOverHomMap` and
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_equivalenceOverHomMap`: the forward
  1-morphism has an equivalence for its underlying functor, and is surjective on objects in the
  sense of **Stacks 06D4** with no field extension.
* `AlgebraicGeometry.Stack.range_pointsMap_siteObjectAlgebraicSpaceStackMap_comp`: crossing
  does not change the image of a chart on points.
* `AlgebraicGeometry.Stack.isRelativelyEtale_siteObjectAlgebraicSpaceStackMap_comp`: a chart of
  `𝒳` by the algebraic space `F` which is étale in the sense of **Stacks 0CIL** is, read on the
  scheme `V₀` of the site, relatively étale in the sense of **Stacks 04XB**.
* `AlgebraicGeometry.Stack.exists_siteObject_isRelativelyEtale_chart_of_mem_range`: **the chart
  of Stacks 06N3 in the shape its family assembly consumes**, from the conclusion of
  Stacks 06N2 on an open subspace of a representable chart together with the point-set clause.
* `AlgebraicGeometry.Stack.exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear`:
  the same, run off the fibre hypothesis of Stacks 06N2 itself, with the point-set clause in
  the form Stacks 06MD states it — a point of an algebraic space representing the fibre.
* `AlgebraicGeometry.Stack`
  `.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_isOpenSubspace_isEtale`: **the
  substantial direction of Stacks 06N3 reduced to the open-subspace chart.** The hypothesis that
  direction still carries,
  `AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`, follows from the conclusion
  of Stacks 06N2 on an open subspace of a scheme of the site monomorphic to the smooth chart,
  together with the point-set clause at the prescribed finite type point. The size bound is read
  off the composite monomorphism into the smooth chart, so passing through the Stacks 06MD slice
  does not iterate the double power.

## What this does not settle

The family assembly also asks that the prescribed finite type point of `|𝒳|` lie in the image
of the chart on points. That is not a consequence of Stacks 06N2, whose point-set conclusion is
about a point of `|U|`, and it is the one hypothesis left in
`AlgebraicGeometry.Stack`
`.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_isOpenSubspace_isEtale` once
everything about open substacks, schemes of the site, coproducts, index types and sizes is
discharged. Producing it is the business of the remaining steps of the Stacks 06N3
assembly: the identification of the fibre of the Stacks 06MD slice, which is proved as
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_fibreOverFieldPoint_zeroLocusOnOpen`,
has to be fed to the fibre hypothesis
`AlgebraicGeometry.Stack.FibreIsUnramifiedNear`, and the closed point of **Stacks 056U** has to
be produced in the form the assembly reads, the library's
`AlgebraicGeometry.Space.dense_setOf_class_finiteSeparable_of_isSmooth` being stated over
`Spec k` itself. No part of **Stacks 06N3** is claimed here, and no `@[stacks]` attribute is
registered: the Stacks 06N2 registration sits on
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale`, which states the source's own
conclusion, and nothing below is a step of Stacks 06N2 — only a reading of its conclusion.

## References

* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The forward 1-morphism of a representing equivalence -/

/-- The 1-morphism from a category `𝒳` fibred in groupoids over the big fppf site of `S` to the
category of elements of a presheaf `F` representing it: the forward 1-morphism of the
representing equivalence, read as a 1-morphism of the 2-category of categories fibred in
groupoids.

`AlgebraicGeometry.Stack.equivalenceOverInvMap` is the backward one. This direction is the one a
chart *out of* `𝒳` has to be crossed along when the chart whose property is known is the one out
of the category of elements. -/
def equivalenceOverHomMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    𝒳 ⟶ fibredCategory B S hS F :=
  (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm ⟨eX.hom.functor, eX.hom.w⟩

/-- **The forward 1-morphism of a representing equivalence has an equivalence of categories for
its underlying functor.** By **Stacks 02XS**, clause (2), that functor is the one the 1-morphism
is built from, which is the forward functor of the underlying equivalence of categories of the
equivalence over the site. -/
theorem isEquivalence_homFunctor_equivalenceOverHomMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (equivalenceOverHomMap B S hS F eX)) :=
  eX.toEquivalence.isEquivalence_functor

/-- **The forward 1-morphism of a representing equivalence is surjective on objects** in the
sense of **Stacks 06D4**, and with no field extension: an object `y` of the category of elements
over a field object `U` is the target of the counit of the equivalence at `y`, whose source lies
over `U` and which lies over the identity of `U`.

This is the mirror of
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_equivalenceOverInvMap`, with the counit in place
of the unit. The membership datum is restated in the `fibredCategory` spelling of the structure
functor before the object's base is substituted: the two spellings are definitionally equal but
not syntactically, so the rewrite does not see the `presheafOfCategories` one. -/
theorem isSurjectiveOnObjects_equivalenceOverHomMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsSurjectiveOnObjects B S hS 𝒳.val.p (fibredCategory B S hS F).val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverHomMap B S hS F eX)) := by
  intro U hU y hy
  refine ⟨U, hU, 𝟙 U, eX.inv.functor.obj y,
    (Functor.congr_obj eX.inv.w y).trans hy, (eX.counitIso.app y).hom, ?_⟩
  have h : (fibredCategory B S hS F).val.p.IsHomLift
      (𝟙 ((fibredCategory B S hS F).val.p.obj y)) (eX.counitIso.app y).hom :=
    eX.isHomLift_counitIso_hom_app y
  rw [hy] at h
  exact h

/-! ### A scheme of the site, compared with an algebraic space it represents -/

/-- **The slice of the site over a scheme `V₀`, compared with the algebraic stack of an
algebraic space `F` isomorphic to `h_{V₀}`.** The forward 1-morphism of the representing
equivalence obtained by composing the slice-as-elements equivalence of `V₀` with the equivalence
the presheaf isomorphism `h_{V₀} ≅ F` induces.

`AlgebraicGeometry.Stack.algebraicSpaceStackOfSchemeStack` is the comparison in the opposite
direction, at `F = h_{V₀}`. -/
noncomputable def siteObjectAlgebraicSpaceStackMap
    {V₀ : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (e : yoneda.obj V₀ ≅ F) :
    schemeStack.{u, w} B S hS V₀ ⟶ algebraicSpaceStack.{u, w} B S hS F hF :=
  Bicategory.InducedBicategory.mkHom
    (equivalenceOverHomMap B S hS F
      ((PresheafOfCategories.sliceElementsEquivalenceOver V₀).trans
        (PresheafOfCategories.equivalenceOverOfPointwiseEquiv
          (PresheafOfCategories.PointwiseEquiv.ofUliftIso
            (Functor.isoWhiskerRight e uliftFunctor.{u, u})))))

/-- **The comparison is surjective on points**, being surjective on objects in the sense of
**Stacks 06D4**. -/
theorem pointsMap_surjective_siteObjectAlgebraicSpaceStackMap
    {V₀ : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (e : yoneda.obj V₀ ≅ F) :
    Function.Surjective (AlgebraicStacks.pointsMap B S hS
      (siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hF e)) :=
  pointsMap_surjective_of_isSurjectiveOnObjects B S hS
    (siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hF e)
    (isSurjectiveOnObjects_equivalenceOverHomMap B S hS F _)

/-- **Crossing does not change the image of a chart on points.** The comparison is surjective on
points, so the image of the composite is the image of the chart out of the algebraic space. In
particular a prescribed point of `|𝒳|` in the image of the chart is still in the image of the
chart read on the scheme of the site. -/
theorem range_pointsMap_siteObjectAlgebraicSpaceStackMap_comp
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {V₀ : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (e : yoneda.obj V₀ ≅ F)
    (q : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) :
    Set.range (AlgebraicStacks.pointsMap B S hS
        (siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hF e ≫ q)) =
      Set.range (AlgebraicStacks.pointsMap B S hS q) := by
  rw [AlgebraicStacks.pointsMap_comp]
  exact (pointsMap_surjective_siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hF e).range_comp _

/-- **A chart by an algebraic space which is étale in the sense of Stacks 0CIL is relatively
étale in the sense of Stacks 04XB when read on a scheme of the site representing that space.**

Two steps. The chart `q : S_F ⟶ 𝒳` is representable by algebraic spaces because its source is
the algebraic stack of an algebraic space, so the universal étale-smooth diagram test of
**Stacks 0CIF** that étaleness of **Stacks 0CIL** asks for agrees with the relative property of
**Stacks 04XB** — étaleness being étale-smooth local on source and target by **Stacks 0CG3** —
and `q` is relatively étale. And relative étaleness is invariant under precomposition with a
1-morphism whose underlying functor is an equivalence of categories, which the comparison's
is. -/
theorem isRelativelyEtale_siteObjectAlgebraicSpaceStackMap_comp
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {V₀ : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (e : yoneda.obj V₀ ≅ F)
    (q : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) (hq : IsEtale B S hS q) :
    IsRelativelyEtale B S hS
      (siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hF e ≫ q).hom := by
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS q.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 F hF q
  have hqrel : IsRelativelyEtale B S hS q.hom :=
    ⟨hqrep, (hasPropertyOnEveryEtaleSmoothDiagram_iff_relative.{u, u, w} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsEtale B S hS g.hom)
      (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) q hqrep).1 hq.2⟩
  exact isRelativelyEtale_of_isEquivalence_comp B S hS
    (siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hF e).hom q.hom
    (isEquivalence_homFunctor_equivalenceOverHomMap B S hS F _) hqrel

/-! ### The chart of Stacks 06N3 off the conclusion of Stacks 06N2 -/

/-- **The étale chart on an open subspace of a representable chart is a chart of the Stacks 06N3
family.** Let `ρ : h_{U₀} ≅ U` present the algebraic space `U` as the functor of points of a
scheme `U₀` of the big fppf site of `S`, let `f : U ⟶ 𝒳` be a 1-morphism, let `V ⊆ U` be an open
subspace in the sense of **Stacks 02YU**, part (2), for which the composite of the 1-morphism of
**Stacks 0458** induced by `V` with `f` is étale, and let `x` be a point of `|𝒳|` in the image of
that composite. Then there are a scheme `Z` of the site and a 1-morphism `Z ⟶ 𝒳` which is
relatively étale in the sense of **Stacks 04XB**, whose image on points contains `x`, and with
`size Z ≤ 2 ^ 2 ^ size U₀`. The morphism `Z ⟶ U₀` of the site realizing the subspace is returned
alongside, with open immersion of schemes underlying it, so that a consumer which reached `U₀`
itself as a subobject of an outer chart can recompute the size bound against *that* chart from
the composite monomorphism rather than iterate the double power.

This is exactly the datum that
`AlgebraicGeometry.Stack.exists_etaleChartFamily_of_forall_isFiniteTypePoint` asks for at one
finite type point, so it reduces the chart construction of **Stacks 06N3** on the unramifiedness
route to the point-set clause alone. The open subspace is a scheme of the site by
`AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace`, which also supplies the
size bound; the étaleness and the image are carried across the comparison by
`AlgebraicGeometry.Stack.isRelativelyEtale_siteObjectAlgebraicSpaceStackMap_comp` and
`AlgebraicGeometry.Stack.range_pointsMap_siteObjectAlgebraicSpaceStackMap_comp`. -/
theorem exists_siteObject_isRelativelyEtale_chart_of_mem_range
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    {U₀ : BigFppfOver B S hS} (ρ : yoneda.obj U₀ ≅ U)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    {V : Subfunctor U} (hV : Space.IsOpenSubspace B S hS V)
    (het : IsEtale B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f))
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f))) :
    ∃ (Z : BigFppfOver B S hS) (z : Z ⟶ U₀) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map z) ∧
        IsRelativelyEtale B S hS c.hom ∧
          x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
            ((BigFppfOver.toScheme B S hS).obj Z).size ≤
              (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
                ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  obtain ⟨V₀, v, ε, hvoi, -, -, hsize⟩ :=
    Space.exists_siteObject_iso_mono_of_isOpenSubspace B S hS ρ hV
  refine ⟨V₀, v, siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hV.1 ε ≫
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f, hvoi,
    isRelativelyEtale_siteObjectAlgebraicSpaceStackMap_comp.{u, w} B S hS hV.1 ε _ het, ?_,
    hsize⟩
  rw [range_pointsMap_siteObjectAlgebraicSpaceStackMap_comp.{u, w} B S hS hV.1 ε]
  exact hx

/-- **The conclusion of Stacks 06N2, read on a scheme of the site.** Let `𝒳` be an algebraic
stack, let `ρ : h_{U₀} ≅ U` present the algebraic space `U` as the functor of points of a scheme
`U₀` of the site, let `f : U ⟶ 𝒳` be flat and locally of finite presentation, let
`Spec k ⟶ 𝒳` be a field-valued point, let `Fsp` be an algebraic space representing the fibre
`F = U ×_𝒳 Spec k` and let `p : Fsp ⟶ U` be the projection read on it. If `F ⟶ Spec k` is
unramified near the point of `|F|` named by `x ∈ |Fsp|`, then there are an open subspace
`V ⊆ U` in the sense of **Stacks 02YU**, part (2), a scheme `V₀` of the site, a morphism
`v : V₀ ⟶ U₀` of the site and an isomorphism `ε : h_{V₀} ≅ V` such that

* the morphism of schemes underlying `v` is an open immersion and `v` is a monomorphism;
* `ε` carries the inclusion of `V` to `v` read through `ρ`;
* `p(x)` lies in the point set of `V`;
* the chart `S_{V₀} ⟶ 𝒳` obtained by crossing the composite of the 1-morphism of **Stacks 0458**
  induced by `V` with `f` along the comparison is relatively étale in the sense of
  **Stacks 04XB**; and
* `size V₀ ≤ 2 ^ 2 ^ size U₀`.

So the open subspace that Stacks 06N2 returns is a scheme of the site, and the étale chart it
carries is a chart by that scheme of the site, of the size the family assembly of
**Stacks 06N3** asks of its summands. The point-set clause is the one Stacks 06MD states, a
point of an algebraic space representing the fibre, so that the two legs of the chart
construction match; it is **not** the clause the family assembly consumes, which asks for a
prescribed point of `|𝒳|` and is the hypothesis of
`AlgebraicGeometry.Stack.exists_siteObject_isRelativelyEtale_chart_of_mem_range` instead.

Nothing is added to `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι`
beyond `AlgebraicGeometry.Space.exists_siteObject_iso_mono_of_isOpenSubspace` and the crossing. -/
theorem exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
    (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
      (presheafOfCategories (Fsp ⋙ typeToCat)).p)
    {U₀ : BigFppfOver B S hS} (ρ : yoneda.obj U₀ ≅ U)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (x : Space.points B S hS Fsp)
    (hx : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor x)) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V)
      (V₀ : BigFppfOver B S hS) (v : V₀ ⟶ U₀) (ε : yoneda.obj V₀ ≅ V.toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
        Mono v ∧ ε.hom ≫ V.ι = yoneda.map v ≫ ρ.hom ∧
          Space.pointsMap B S hS Fsp
              (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) x ∈
            Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
            IsRelativelyEtale B S hS
              (siteObjectAlgebraicSpaceStackMap.{u, w} B S hS hV.1 ε ≫
                algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f).hom ∧
            ((BigFppfOver.toScheme B S hS).obj V₀).size ≤
              (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
                ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  obtain ⟨V, hV, hmem, het⟩ :=
    exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι.{u, w} B S hS 𝒳 U hU k hk toBase f g
      Fsp eF hflat hfp x hx
  obtain ⟨V₀, v, ε, hvoi, hvmono, hve, hsize⟩ :=
    Space.exists_siteObject_iso_mono_of_isOpenSubspace B S hS ρ hV
  exact ⟨V, hV, V₀, v, ε, hvoi, hvmono, hve, hmem,
    isRelativelyEtale_siteObjectAlgebraicSpaceStackMap_comp.{u, w} B S hS hV.1 ε _ het, hsize⟩

/-! ### The substantial direction of Stacks 06N3, reduced to the open-subspace chart -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The substantial direction of Stacks 06N3 reduced to the étale chart on an open subspace.**
Suppose that for every DM algebraic stack `𝒳`, every smooth surjective chart
`a₀ : U₀ ⟶ 𝒳` by a scheme of the site and every finite type point `x` of `|𝒳|` there are

* a scheme `U₀'` of the site and a morphism `m : U₀' ⟶ U₀` of the site which is a monomorphism of
  schemes — in the intended application `U₀'` is the slice of **Stacks 06MD** inside `U₀` and `m`
  is its immersion, by `AlgebraicGeometry.Stack.exists_siteObject_iso_mono_zeroLocusOnOpen`;
* an algebraic space `U` presented by `U₀'` and a 1-morphism `f : U ⟶ 𝒳`; and
* an open subspace `V ⊆ U` in the sense of **Stacks 02YU**, part (2), for which the composite of
  the 1-morphism of **Stacks 0458** induced by `V` with `f` is étale and has `x` in its image on
  points — which is what **Stacks 06N2** returns, in the form
  `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale`.

Then `AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM` holds, which is the
substantial direction of **Stacks 06N3**, registered on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.

So nothing about open substacks, schemes of the site, coproducts, index types or sizes is owed
any more: the whole of the chart construction after Stacks 06N2 is discharged here, and what is
left is the *point-set* clause — that the prescribed finite type point of `|𝒳|` lies in the image
of the shrunk chart. The size bound is read off the composite `Z ⟶ U₀' ⟶ U₀`, an open immersion
followed by a monomorphism, so it is `2 ^ 2 ^ size U₀` and does not degrade by passing through
the slice. -/
theorem existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_isOpenSubspace_isEtale
    (hchart : ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS),
      AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 →
      ∀ (U₀ : BigFppfOver B S hS) (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳),
        AlgebraicStacks.IsSmooth B S hS a₀ → IsSurjective B S hS a₀ →
        ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
          IsFiniteTypePoint.{u, w} B S hS 𝒳 x →
            ∃ (U₀' : BigFppfOver B S hS) (m : U₀' ⟶ U₀)
              (_hm : Mono ((BigFppfOver.toScheme B S hS).map m))
              (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
              (_ρ : yoneda.obj U₀' ≅ U) (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
              (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
              IsEtale B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f) ∧
                x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
                  (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f))) :
    ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ := by
  refine existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart.{u, w} B S hS hZ
    (fun 𝒳 h𝒳 U₀ a₀ ha₀sm ha₀su x hx => ?_)
  obtain ⟨U₀', m, hm, U, hU, ρ, f, V, hV, het, hmem⟩ := hchart 𝒳 h𝒳 U₀ a₀ ha₀sm ha₀su x hx
  obtain ⟨Z, z, c, hzoi, hcet, hcmem, -⟩ :=
    exists_siteObject_isRelativelyEtale_chart_of_mem_range.{u, w} B S hS hU ρ f hV het x hmem
  have : Mono ((BigFppfOver.toScheme B S hS).map m) := hm
  have : Mono ((BigFppfOver.toScheme B S hS).map z) :=
    _root_.AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ hzoi
  have : Mono ((BigFppfOver.toScheme B S hS).map (z ≫ m)) := by
    rw [Functor.map_comp]
    infer_instance
  exact ⟨Z, c, hcet, hcmem,
    size_le_of_mono_double_power ((BigFppfOver.toScheme B S hS).map (z ≫ m))⟩

end AlgebraicGeometry.Stack

end
