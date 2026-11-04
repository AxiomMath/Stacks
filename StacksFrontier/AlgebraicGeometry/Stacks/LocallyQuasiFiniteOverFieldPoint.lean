module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteOverField

/-!
# Local quasi-finiteness over a field-valued point of the base (Stacks 06UC)

Let `S` be a base scheme, let `Spec(k) ⟶ S` be a field-valued point of `S` in the big fppf site,
let `𝒴₀` be an algebraic stack over `S` whose 1-morphism `q : 𝒴₀ ⟶ Spec(k)` is locally
quasi-finite (**Stacks 06PU**), and let `c : W ⟶ 𝒴₀` be a locally quasi-finite 1-morphism out of
the algebraic stack represented by an object `W` of the site. Then the morphism of schemes
`W ⟶ Spec(k)` underlying the composite `c ≫ q` is locally of finite type and locally
quasi-finite.

This is **Stacks 06UC** with the field appearing as a field-valued point of an arbitrary base
rather than as the base scheme itself;
`AlgebraicGeometry.Stack.AlgebraicStacks.locallyQuasiFinite_of_isLocallyQuasiFinite_over_field`
is the same result for a site whose base scheme *is* `Spec(k)`.

## Main results

* `AlgebraicGeometry.Stack.representingMap_representedChart_eq_yoneda_map_siteMap`: the morphism of
  representing presheaves of a 1-morphism of represented algebraic stacks is the Yoneda image of
  the morphism of the site underlying it.
* `AlgebraicGeometry.Stack.eq_of_specializes_of_isLocallyQuasiFinite_pair_fieldPoint`: two
  locally quasi-finite lifts of a specialization which agree after composing with a morphism to
  the spectrum of a field agree.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.eq_of_specializes_of_isLocallyQuasiFinite_fieldPoint`: the specialization relation on the
  points of `W` is trivial.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.locallyQuasiFinite_siteMap_of_isLocallyQuasiFinite_fieldPoint`: **Stacks 06UC** at a
  field-valued point of a general base scheme, with local quasi-finiteness of the chart in the
  sense of **Stacks 04XB**.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.locallyQuasiFinite_of_isLocallyQuasiFinite_over_fieldPoint`: the same with local
  quasi-finiteness of the chart in the sense of **Stacks 06PU**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.discretePointsOfChartOverField`: the same read as
  discreteness of the space of points of the represented algebraic stack of `W`, which is the
  shape in which **Stacks 06UD** consumes it.

## Implementation notes

The proof is the one of **Stacks 06UC** over a field, with the base scheme generalized. Two
points need more than a substitution.

First, there is no structure morphism to `Spec(k)` to appeal to: the morphism of schemes
`W ⟶ Spec(k)` is recovered from the 1-morphism `c ≫ q` of *represented* algebraic stacks by
`AlgebraicGeometry.Stack.siteMap`, and
`AlgebraicGeometry.Stack.representingMap_representedChart_eq_yoneda_map_siteMap` identifies the
morphism of representing presheaves of `c ≫ q` with the Yoneda image of it. That identification
replaces the terminality computation of
`AlgebraicGeometry.Stack.locallyOfFiniteType_structureMap`, which is the same statement for the
terminal object of the site.

Second, `AlgebraicGeometry.eq_of_specialization_of_common_lift_over_field` asks that the two
morphisms `W' ⟶ W` lifting the specialization commute with `W ⟶ Spec(k)`. Over a field that is
automatic from the structure of the slice category; here it is derived from the filler of the
2-fibre product square `W ×_{𝒴₀} W`: the two projections become 2-isomorphic after composing
with `c`, hence after composing with `c ≫ q`, and
`AlgebraicGeometry.Stack.representingMap_congr_twoIso` turns that 2-isomorphism into an equality
of the induced morphisms of representing presheaves, which is the required commutation read
through the Yoneda embedding.

`AlgebraicGeometry.Stack.pointTopology` is a `def` and not an instance: the statements supply
the topologies explicitly, and the proofs make them local instances.

## References

* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
* [Stacks Project, Tag 06UC](https://stacks.math.columbia.edu/tag/06UC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] AlgebraicGeometry.Space.pointTopology
  AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of representing presheaves of a 1-morphism of represented algebraic stacks is
the Yoneda image of the morphism of the site underlying it.** The morphism of representing
presheaves is itself the Yoneda image of some morphism `q` of the site, which by
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap` and the uniqueness clause of
**Stacks 04SW** makes the 1-morphism 2-isomorphic to the one induced by `q`; the morphism of the
site underlying it is therefore `q` itself, by
`AlgebraicGeometry.Stack.siteMap_eq_of_iso` and
`AlgebraicGeometry.Stack.siteMap_schemeStackMap`. -/
theorem representingMap_representedChart_eq_yoneda_map_siteMap {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V) :
    representingMap B S hS (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
        (yoneda.obj U) (yoneda.obj V)
        (representedChart B S hS U) (representedChart B S hS V) c.hom =
      yoneda.map (siteMap B S hS c) := by
  obtain ⟨q, hq⟩ : ∃ q : U ⟶ V, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
        (yoneda.obj U) (yoneda.obj V) (representedChart B S hS U) (representedChart B S hS V)
        c.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
    (yoneda.obj U) (yoneda.obj V) (representedChart B S hS U) (representedChart B S hS V)
    (f := c.hom) (g := schemeFibredCategoryMap B S hS q)
    (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
  have hiso : c ≅ schemeStackMap.{u, w} B S hS q :=
    Bicategory.InducedBicategory.isoMk (f := c) (g := schemeStackMap.{u, w} B S hS q) hu.default
  rw [(siteMap_eq_of_iso B S hS hiso).trans (siteMap_schemeStackMap.{u, w} B S hS q)]
  exact hq.symm

/-- **Two locally quasi-finite lifts of a specialization over a field-valued point agree.** Let
`U` be an object of the site, let `m : U ⟶ Spec(k)` be a morphism of the site to a field-valued
point of `S` whose underlying morphism of schemes is locally of finite type, let `F` be an
algebraic space with two morphisms `s, t : F ⟶ U` which agree after composing with `m` and of
which the second is locally quasi-finite, and let `r` be a point of `F` whose images under `s`
and `t` are `x` and `y`. If `x` specializes to `y` then `x = y`.

An étale atlas of `F` by a scheme `W` lifts `r`, and the two composites `W ⟶ U` are two
morphisms carrying one point of `W` to `x` and to `y`, the second locally quasi-finite, which
agree after composing with `m` because `yoneda` is faithful. This is
`AlgebraicGeometry.eq_of_specialization_of_common_lift_over_field`. -/
theorem eq_of_specializes_of_isLocallyQuasiFinite_pair_fieldPoint
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (U : BigFppfOver B S hS) (m : U ⟶ Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))
    (hm : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (s t : F ⟶ yoneda.obj U)
    (hst : s ≫ yoneda.map m = t ≫ yoneda.map m)
    (ht : Space.IsLocallyQuasiFinite B S hS t)
    (r : Space.points B S hS F)
    (x y : (BigFppfOver.toScheme B S hS).obj U)
    (hx : Space.pointsToScheme B S hS U (Space.pointsMap B S hS F s r) = x)
    (hy : Space.pointsToScheme B S hS U (Space.pointsMap B S hS F t r) = y)
    (hxy : x ⤳ y) :
    x = y := by
  classical
  have _ := hm
  have _ := Space.isMultiplicative_presheaf_etale B S hS
  obtain ⟨W, c, hcsurj, hcetale⟩ := hF.exists_atlas
  obtain ⟨w, hw⟩ := Space.isSurjective_of_presheafSurjective B S hS c hcsurj r
  have hqm := ht W U c (𝟙 _) (yoneda.preimage (c ≫ t)) hcetale
    (MorphismProperty.id_mem _ _) (by rw [yoneda.map_preimage]; simp)
  have hpt : ∀ (g : F ⟶ yoneda.obj U) (z : (BigFppfOver.toScheme B S hS).obj U),
      Space.pointsToScheme B S hS U (Space.pointsMap B S hS F g r) = z →
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ g))
        (Space.pointsToScheme B S hS W w) = z := by
    intro g z hz
    rw [← Space.pointsToScheme_pointsMap, yoneda.map_preimage,
      Space.pointsMap_comp B S hS (yoneda.obj W) c g]
    simp only [Function.comp_apply, hw]
    exact hz
  have hnx := hpt s x hx
  have hmy := hpt t y hy
  have hcomp : (BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ s)) ≫
      (BigFppfOver.toScheme B S hS).map m =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ t)) ≫
        (BigFppfOver.toScheme B S hS).map m := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (BigFppfOver.toScheme B S hS).map (yoneda.map_injective ?_)
    rw [Functor.map_comp, Functor.map_comp, yoneda.map_preimage, yoneda.map_preimage,
      Category.assoc, Category.assoc, hst]
  have _ : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map
    (yoneda.preimage (c ≫ t))) := hqm.2
  have hres := AlgebraicGeometry.eq_of_specialization_of_common_lift_over_field (k := k)
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ s)))
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ t)))
    ((BigFppfOver.toScheme B S hS).map m) hcomp (Space.pointsToScheme B S hS W w)
    (by rw [hnx, hmy]; exact hxy)
  rwa [hnx, hmy] at hres

namespace AlgebraicStacks

/-- **The specialization relation on a scheme mapping locally quasi-finitely to an algebraic
stack with discrete space of points, at a field-valued point of the base, is trivial.**
Discreteness makes the two images in the stack of a specialization coincide, so **Stacks 04XH**
lifts the pair of points to a single point of `W ×_{𝒴₀} W`, whose two projections to `W` are
locally quasi-finite by **Stacks 04XC**.

The filler of the 2-fibre product square makes the two projections 2-isomorphic over `𝒴₀`, hence
over the represented stack of `Spec(k)`, so by
`AlgebraicGeometry.Stack.representingMap_congr_twoIso` the two induced morphisms of representing
presheaves agree after composing with the Yoneda image of `W ⟶ Spec(k)`. That is the commutation
hypothesis of
`AlgebraicGeometry.Stack.eq_of_specializes_of_isLocallyQuasiFinite_pair_fieldPoint`. -/
theorem eq_of_specializes_of_isLocallyQuasiFinite_fieldPoint
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    {𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS} (W : BigFppfOver B S hS)
    (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (c : Stack.schemeStack.{u, w} B S hS W ⟶ 𝒴₀)
    (hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q))))
    (hcrep : Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom)
    (hclqf : Stack.IsLocallyQuasiFinite B S hS c.hom)
    (hX : @DiscreteTopology (Stack.points B S hS 𝒴₀.val.val 𝒴₀.val.property)
      (Stack.pointTopology B S hS 𝒴₀.val))
    (x y : (BigFppfOver.toScheme B S hS).obj W) (hxy : x ⤳ y) :
    x = y := by
  classical
  let _ := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS W)
  let _ := Stack.pointTopology B S hS 𝒴₀.val
  let _ := hX
  have hcont : Continuous (fun z : (BigFppfOver.toScheme B S hS).obj W =>
      Stack.pointsMap B S hS (Stack.schemeStack.{u, w} B S hS W).val.val
        (Stack.schemeStack.{u, w} B S hS W).val.property 𝒴₀.val.property
        c.hom.hom ((Stack.pointsHomeomorphScheme B S hS W).symm z)) :=
    (Stack.continuous_pointsMap B S hS (Stack.schemeStack.{u, w} B S hS W).val 𝒴₀.val
      c.hom.hom).comp (Stack.pointsHomeomorphScheme B S hS W).symm.continuous
  have himg := specializes_iff_eq.mp (hxy.map hcont)
  have hQ := Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS c c)
  obtain ⟨r, hr1, hr2⟩ := Stack.exists_point_of_isTwoFibreProduct B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying hQ
    ((Stack.pointsHomeomorphScheme B S hS W).symm x)
    ((Stack.pointsHomeomorphScheme B S hS W).symm y) himg
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
      B S hS (Stack.schemeStack.{u, w} B S hS W).val 𝒴₀.val
      (Stack.schemeStack.{u, w} B S hS W).val c.hom c.hom
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying hQ hcrep
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  obtain ⟨rF, hrF⟩ := (Stack.bijective_spacePointMap_representing B S hS F
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.pt eF).2 r
  have ht := Stack.prop_representingMap_of_hasRelativeProperty.{u, u + 1} B S hS
    (Space.locallyQuasiFiniteProperty B S hS) c.hom hcrep hclqf
    (Stack.schemeFibredCategory B S hS W) c.hom
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.swap
    (Bicategory.isTwoFibreProduct_swap hQ)
    F (yoneda.obj W) hF (isAlgebraicSpace_yoneda B S hS W) eF
    (Stack.representedChart B S hS W)
  have hrc : ∀ z, Stack.representedChartPointMap B S hS W z =
      Stack.spacePointMap B S hS (yoneda.obj W) (Stack.schemeFibredCategory B S hS W)
        (Stack.representingEquivalence B S hS (yoneda.obj W)
          (Stack.schemeFibredCategory B S hS W) (Stack.representedChart B S hS W)).functor z :=
    fun _ => rfl
  have hid : ∀ (f : (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.pt ⟶
        (Stack.schemeStack.{u, w} B S hS W).val) (z : (BigFppfOver.toScheme B S hS).obj W),
      Stack.pointsMap B S hS _ _ _ f.hom r = (Stack.pointsHomeomorphScheme B S hS W).symm z →
      Space.pointsToScheme B S hS W
        (Space.pointsMap B S hS F
          (Stack.representingMap B S hS
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.pt
            (Stack.schemeFibredCategory B S hS W) F (yoneda.obj W) eF
            (Stack.representedChart B S hS W) f) rF) = z := by
    intro f z hf
    rw [← Stack.pointsHomeomorphScheme_representedChartPointMap B S hS W, hrc,
      Stack.spacePointMap_representing_naturality B S hS F (yoneda.obj W)
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.pt
        (Stack.schemeFibredCategory B S hS W) eF (Stack.representedChart B S hS W) f rF,
      hrF, hf]
    exact (Stack.pointsHomeomorphScheme B S hS W).apply_symm_apply z
  have hiso :
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.fst ≫ (c ≫ q).hom ≅
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.snd ≫ (c ≫ q).hom :=
    (Bicategory.associator
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.fst
        c.hom q.hom).symm ≪≫
      Bicategory.whiskerRightIso
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.iso q.hom ≪≫
      Bicategory.associator
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.snd c.hom q.hom
  have hst :
      Stack.representingMap B S hS
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.pt
          (Stack.schemeFibredCategory B S hS W) F (yoneda.obj W) eF
          (Stack.representedChart B S hS W)
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.fst ≫
        yoneda.map (siteMap B S hS (c ≫ q)) =
      Stack.representingMap B S hS
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.pt
          (Stack.schemeFibredCategory B S hS W) F (yoneda.obj W) eF
          (Stack.representedChart B S hS W)
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS c c).underlying.snd ≫
        yoneda.map (siteMap B S hS (c ≫ q)) := by
    rw [← Stack.representingMap_representedChart_eq_yoneda_map_siteMap B S hS (c ≫ q)]
    simp only [← Stack.representingMap_comp B S hS F (yoneda.obj W)
      (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) eF
      (Stack.representedChart B S hS W)
      (Stack.representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))]
    exact Stack.representingMap_congr_twoIso B S hS F
      (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) eF
      (Stack.representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) hiso
  exact Stack.eq_of_specializes_of_isLocallyQuasiFinite_pair_fieldPoint B S hS k hk toBase W
    (siteMap B S hS (c ≫ q)) hft hF _ _ hst ht rF x y (hid _ x hr1) (hid _ y hr2) hxy

/-- **Stacks 06UC at a field-valued point of a general base scheme.** Let `Spec(k) ⟶ S` be a
field-valued point of the base scheme in the big fppf site, let `q : 𝒴₀ ⟶ Spec(k)` be a locally
quasi-finite 1-morphism of algebraic stacks over `S`, and let `c : W ⟶ 𝒴₀` be a locally
quasi-finite 1-morphism out of the algebraic stack represented by an object `W` of the site.
Then the morphism of schemes underlying `c ≫ q` is locally of finite type and locally
quasi-finite.

Local finite type is
`AlgebraicGeometry.Stack.locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType` applied to the
composite, which is locally of finite type by **Stacks 06FT**. Given that, **Stacks 01TH**
reduces local quasi-finiteness to triviality of the specialization relation on `W`, which is
`eq_of_specializes_of_isLocallyQuasiFinite_fieldPoint`; its inputs are local quasi-finiteness of
`c` in the sense of **Stacks 04XB**, which is the hypothesis here, and discreteness of `|𝒴₀|`,
which is `discreteTopology_points_of_isLocallyQuasiFinite`. -/
theorem locallyQuasiFinite_siteMap_of_isLocallyQuasiFinite_fieldPoint
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    {𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS} (W : BigFppfOver B S hS)
    (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (c : Stack.schemeStack.{u, w} B S hS W ⟶ 𝒴₀)
    (hq : IsLocallyQuasiFinite B S hS q) (hc : Stack.IsLocallyQuasiFinite B S hS c.hom) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q))) ∧
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q))) := by
  classical
  have hcrep : Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴₀.property
      (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) c.hom
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (siteMap B S hS (c ≫ q))) :=
    Stack.locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType B S hS (c ≫ q)
      (isLocallyOfFiniteType_comp B S hS c q
        (Stack.isLocallyOfFiniteType_of_isLocallyQuasiFinite B S hS c hcrep hc) hq.2.1)
  have hX := discreteTopology_points_of_isLocallyQuasiFinite B S hS k hk
    toBase q hq
  have _ := hft
  rw [← AlgebraicGeometry.forall_quasiFiniteAt_iff
    ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q)))]
  exact AlgebraicGeometry.forall_quasiFiniteAt_of_specialization_eq _
    (fun x y hxy => eq_of_specializes_of_isLocallyQuasiFinite_fieldPoint B S hS k hk toBase W
      q c hft hcrep hc hX x y hxy)

/-- **Stacks 06UC at a field-valued point of a general base scheme, for the Stacks 06PU notion
of local quasi-finiteness of the chart.** This is
`locallyQuasiFinite_siteMap_of_isLocallyQuasiFinite_fieldPoint` with local quasi-finiteness of
`c` read in the sense of **Stacks 06PU**, which is what the source's statement uses; it implies
the **Stacks 04XB** notion by **Stacks 06UA**, since `c` is representable by algebraic
spaces. -/
@[stacks 06UC "at a field-valued point of a general base scheme"]
theorem locallyQuasiFinite_of_isLocallyQuasiFinite_over_fieldPoint
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    {𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS} (W : BigFppfOver B S hS)
    (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (c : Stack.schemeStack.{u, w} B S hS W ⟶ 𝒴₀)
    (hq : IsLocallyQuasiFinite B S hS q) (hc : IsLocallyQuasiFinite B S hS c) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q))) ∧
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q))) :=
  locallyQuasiFinite_siteMap_of_isLocallyQuasiFinite_fieldPoint B S hS k hk toBase W q c hq
    (Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology B S hS c
      (Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴₀.property
        (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W) c.hom)
      hc.2.1 hc.2.2)

/-- **The chart of a stack locally quasi-finite over a field-valued point has discrete space of
points.** This is `locallyQuasiFinite_of_isLocallyQuasiFinite_over_fieldPoint` read through
`AlgebraicGeometry.locallyQuasiFinite_iff_discreteTopology_of_subsingleton`: a morphism of
schemes locally of finite type over the spectrum of a field is locally quasi-finite exactly when
its source is discrete, and the space of points of a represented algebraic stack is the
underlying space of its scheme (`AlgebraicGeometry.Stack.pointsHomeomorphScheme`).

Local quasi-finiteness of the chart is taken in the sense of **Stacks 04XB**, which is the shape
in which **Stacks 06UD** supplies it. -/
theorem discretePointsOfChartOverField :
    ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
      (𝒴₀ : Stack.AlgebraicStacks.{u, w} B S hS)
      (q : 𝒴₀ ⟶ Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (W : BigFppfOver B S hS) (c : Stack.schemeStack.{u, w} B S hS W ⟶ 𝒴₀),
      IsLocallyQuasiFinite B S hS q → Stack.IsLocallyQuasiFinite B S hS c.hom →
        @DiscreteTopology
          (Stack.points B S hS (Stack.schemeStack.{u, w} B S hS W).val.val
            (Stack.schemeStack.{u, w} B S hS W).val.property)
          (Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS W).val) := by
  classical
  intro k _ hk toBase 𝒴₀ q W c hq hc
  let : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  let := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS W).val
  obtain ⟨hft, hlqf⟩ := locallyQuasiFinite_siteMap_of_isLocallyQuasiFinite_fieldPoint
    B S hS k hk toBase W q c hq hc
  let := hft
  let : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj W) :=
    (AlgebraicGeometry.locallyQuasiFinite_iff_discreteTopology_of_subsingleton
      ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (c ≫ q)))).1 hlqf
  exact (Stack.pointsHomeomorphScheme B S hS W).symm.discreteTopology

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
