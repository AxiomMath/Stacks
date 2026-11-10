module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFinitePresentationChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionOpenSourceRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct

/-!
# A flat chart locally of finite presentation and locally quasi-finite at a point

Let `𝒴₀` be an algebraic stack over `S` which is locally quasi-finite over a field-valued point
`Spec(k) ⟶ S` of the base, and let `y` be a point of `|𝒴₀|`. The chart construction
`AlgebraicGeometry.Stack.exists_flat_isLocallyOfFinitePresentation_chart_at_point` of
**Stacks 06MF** produces a scheme `Z` of the site and a 1-morphism `Z ⟶ 𝒴₀` flat and locally of
finite presentation whose image on points contains `y`. This file shrinks `Z` so that the chart is
moreover **locally quasi-finite** in the sense of Properties of Stacks, Section **04XB**, and
does so with nothing assumed: the geometric input the shrinking needs is the quasi-finiteness
datum the chart construction already carries.

The shrinking is `AlgebraicGeometry.Stack`
`.exists_opens_isLocallyQuasiFinite_schemeStack_of_hasRelativeDimensionAt_zero`: a 1-morphism out
of a scheme of the site, locally of finite type, is locally quasi-finite on an open neighbourhood
of the image of any point of any smooth chart's base change at which the relative dimension of
**Stacks 04NM** vanishes. Flatness and local finite presentation survive the shrinking because the
inclusion of an open is flat and locally of finite presentation, and the point `y` survives
because the open contains the point of `Z` the chart construction pins.

## Main results

* `AlgebraicGeometry.Stack.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart`:
  the assembly, from a relative-dimension-zero datum on a chart of the target at the pinned point
  of `Z`.
* `AlgebraicGeometry.Stack.exists_comparison_representingMap_of_twoIso`: the comparison morphism
  from `h_T` to an algebraic space representing `V₀ ×_{𝒴₀} Z` that a 2-isomorphism of the two
  composites `T ⟶ Z ⟶ 𝒴₀` and `T ⟶ V₀ ⟶ 𝒴₀` provides, with its two projections computed.
* `AlgebraicGeometry.Stack`
  `.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_presheafEtale`: the
  relative-dimension-zero datum read off the quasi-finiteness datum of the chart construction,
  given that that comparison is étale after every representable base change.
* `AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct`: the comparison of
  two 2-fibre products of one cospan induces an isomorphism of representing presheaves,
  compatible with the two projections.
* `AlgebraicGeometry.Stack.exists_presheafEtale_innerComparison_of_isPullback_relationSlice` and
  `AlgebraicGeometry.Stack.exists_presheafEtale_comparison_of_isPullback_relationSlice`: **the
  étaleness of that comparison, proved** — for a chart which factors through the smooth chart and
  a `T` which is the fibre product of an étale piece of the charted self-intersection with `Z`.
* `AlgebraicGeometry.Stack`
  `.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_relationSlice`: the
  previous result with the étaleness hypothesis discharged, so that it is a conclusion and not a
  hypothesis.
* `AlgebraicGeometry.Stack`
  `.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_at_point`: the chart of
  **Stacks 06MF** at a point, flat, locally of finite presentation and locally quasi-finite, with
  nothing assumed.

## Implementation notes

The relative-dimension-zero datum is the hypothesis, not a conclusion: it is what a consumer of
the chart construction of **Stacks 06MF** has to produce from the quasi-finiteness datum that
construction carries, and it is stated here in exactly the shape the shrinking lemma consumes —
a smooth, not necessarily surjective, chart `V₀ ⟶ 𝒴₀`, an algebraic space `P` representing
`V₀ ×_{𝒴₀} Z`, and a point of `|P|` lying over the pinned point of `Z` at which the projection
`P ⟶ V₀` has relative dimension zero.

The second step reduces that datum to a single geometric input: **étaleness of the comparison**
`h_T ⟶ P`. Everything else in the passage from the quasi-finiteness datum of the chart
construction to the relative-dimension-zero datum is unconditional and is proved here — the
comparison itself, its two projections, the identification of quasi-finiteness of `T ⟶ V₀` at `t`
with relative dimension zero, and the transport of that along the comparison.

The third step **proves that étaleness** in the situation the chart construction of **Stacks 06MF**
produces, so the last result of the file has no étaleness hypothesis at all. The chart of
Stacks 06MF factors as `Z ⟶ V₀ ⟶ 𝒴₀` through the smooth chart, so the base change `V₀ ×_{𝒴₀} Z`
is the iterated 2-fibre product `(V₀ ×_{𝒴₀} V₀) ×_{V₀} Z` — **Stacks 02XD**, cancelling the
*first* factor of the inner product, which is the factor `Z` is glued to, so that the remaining
projection to `V₀` is the *second* leg of the self-intersection: the leg the quasi-finiteness
datum is carried by. The inner product is a cospan of *represented* categories fibred in
groupoids, so the algebraic space representing the iterated apex is a fibre product of presheaves
(**Stacks 04SD**), and the comparison out of `T = W ×_{V₀} Z` is there the base change of the
étale chart `h_W ⟶ h_R ⟶ F` of the self-intersection, hence étale. The two 2-fibre products of
the cospan — the iterated one and the canonical one of **Stacks 04T2** — are then identified on
representing algebraic spaces, compatibly with both projections.

Two elaboration notes. The spelling of a 2-fibre product's apex matters for `rw`: the apex of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` and that of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` are definitionally equal but not
syntactically, so each statement here fixes one of them and the goals are restated with `show`
where the two meet. And `AlgebraicGeometry.Stack.representingMap_comp` is applied *without* an
expected type and only then ascribed: elaborated against an expected type whose apex is spelled
the other way, its implicit arguments are solved in an order which sends the unifier into
`AlgebraicGeometry.Stack.representingMap` itself.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart of Stacks 06MF, shrunk to be locally quasi-finite.** Let `c : Z ⟶ 𝒴₀` be a
1-morphism out of a scheme of the site which is flat and locally of finite presentation, let `zs`
be a point of `|Z|` lying over the point `z₀` of the scheme `Z` and sent to `y`, and suppose the
relative dimension of **Stacks 04NM** of the projection `P ⟶ V₀` vanishes at some point `ξ₀` of
an algebraic space `P` representing `V₀ ×_{𝒴₀} Z`, for some smooth chart `V₀ ⟶ 𝒴₀`, with `ξ₀`
lying over `z₀`. Then some object of the site carries a 1-morphism to `𝒴₀` which is flat, locally
of finite presentation, **locally quasi-finite** in the sense of **Stacks 04XB**, and whose image
on points contains `y`.

The object is the open neighbourhood of `z₀` in `Z` that
`exists_opens_isLocallyQuasiFinite_schemeStack_of_hasRelativeDimensionAt_zero` produces. Flatness
and local finite presentation of the restriction are those of `c` composed with those of the open
immersion, and `y` is still in the image because the open contains `z₀`. -/
theorem exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS} (Z : BigFppfOver B S hS)
    (c : schemeStack.{u, w} B S hS Z ⟶ 𝒴₀)
    (hcflat : AlgebraicStacks.IsFlat B S hS c)
    (hclfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c)
    (z₀ : (BigFppfOver.toScheme B S hS).obj Z)
    (zs : points B S hS (schemeFibredCategory B S hS Z).val
      (schemeFibredCategory B S hS Z).property)
    (hzs : pointsHomeomorphScheme B S hS Z zs = z₀)
    (y : points B S hS 𝒴₀.val.val 𝒴₀.val.property)
    (hy : AlgebraicStacks.pointsMap B S hS c zs = y)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (haSm : AlgebraicStacks.IsSmooth B S hS a)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (ξ₀ : Space.points B S hS P)
    (hξ₀ : Space.HasRelativeDimensionAt 0 B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ₀)
    (hzξ : Space.pointsToScheme B S hS Z (Space.pointsMap B S hS P
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver Z)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ξ₀) = z₀) :
    ∃ (Z' : BigFppfOver B S hS) (c' : schemeStack.{u, w} B S hS Z' ⟶ 𝒴₀),
      AlgebraicStacks.IsFlat B S hS c' ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c' ∧
      IsLocallyQuasiFinite B S hS c'.hom ∧
      y ∈ Set.range (AlgebraicStacks.pointsMap B S hS c') ∧
      ((BigFppfOver.toScheme B S hS).obj Z').size ≤
        ((BigFppfOver.toScheme B S hS).obj Z).size := by
  classical
  obtain ⟨V₁, hmem, hqf⟩ :=
    exists_opens_isLocallyQuasiFinite_schemeStack_of_hasRelativeDimensionAt_zero.{u, w}
      B S hS 𝒴₀ Z c (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
        B S hS hclfp) V₀ a haSm P hP eP ξ₀ hξ₀
  rw [hzξ] at hmem
  refine ⟨AlgebraicStacks.openChart B S hS Z V₁,
    schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V₁) ≫ c, ?_, ?_, hqf, ?_,
    Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj Z) V₁⟩
  · exact AlgebraicStacks.isFlat_comp B S hS _ c
      (isFlat_schemeStackMap.{u, w} B S hS _ (inferInstanceAs (Flat V₁.ι))) hcflat
  · exact AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ c
      (isLocallyOfFinitePresentation_schemeStackMap.{u, w} B S hS _
        (inferInstanceAs (LocallyOfFinitePresentation V₁.ι))) hclfp
  let := pointTopology B S hS (schemeFibredCategory B S hS Z)
  let := pointTopology B S hS
    (schemeFibredCategory B S hS (AlgebraicStacks.openChart B S hS Z V₁))
  obtain ⟨w, hw⟩ :=
    (pointsHomeomorphScheme B S hS (AlgebraicStacks.openChart B S hS Z V₁)).surjective
      ⟨z₀, hmem⟩
  refine ⟨w, ?_⟩
  rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ← hy]
  congr 1
  refine (pointsHomeomorphScheme B S hS Z).injective ?_
  rw [show AlgebraicStacks.pointsMap B S hS
        (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V₁)) w =
      pointsMap B S hS (schemeFibredCategory B S hS
          (AlgebraicStacks.openChart B S hS Z V₁)).val
        (schemeFibredCategory B S hS (AlgebraicStacks.openChart B S hS Z V₁)).property
        (schemeFibredCategory B S hS Z).property
        (schemeFibredCategoryMap B S hS (AlgebraicStacks.openChartHom B S hS Z V₁)).hom
        w from rfl,
    pointsHomeomorphScheme_naturality, hw,
    AlgebraicStacks.openChartHom_toScheme, hzs]
  rfl

/-- **The comparison morphism into the algebraic space representing a base change along a
chart.** A 2-isomorphism between the two composites `T ⟶ Z ⟶ 𝒴₀` and `T ⟶ V₀ ⟶ 𝒴₀` makes
`T`, with the two morphisms of the site, a 2-commutative square over the cospan `(a, c)`, so the
strict comparison with the canonical 2-fibre product square of **Stacks 04T2** —
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks`, whose composites with the two
projections are the two legs *on the nose* — gives a 1-morphism `T ⟶ V₀ ×_{𝒴₀} Z`. Read on
representing algebraic spaces by **Stacks 04SW** it is a morphism `h_T ⟶ P` whose composites with
the two projections are the Yoneda images of the two morphisms of the site. -/
theorem exists_comparison_representingMap_of_twoIso
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS} {V₀ Z T : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒴₀)
    (kT : T ⟶ Z) (bT : T ⟶ V₀)
    (e : schemeStackMap.{u, w} B S hS kT ≫ c ≅ schemeStackMap.{u, w} B S hS bT ≫ a)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    ∃ γ : yoneda.obj T ⟶ P,
      γ ≫ representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
          (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
          (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom = yoneda.map bT ∧
        γ ≫ representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
            (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
            (PresheafOfCategories.sliceElementsEquivalenceOver Z)
            (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom = yoneda.map kT := by
  classical
  set Tsq : Bicategory.TwoCommSq a c :=
    { pt := schemeStack.{u, w} B S hS T
      fst := schemeStackMap.{u, w} B S hS bT
      snd := schemeStackMap.{u, w} B S hS kT
      iso := e.symm } with hTsq
  set γstack := (canonicalPreHomAlgebraicStacks B S hS a c Tsq).hom with hγstack
  have key : ∀ (V : BigFppfOver B S hS) (g : (twoFibreProductSquareAlgebraicStacks B S hS a c).pt ⟶
        schemeStack.{u, w} B S hS V) (k : T ⟶ V),
      γstack.hom ≫ g.hom = (schemeStackMap.{u, w} B S hS k).hom →
      representingMap B S hS (schemeStack.{u, w} B S hS T).val
          (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val (yoneda.obj T) P
          (PresheafOfCategories.sliceElementsEquivalenceOver T) eP γstack.hom ≫
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
          (schemeStack.{u, w} B S hS V).val P (yoneda.obj V) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V) g.hom = yoneda.map k := by
    intro V g k hg
    rw [← representingMap_comp B S hS (yoneda.obj T) P (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver T) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver V) γstack.hom g.hom, hg]
    exact representingMap_schemeFibredCategoryMap B S hS k
  exact ⟨_, key V₀ _ bT (congrArg Bicategory.InducedBicategory.Hom.hom
      (canonicalPreHomAlgebraicStacks_hom_comp_fst B S hS a c Tsq)),
    key Z _ kT (congrArg Bicategory.InducedBicategory.Hom.hom
      (canonicalPreHomAlgebraicStacks_hom_comp_snd B S hS a c Tsq))⟩

/-- **The chart of Stacks 06MF is locally quasi-finite after shrinking, given that its
quasi-finiteness datum compares étalely with the base change along the chart.** Let `c : Z ⟶ 𝒴₀`
be flat and locally of finite presentation with a pinned point `zs` over `z₀` sent to `y`, and let
the quasi-finiteness datum of the chart construction be given: a scheme `T` of the site, morphisms
`kT : T ⟶ Z` and `bT : T ⟶ V₀` into a smooth chart `V₀ ⟶ 𝒴₀` with `kT t = z₀` and `bT`
quasi-finite at `t`, and the comparison `h_T ⟶ P` into an algebraic space representing
`V₀ ×_{𝒴₀} Z` that the 2-isomorphism of the two composites provides
(`AlgebraicGeometry.Stack.exists_comparison_representingMap_of_twoIso`). If that comparison is
**étale after every representable base change**, the chart becomes locally quasi-finite on an open
neighbourhood of `z₀`.

Quasi-finiteness of `bT` at `t` is relative dimension zero of `h_T ⟶ h_{V₀}` there
(`AlgebraicGeometry.Space.isQuasiFiniteAt_yoneda_map_iff` and
`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero`), and relative dimension
is unchanged by a precomposition with a relatively étale morphism
(`AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_iff`), so the image of `t` in `|P|` is a
point of relative dimension zero of the projection `P ⟶ V₀` lying over `z₀`. That is the datum
`AlgebraicGeometry.Stack.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart`
consumes.

The étaleness of the comparison is a hypothesis here, and it is *discharged* in
`AlgebraicGeometry.Stack`
`.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_relationSlice`, which
replaces it by the data the chart construction of **Stacks 06MF** carries: the comparison factors
through `R ×_{V₀} Z` — `R` an étale chart of the algebraic space representing `V₀ ×_{𝒴₀} V₀` — as
the base change of that étale chart, and the slice of the relation which carries the
quasi-finiteness datum is by construction the fibre product `W ×_{V₀} Z` of an open `W` of `R`
with `Z`. That factorisation is
`AlgebraicGeometry.Stack.exists_presheafEtale_comparison_of_isPullback_relationSlice`. -/
theorem exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_presheafEtale
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS} (Z : BigFppfOver B S hS)
    (c : schemeStack.{u, w} B S hS Z ⟶ 𝒴₀)
    (hcflat : AlgebraicStacks.IsFlat B S hS c)
    (hclfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c)
    (z₀ : (BigFppfOver.toScheme B S hS).obj Z)
    (zs : points B S hS (schemeFibredCategory B S hS Z).val
      (schemeFibredCategory B S hS Z).property)
    (hzs : pointsHomeomorphScheme B S hS Z zs = z₀)
    (y : points B S hS 𝒴₀.val.val 𝒴₀.val.property)
    (hy : AlgebraicStacks.pointsMap B S hS c zs = y)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (haSm : AlgebraicStacks.IsSmooth B S hS a)
    (T : BigFppfOver B S hS) (kT : T ⟶ Z) (bT : T ⟶ V₀)
    (hbTlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map bT))
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (ht : (BigFppfOver.toScheme B S hS).map kT t = z₀)
    (hqf : quasiFiniteAt ((BigFppfOver.toScheme B S hS).map bT) t)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (γ : yoneda.obj T ⟶ P)
    (hγ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf γ)
    (hγfst : γ ≫ representingMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom = yoneda.map bT)
    (hγsnd : γ ≫ representingMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver Z)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom = yoneda.map kT) :
    ∃ (Z' : BigFppfOver B S hS) (c' : schemeStack.{u, w} B S hS Z' ⟶ 𝒴₀),
      AlgebraicStacks.IsFlat B S hS c' ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c' ∧
      IsLocallyQuasiFinite B S hS c'.hom ∧
      y ∈ Set.range (AlgebraicStacks.pointsMap B S hS c') ∧
      ((BigFppfOver.toScheme B S hS).obj Z').size ≤
        ((BigFppfOver.toScheme B S hS).obj Z).size := by
  classical
  have := hbTlft
  obtain ⟨t', ht'⟩ := Space.surjective_pointsToScheme B S hS T t
  have hlft : Space.IsLocallyOfFiniteType B S hS (yoneda.map bT) :=
    (Space.isLocallyOfFiniteType_yoneda_map_iff B S hS bT).mpr hbTlft
  have hqfat : Space.IsQuasiFiniteAt B S hS (yoneda.map bT) t' := by
    rw [Space.isQuasiFiniteAt_yoneda_map_iff B S hS bT t', ht']
    exact hqf.2
  have hd0 : Space.HasRelativeDimensionAt 0 B S hS (yoneda.map bT) t' :=
    (Space.isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS
      (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS V₀)
      (yoneda.map bT) hlft t').mp hqfat
  have hξ := (Space.hasRelativeDimensionAt_comp_iff B S hS 0 γ
    (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
      (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
      (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom)
    hγ (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS V₀) t').mp
    (by rw [hγfst]; exact hd0)
  refine exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart.{u, w}
    B S hS Z c hcflat hclfp z₀ zs hzs y hy V₀ a haSm P hP eP _ hξ ?_
  rw [← Space.pointsMap_comp_apply, hγsnd, Space.pointsToScheme_pointsMap, ht', ht]

/-- **The comparison of two 2-fibre products of one cospan, read on representing presheaves, is
an isomorphism compatible with the two projections.** Let `K` and `L` be 2-fibre products of the
same cospan `(f, g)` of categories fibred in groupoids over the big fppf site of `S`, with the two
apexes represented by presheaves `X` and `Y` and the two other corners of the cospan by `A` and
`C`. Then the morphism `X ⟶ Y` which **Stacks 04SW** reads off the mediating 1-morphism is
invertible, and its composites with the two projections of `L` are the two projections of `K`.

Invertibility is
`AlgebraicGeometry.Stack.isIso_representingMap_preHom_of_isTwoFibreProduct`. The compatibility
with the projections is the comparison 2-cell of the mediating pre-morphism, read through the
functoriality of Stacks 04SW and its invariance under 2-isomorphism. -/
theorem exists_isIso_representingMap_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {K L : Bicategory.TwoCommSq f g}
    (hK : Bicategory.IsTwoFibreProduct K) (hL : Bicategory.IsTwoFibreProduct L)
    (X Y A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eK : StacksRepresentableCFG.EquivalenceOver K.pt.val.p
      (presheafOfCategories (X ⋙ typeToCat)).p)
    (eL : StacksRepresentableCFG.EquivalenceOver L.pt.val.p
      (presheafOfCategories (Y ⋙ typeToCat)).p)
    (eA : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (A ⋙ typeToCat)).p)
    (eC : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p
      (presheafOfCategories (C ⋙ typeToCat)).p) :
    ∃ m : X ⟶ Y, IsIso m ∧
      m ≫ representingMap B S hS L.pt 𝒳 Y A eL eA L.fst =
        representingMap B S hS K.pt 𝒳 X A eK eA K.fst ∧
      m ≫ representingMap B S hS L.pt 𝒴 Y C eL eC L.snd =
        representingMap B S hS K.pt 𝒴 X C eK eC K.snd := by
  classical
  set cmp := Bicategory.twoFibreProductPreHom hL K with hcmp
  refine ⟨representingMap B S hS K.pt L.pt X Y eK eL cmp.hom,
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS hK hL cmp X Y eK eL, ?_, ?_⟩
  · exact (representingMap_comp B S hS X Y A eK eL eA cmp.hom L.fst).symm.trans
      (representingMap_congr_twoIso B S hS X A eK eA cmp.isoFst).symm
  · exact (representingMap_comp B S hS X Y C eK eL eC cmp.hom L.snd).symm.trans
      (representingMap_congr_twoIso B S hS X C eK eC cmp.isoSnd).symm
/-- A 2-fibre product of `a` with its composite `ιZ ≫ a` by a morphism `ιZ` of the site has an
apex represented by an algebraic space (**Stacks 04ZP**). -/
private theorem isRepresentableByAlgebraicSpace_of_isTwoFibreProduct_schemeStackMap_comp
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS} {V₀ Z : BigFppfOver B S hS}
    (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀) (ιZ : Z ⟶ V₀)
    {K : Bicategory.TwoCommSq a.hom (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom}
    (hK : Bicategory.IsTwoFibreProduct K) :
    IsRepresentableByAlgebraicSpace B S hS K.pt :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    (schemeStack.{u, w} B S hS Z).val 𝒴₀.val (schemeStack.{u, w} B S hS V₀).val
    (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom a.hom _ hK
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴₀.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS Z)
      (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V₀)

/-- The Yoneda image of `chartLeg` of a leg of the self-intersection `V₀ ×_{𝒴₀} V₀` is the
chart followed by the morphism of representing presheaves of that leg. -/
private theorem yoneda_map_chartLeg_self_intersection
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a a).pt.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (R : BigFppfOver B S hS) (cR : yoneda.obj R ⟶ F)
    (leg : (twoFibreProductSquareAlgebraicStacks B S hS a a).pt ⟶ schemeStack.{u, w} B S hS V₀) :
    yoneda.map (chartLeg B S hS V₀ a (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        leg) =
      cR ≫ representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a a).pt.val
        (schemeStack.{u, w} B S hS V₀).val F (yoneda.obj V₀) eF
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀) leg.hom :=
  Functor.map_preimage _ _

/-- **The slice of a relation compares étalely with the inner 2-fibre product
`(V₀ ×_{𝒴₀} V₀) ×_{V₀} Z`.** Let `a : V₀ ⟶ 𝒴₀` be a 1-morphism from a scheme of the site, let `F`
be an algebraic space representing the self-intersection `V₀ ×_{𝒴₀} V₀` and let `cR : h_R ⟶ F` be
an étale chart of it, so that the two projections of the self-intersection become two morphisms of
schemes `a', b' : R ⟶ V₀` (**Stacks 04SW**, `AlgebraicGeometry.Stack.chartLeg`). Let
`ιZ : Z ⟶ V₀` be a morphism of the site, let `jW : W ⟶ R` have étale underlying morphism of
schemes, and let `T` be, with `jT : T ⟶ W` and `kT : T ⟶ Z`, the fibre product
`W ×_{a', V₀, ιZ} Z`. Then some algebraic space `Q` represents the iterated 2-fibre product
`(V₀ ×_{𝒴₀} V₀) ×_{V₀} Z` — the product taken along the *first* projection, the one `Z` is glued
to — and carries a morphism `h_T ⟶ Q` which is **étale after every representable base change**
and whose composites with the two projections are `jT ≫ jW ≫ cR` and `kT`.

The iterated apex is the canonical 2-fibre product of a cospan of *represented* categories fibred
in groupoids, so **Stacks 04SD**
(`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct`) makes `Q` the fibre
product `F ×_{h_{V₀}} h_Z` of presheaves. The chart `h_W ⟶ h_R ⟶ F` is étale (**Stacks 03FT**),
`h_T` is `h_W ×_{h_{V₀}} h_Z` because the Yoneda embedding preserves the fibre product of the
site, and cancelling those two pullback squares exhibits `h_T ⟶ Q` as a base change of that
chart, hence étale (**Stacks 03FU**). -/
theorem exists_presheafEtale_innerComparison_of_isPullback_relationSlice
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a a).pt.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (R : BigFppfOver B S hS) (cR : yoneda.obj R ⟶ F)
    (hcR : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf cR)
    (Z : BigFppfOver B S hS) (ιZ : Z ⟶ V₀)
    (W T : BigFppfOver B S hS) (jW : W ⟶ R) (jT : T ⟶ W) (kT : T ⟶ Z)
    (hjW : Etale ((BigFppfOver.toScheme B S hS).map jW))
    (hpb : IsPullback jT kT (jW ≫ chartLeg B S hS V₀ a
        (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS a a).fst) ιZ) :
    ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Q ∧
      ∃ (eQ : StacksRepresentableCFG.EquivalenceOver
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
            (schemeStackMap.{u, w} B S hS ιZ).hom).pt.val.p
          (presheafOfCategories (Q ⋙ typeToCat)).p)
        (γ : yoneda.obj T ⟶ Q),
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf γ ∧
        γ ≫ representingMap B S hS
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
              (schemeStackMap.{u, w} B S hS ιZ).hom).pt
            (twoFibreProductSquareAlgebraicStacks B S hS a a).pt.val Q F eQ eF
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
              (schemeStackMap.{u, w} B S hS ιZ).hom).fst =
          yoneda.map jT ≫ (yoneda.map jW ≫ cR) ∧
        γ ≫ representingMap B S hS
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
              (schemeStackMap.{u, w} B S hS ιZ).hom).pt
            (schemeStack.{u, w} B S hS Z).val Q (yoneda.obj Z) eQ
            (PresheafOfCategories.sliceElementsEquivalenceOver Z)
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
              (schemeStackMap.{u, w} B S hS ιZ).hom).snd =
          yoneda.map kT := by
  classical
  -- the first-factor cancellation of Stacks 02XD, and the inner canonical square
  have hCF := CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
    a.hom a.hom (schemeStackMap.{u, w} B S hS ιZ).hom
    (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom (Iso.refl _)
  have hO := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
    (schemeStackMap.{u, w} B S hS ιZ).hom
  -- the apex is representable by an algebraic space, Stacks 04ZP
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct_schemeStackMap_comp.{u, w} B S hS a ιZ hCF
  -- the apex is the fibre product `F ×_{h_{V₀}} h_Z` of presheaves, Stacks 04SD
  have hQpb := isPullback_representingMap_of_isTwoFibreProduct B S hS hO
    F (yoneda.obj Z) (yoneda.obj V₀) Q Q eF
    (PresheafOfCategories.sliceElementsEquivalenceOver Z)
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀) eQ eQ
  have hιZ : representingMap B S hS (schemeStack.{u, w} B S hS Z).val
      (schemeStack.{u, w} B S hS V₀).val (yoneda.obj Z) (yoneda.obj V₀)
      (PresheafOfCategories.sliceElementsEquivalenceOver Z)
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
      (schemeStackMap.{u, w} B S hS ιZ).hom = yoneda.map ιZ :=
    representingMap_schemeFibredCategoryMap B S hS ιZ
  rw [hιZ] at hQpb
  -- the first leg of the self-intersection, read on the chart
  have haLegY := yoneda_map_chartLeg_self_intersection.{u, w} B S hS V₀ a F eF R cR
    (twoFibreProductSquareAlgebraicStacks B S hS a a).fst
  -- the chart of the self-intersection restricted to `W` is still étale
  have hcWetale : Space.IsEtale B S hS (yoneda.map jW ≫ cR) :=
    Space.isEtale_comp B S hS
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map jW)).2
        (Space.presheaf_yoneda_map_of_inverseImage B S hS
          AlgebraicGeometry.Etale.etale_isStableUnderBaseChange jW hjW))
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS cR).2 hcR)
  have hcWq : (yoneda.map jW ≫ cR) ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).pt
        (schemeStack.{u, w} B S hS V₀).val F (yoneda.obj V₀) eF
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst =
      yoneda.map (jW ≫ chartLeg B S hS V₀ a
        (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS a a).fst) := by
    rw [Functor.map_comp, haLegY, Category.assoc]
    rfl
  have hcomm : ((yoneda.map jT ≫ (yoneda.map jW ≫ cR)) ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).pt
        (schemeStack.{u, w} B S hS V₀).val F (yoneda.obj V₀) eF
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst) =
      yoneda.map kT ≫ yoneda.map ιZ := by
    rw [Category.assoc, hcWq, ← Functor.map_comp, ← Functor.map_comp, hpb.w]
  -- the comparison is a base change of that chart, hence étale
  have hγfst' := hQpb.lift_fst (yoneda.map jT ≫ (yoneda.map jW ≫ cR)) (yoneda.map kT) hcomm
  have hγsnd' := hQpb.lift_snd (yoneda.map jT ≫ (yoneda.map jW ≫ cR)) (yoneda.map kT) hcomm
  have hsq : IsPullback (yoneda.map jT)
      (hQpb.lift (yoneda.map jT ≫ (yoneda.map jW ≫ cR)) (yoneda.map kT) hcomm)
      (yoneda.map jW ≫ cR)
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
          (schemeStackMap.{u, w} B S hS ιZ).hom).pt
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).pt Q F
        eQ eF
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
          (schemeStackMap.{u, w} B S hS ιZ).hom).fst) := by
    refine (IsPullback.of_right ?_ hγfst' hQpb.flip).flip
    rw [hγsnd', hcWq]
    exact (hpb.map (yoneda (C := BigFppfOver B S hS))).flip
  exact ⟨Q, hQ, eQ, _,
    (Space.isEtale_iff_presheaf_of_yoneda B S hS _).1
      (Space.isEtale_of_isPullback_yoneda B S hS hsq hcWetale),
    hγfst', hγsnd'⟩

/-- **The comparison of the slice of a relation with the base change of the sliced chart is étale
after every representable base change.** Let `a : V₀ ⟶ 𝒴₀` be a 1-morphism from a scheme of the
site, let `F` be an algebraic space representing the self-intersection `V₀ ×_{𝒴₀} V₀` and let
`cR : h_R ⟶ F` be an étale chart of it, so that the two projections of the self-intersection
become two morphisms of schemes `a', b' : R ⟶ V₀` (**Stacks 04SW**,
`AlgebraicGeometry.Stack.chartLeg`). Let `ιZ : Z ⟶ V₀` be a morphism of the site, read as the
chart `c = ιZ ≫ a` of `𝒴₀`, let `jW : W ⟶ R` have étale underlying morphism of schemes, and let
`T` be, with `jT : T ⟶ W` and `kT : T ⟶ Z`, the fibre product `W ×_{a', V₀, ιZ} Z`. Then some
algebraic space `P` represents `V₀ ×_{𝒴₀} Z` and carries a comparison `h_T ⟶ P` which is **étale
after every representable base change** and whose two projections are `jT ≫ jW ≫ b'` and `kT`.

This is the factorisation the étaleness hypothesis of
`AlgebraicGeometry.Stack`
`.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_presheafEtale` asks for.
The chart `c` factors through `a`, so **Stacks 02XD** —
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare`, cancelling the *first*
factor of the inner product, which is the factor `Z` is glued to — exhibits
`(V₀ ×_{𝒴₀} V₀) ×_{V₀} Z` as a 2-fibre product of the cospan `(a, c)`. On that apex the comparison
is étale, which is
`AlgebraicGeometry.Stack.exists_presheafEtale_innerComparison_of_isPullback_relationSlice`; the
algebraic space representing it and the one representing the canonical 2-fibre product of `(a, c)`
are then identified by
`AlgebraicGeometry.Stack.exists_isIso_representingMap_of_isTwoFibreProduct`, which carries the two
projections across. The first projection of the iterated apex to `V₀` is, *on the nose*, its
projection to the self-intersection followed by the *second* projection of the
self-intersection — which is `b'` on the chart, the leg the quasi-finiteness datum of
**Stacks 06MF** is carried by. -/
theorem exists_presheafEtale_comparison_of_isPullback_relationSlice
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a a).pt.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (R : BigFppfOver B S hS) (cR : yoneda.obj R ⟶ F)
    (hcR : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf cR)
    (Z : BigFppfOver B S hS) (ιZ : Z ⟶ V₀)
    (W T : BigFppfOver B S hS) (jW : W ⟶ R) (jT : T ⟶ W) (kT : T ⟶ Z)
    (hjW : Etale ((BigFppfOver.toScheme B S hS).map jW))
    (hpb : IsPullback jT kT (jW ≫ chartLeg B S hS V₀ a
        (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS a a).fst) ιZ) :
    ∃ (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS P ∧
      ∃ (eP : StacksRepresentableCFG.EquivalenceOver
          (twoFibreProductSquareAlgebraicStacks B S hS a
            (schemeStackMap.{u, w} B S hS ιZ ≫ a)).pt.val.val.p
          (presheafOfCategories (P ⋙ typeToCat)).p)
        (γ : yoneda.obj T ⟶ P),
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf γ ∧
        γ ≫ representingMap B S hS
            (twoFibreProductSquareAlgebraicStacks B S hS a
              (schemeStackMap.{u, w} B S hS ιZ ≫ a)).pt.val
            (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
            (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
            (twoFibreProductSquareAlgebraicStacks B S hS a
              (schemeStackMap.{u, w} B S hS ιZ ≫ a)).fst.hom =
          yoneda.map (jT ≫ jW ≫ chartLeg B S hS V₀ a
            (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
            (twoFibreProductSquareAlgebraicStacks B S hS a a).snd) ∧
        γ ≫ representingMap B S hS
            (twoFibreProductSquareAlgebraicStacks B S hS a
              (schemeStackMap.{u, w} B S hS ιZ ≫ a)).pt.val
            (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
            (PresheafOfCategories.sliceElementsEquivalenceOver Z)
            (twoFibreProductSquareAlgebraicStacks B S hS a
              (schemeStackMap.{u, w} B S hS ιZ ≫ a)).snd.hom =
          yoneda.map kT := by
  classical
  obtain ⟨Q, hQ, eQ, γ, hγ, hγfst, hγsnd⟩ :=
    exists_presheafEtale_innerComparison_of_isPullback_relationSlice.{u, w}
      B S hS V₀ a F eF R cR hcR Z ιZ W T jW jT kT hjW hpb
  have hKac := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    a.hom (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom
  have hCF := CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
    a.hom a.hom (schemeStackMap.{u, w} B S hS ιZ).hom
    (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom (Iso.refl _)
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct_schemeStackMap_comp.{u, w} B S hS a ιZ hKac
  obtain ⟨m, hmiso, hmfst, hmsnd⟩ := exists_isIso_representingMap_of_isTwoFibreProduct B S hS
    hCF hKac Q P (yoneda.obj V₀) (yoneda.obj Z) eQ eP
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
    (PresheafOfCategories.sliceElementsEquivalenceOver Z)
  -- the first projection of the iterated apex is its inner projection followed by the second
  -- projection of the self-intersection
  have hcomp0 := representingMap_comp B S hS Q F (yoneda.obj V₀) eQ eF
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).fst
      (schemeStackMap.{u, w} B S hS ιZ).hom).fst
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom a.hom).snd
  have hcomp : representingMap B S hS
        (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} a.hom a.hom
          (schemeStackMap.{u, w} B S hS ιZ).hom (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom
          (Iso.refl _)).pt
        (schemeStack.{u, w} B S hS V₀).val Q (yoneda.obj V₀) eQ
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} a.hom a.hom
          (schemeStackMap.{u, w} B S hS ιZ).hom (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom
          (Iso.refl _)).fst = _ := hcomp0
  have hbLegY := yoneda_map_chartLeg_self_intersection.{u, w} B S hS V₀ a F eF R cR
    (twoFibreProductSquareAlgebraicStacks B S hS a a).snd
  have := hmiso
  refine ⟨P, hP, eP, γ ≫ m, ?_, ?_, ?_⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso _ γ m).mpr hγ
  · change (γ ≫ m) ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom
          (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom).pt
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom
          (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom).fst = _
    rw [Category.assoc, hmfst, hcomp, ← Category.assoc, hγfst, Functor.map_comp,
      Functor.map_comp, hbLegY]
    simp only [Category.assoc]
    rfl
  · change (γ ≫ m) ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom
          (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom).pt
        (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver Z)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a.hom
          (schemeStackMap.{u, w} B S hS ιZ ≫ a).hom).snd = _
    rw [Category.assoc, hmsnd]
    exact hγsnd

/-- **The chart of Stacks 06MF is locally quasi-finite after shrinking: the étaleness of the
comparison is a conclusion.** Let `a : V₀ ⟶ 𝒴₀` be a *smooth* 1-morphism from a scheme of the
site, let `F` be an algebraic space representing the self-intersection `V₀ ×_{𝒴₀} V₀` with an
étale chart `cR : h_R ⟶ F`, whose two projections become the two morphisms of schemes
`a', b' : R ⟶ V₀` of **Stacks 04SW**, and let the chart `c = ιZ ≫ a` of `𝒴₀` be flat and locally
of finite presentation, with a pinned point `zs` of `|Z|` over `z₀` sent to `y`. Let `W ⟶ R` have
étale underlying morphism of schemes and let `T` be the fibre product `W ×_{a', V₀, ιZ} Z`,
carrying a point `t` over `z₀` at which the composite `T ⟶ W ⟶ R ⟶ V₀` along `b'` is locally of
finite type and quasi-finite. Then some object of the site carries a 1-morphism to `𝒴₀` which is
flat, locally of finite presentation, **locally quasi-finite** in the sense of **Stacks 04XB**,
and whose image on points contains `y`.

This is
`AlgebraicGeometry.Stack`
`.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_presheafEtale` with its
étaleness hypothesis **discharged**: the comparison of the slice `T` of the relation with the base
change `V₀ ×_{𝒴₀} Z` is étale after every representable base change, by
`AlgebraicGeometry.Stack.exists_presheafEtale_comparison_of_isPullback_relationSlice`. The
hypotheses which replace it are exactly the data the chart construction of **Stacks 06MF** carries:
its smooth chart, the étale chart of the charted self-intersection, the slice of the relation, and
the fibre product square which exhibits that slice as the base change of the sliced chart. -/
theorem exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_relationSlice
    {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (haSm : AlgebraicStacks.IsSmooth B S hS a)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a a).pt.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (R : BigFppfOver B S hS) (cR : yoneda.obj R ⟶ F)
    (hcR : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf cR)
    (Z : BigFppfOver B S hS) (ιZ : Z ⟶ V₀)
    (hcflat : AlgebraicStacks.IsFlat B S hS (schemeStackMap.{u, w} B S hS ιZ ≫ a))
    (hclfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (schemeStackMap.{u, w} B S hS ιZ ≫ a))
    (z₀ : (BigFppfOver.toScheme B S hS).obj Z)
    (zs : points B S hS (schemeFibredCategory B S hS Z).val
      (schemeFibredCategory B S hS Z).property)
    (hzs : pointsHomeomorphScheme B S hS Z zs = z₀)
    (y : points B S hS 𝒴₀.val.val 𝒴₀.val.property)
    (hy : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ιZ ≫ a) zs = y)
    (W T : BigFppfOver B S hS) (jW : W ⟶ R) (jT : T ⟶ W) (kT : T ⟶ Z)
    (hjW : Etale ((BigFppfOver.toScheme B S hS).map jW))
    (hpb : IsPullback jT kT (jW ≫ chartLeg B S hS V₀ a
        (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS a a).fst) ιZ)
    (hbTlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (jT ≫ jW ≫ chartLeg B S hS V₀ a
        (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS a a).snd)))
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (ht : (BigFppfOver.toScheme B S hS).map kT t = z₀)
    (hqf : quasiFiniteAt ((BigFppfOver.toScheme B S hS).map
      (jT ≫ jW ≫ chartLeg B S hS V₀ a
        (twoFibreProductSquareAlgebraicStacks B S hS a a) F eF R cR
        (twoFibreProductSquareAlgebraicStacks B S hS a a).snd)) t) :
    ∃ (Z' : BigFppfOver B S hS) (c' : schemeStack.{u, w} B S hS Z' ⟶ 𝒴₀),
      AlgebraicStacks.IsFlat B S hS c' ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c' ∧
      IsLocallyQuasiFinite B S hS c'.hom ∧
      y ∈ Set.range (AlgebraicStacks.pointsMap B S hS c') ∧
      ((BigFppfOver.toScheme B S hS).obj Z').size ≤
        ((BigFppfOver.toScheme B S hS).obj Z).size := by
  classical
  obtain ⟨P, hP, eP, γ, hγ, hγfst, hγsnd⟩ :=
    exists_presheafEtale_comparison_of_isPullback_relationSlice.{u, w}
      B S hS V₀ a F eF R cR hcR Z ιZ W T jW jT kT hjW hpb
  exact exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_presheafEtale.{u, w}
    B S hS Z (schemeStackMap.{u, w} B S hS ιZ ≫ a) hcflat hclfp z₀ zs hzs y hy V₀ a haSm T kT _
    hbTlft t ht hqf P hP eP γ hγ hγfst hγsnd

/-- **The chart of Stacks 06MF at a point is flat, locally of finite presentation and locally
quasi-finite — nothing assumed.** Let `𝒴₀` be an algebraic stack over `S` which is locally
quasi-finite over a field-valued point `Spec(k) ⟶ S` of the base, and let `y` be a point of
`|𝒴₀|`. Then some object `Z` of the site carries a 1-morphism `Z ⟶ 𝒴₀` which is flat, locally of
finite presentation and **locally quasi-finite** in the sense of Properties of Stacks, Section
**04XB**, and whose image on points contains `y`.

This is `AlgebraicGeometry.Stack.exists_flat_isLocallyOfFinitePresentation_chart_at_point`
followed by
`AlgebraicGeometry.Stack`
`.exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_relationSlice`: the
chart construction exports, besides its quasi-finiteness datum, the geometric input that datum's
comparison needs — the étale chart of the charted self-intersection, the factorisation of the
chart through the smooth chart, and the fibre product square exhibiting the slice of the relation
as `W ×_{V₀} Z` — so the étaleness of the comparison is proved rather than assumed. -/
theorem exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_at_point
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (𝒴₀ : AlgebraicStacks.{u, w} B S hS)
    (q : 𝒴₀ ⟶ schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (hq : AlgebraicStacks.IsLocallyQuasiFinite B S hS q)
    (y : points B S hS 𝒴₀.val.val 𝒴₀.val.property) :
    ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒴₀),
      AlgebraicStacks.IsFlat B S hS c ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c ∧
      IsLocallyQuasiFinite B S hS c.hom ∧
      y ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) := by
  classical
  obtain ⟨Z, c, z₀, zs, hcflat, hclfp, hzs, hy, Uc, pc, T, kT, bT, t, hpcSm, -, -, -, -, ht,
    hbTlfp, hqf, Fc, eFc, Rc, Wc, cRc, ιc, jWc, jTc, hcRc, hjWc, hceq, hbTeq, hpbc⟩ :=
    exists_flat_isLocallyOfFinitePresentation_chart_at_point.{u, w} B S hS k hk toBase 𝒴₀ q hq y
  subst hceq
  subst hbTeq
  have := hbTlfp
  obtain ⟨Z', c', hflat, hlfp, hlqf, hrange, -⟩ :=
    exists_flat_isLocallyOfFinitePresentation_isLocallyQuasiFinite_chart_of_relationSlice.{u, w}
      B S hS Uc pc hpcSm Fc eFc Rc cRc hcRc Z ιc hcflat hclfp z₀ zs hzs y hy Wc T jWc jTc kT hjWc
      hpbc inferInstance t ht hqf
  exact ⟨Z', c', hflat, hlfp, hlqf, hrange⟩

end AlgebraicGeometry.Stack

end
