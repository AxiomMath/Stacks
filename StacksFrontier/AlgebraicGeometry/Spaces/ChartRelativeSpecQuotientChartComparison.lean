module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientAtlasOver
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# The charts of the relative spectrum are the base changes of the charts of the base

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `ν : X' = \underline{Spec}_X(A) ⟶ X` be the
relative spectrum, the quotient of the relation of a pair `pr₁, pr₂ : V' ⟶ V₂` of étale charts
with `V₂ ⟶ X` surjective.

`ν` is affine, hence representable, so an étale scheme chart `W` of `X` base changes to the
étale scheme chart `W ×_X X'` of `X'` (`AlgebraicGeometry.Space.smallBaseChange`). For a chart
`W` *over `V₂`* the relative spectrum `\underline{Spec}_{W}(A|_{W})` is a second fibre product of
the same cospan, by `AlgebraicGeometry.Space.isPullback_chartRelativeSpecAtlasOver`. The two are
isomorphic as étale scheme charts of `X'`, naturally in `W`.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverChart`:
  `\underline{Spec}_{W}(A|_{W})` read as an étale scheme chart of `X'`, its chart morphism being
  the atlas `AlgebraicGeometry.Space.chartRelativeSpecAtlasOver`.
* `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverFunctor`: the same, functorially on the
  charts over `V₂`.
* `AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecIso`: the base change along `ν` of a
  chart over `V₂` is the relative spectrum of `A` over that chart, as an isomorphism of étale
  scheme charts of `X'`.
* `AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecFunctorIso`: the same comparison as an
  isomorphism of functors `ChartOver V₂ ⥤ SmallEtale X'`.

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverLeftIso_hom_comp_atlas` and
  `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverLeftIso_hom_comp_toChart`: the comparison is
  compatible with both cartesian projections, to `X'` and to `W`.
* `AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecIso_naturality`: the comparison is
  natural in the chart over `V₂`.

## Implementation notes

A cartesian square determines its top edge only up to an automorphism of `X' ×_X W` over `W`, so
an isomorphism at a single chart is uniqueness of fibre products; the content is its naturality
in `W`, which holds because the atlas at `W` is attached to the object `W` and not to a chosen
morphism `W ⟶ V₂`.

The isomorphism is taken in the big fppf category: uniqueness of fibre products gives an
isomorphism of the two representing presheaves, which is pulled back along the fully faithful
`CategoryTheory.yoneda` by `CategoryTheory.Functor.preimageIso`.

`AlgebraicGeometry.Space.smallBaseChange` is semireducible, so its spelling of `X' ×_X W` and the
spelling `hν.pullback` of the representability witness are definitionally but not syntactically
equal. `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverLeftIso` is stated at `hν.pullback` and
`AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecLeftIso` at the base change.

The relative spectrum over a chart is an object of the site only if its underlying scheme is
contained in the site, a hypothesis of `AlgebraicGeometry.Space.chartRelativeSpecSite`. The
pointwise statements assume it for the one chart they mention; the functor assumes it for every
chart, as `hcon`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

/-! ### `ν` is representable -/

include hsq hsurj hV'' in
/-- The structure morphism `ν : \underline{Spec}_X(A) ⟶ X` is representable. -/
theorem relativelyRepresentable_chartRelativeSpecQuotientHom :
    yoneda.relativelyRepresentable
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom :=
  relativelyRepresentable_hom_of_isAffineHom B S hS _
    (isAffineHom_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'')

/-! ### The relative spectrum over a chart as a chart of the relative spectrum -/

section Chart

variable (W : ChartOver B S hS X.1 V₂)
    (hW : B.Contains (chartRelativeSpec B S hS X A hA W.obj))

include hsq hsurj hV''

/-- The relative spectrum of `A` over a chart over `V₂`, as an étale scheme chart of
`X' = \underline{Spec}_X(A)` whose chart morphism is the atlas
`AlgebraicGeometry.Space.chartRelativeSpecAtlasOver`. -/
def chartRelativeSpecAtlasOverChart :
    SmallEtale B S hS
      (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1 :=
  ⟨CostructuredArrow.mk (chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW),
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
        W hW).flip W.obj.property⟩

/-- The chart morphism of `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverChart` is the
atlas. -/
@[simp]
theorem chartRelativeSpecAtlasOverChart_obj_hom :
    (chartRelativeSpecAtlasOverChart B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W hW).obj.hom =
      chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW :=
  rfl

/-- The object of the big fppf category over `S` underlying
`AlgebraicGeometry.Space.chartRelativeSpecAtlasOverChart` is the relative spectrum over the
chart. -/
@[simp]
theorem chartRelativeSpecAtlasOverChart_obj_left :
    (chartRelativeSpecAtlasOverChart B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
        W hW).obj.left =
      chartRelativeSpecSite B S hS X A hA W.obj hW :=
  rfl

/-! ### The comparison -/

/-- The object of the big fppf category over `S` representing the base change `X' ×_X W` is
isomorphic to the relative spectrum of `A` over `W`, both being fibre products of
`X' ⟶ X ⟵ W`. -/
def chartRelativeSpecAtlasOverLeftIso :
    (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'').pullback W.obj.obj.hom ≅
      chartRelativeSpecSite B S hS X A hA W.obj hW :=
  yoneda.preimageIso
    (((relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'').isPullback W.obj.obj.hom).isoIsPullback _ _
      (isPullback_chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
        W hW))

/-- The image under `CategoryTheory.yoneda` of
`AlgebraicGeometry.Space.chartRelativeSpecAtlasOverLeftIso` is the comparison of fibre products
`CategoryTheory.IsPullback.isoIsPullback`. -/
theorem yoneda_map_chartRelativeSpecAtlasOverLeftIso_hom :
    yoneda.map (chartRelativeSpecAtlasOverLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
        W hW).hom =
      (((relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'').isPullback W.obj.obj.hom).isoIsPullback _ _
        (isPullback_chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W hW)).hom :=
  yoneda.map_preimage _

/-- The comparison composed with the atlas is the cartesian projection of the base change to
`X'`. -/
theorem chartRelativeSpecAtlasOverLeftIso_hom_comp_atlas :
    yoneda.map (chartRelativeSpecAtlasOverLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W hW).hom ≫
        chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW =
      (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'').fst W.obj.obj.hom :=
  (congrArg (fun m ↦ m ≫ chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW)
      (yoneda_map_chartRelativeSpecAtlasOverLeftIso_hom B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'' W hW)).trans
    (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- The comparison composed with the structure morphism of the relative spectrum over `W` is the
cartesian projection of the base change to `W`. -/
theorem chartRelativeSpecAtlasOverLeftIso_hom_comp_toChart :
    (chartRelativeSpecAtlasOverLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W hW).hom ≫
        chartRelativeSpecSiteToChart B S hS X A hA W.obj hW =
      (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'').snd W.obj.obj.hom :=
  yoneda.map_injective ((yoneda.map_comp _ _).trans
    ((congrArg (fun m ↦ m ≫ yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA W.obj hW))
        (yoneda_map_chartRelativeSpecAtlasOverLeftIso_hom B S hS X A hA pr₁ pr₂ hsq hsurj
          hV' hV₂ hV'' W hW)).trans
      (IsPullback.isoIsPullback_hom_snd _ _ _ _)))

/-- The base change along `ν` of a chart over `V₂` is isomorphic, as an étale scheme chart of
`X'`, to the relative spectrum of `A` over that chart. -/
def smallBaseChangeChartRelativeSpecIso :
    (smallBaseChange B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'')).obj W.obj ≅
      chartRelativeSpecAtlasOverChart B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W hW :=
  (IsEtaleChart B S hS
      (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1).isoMk
    (CostructuredArrow.isoMk
      (chartRelativeSpecAtlasOverLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W hW)
      (chartRelativeSpecAtlasOverLeftIso_hom_comp_atlas B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'' W hW))

/-- `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverLeftIso` with its source spelled as the
base change of the chart rather than as the fibre product of the representability witness. -/
def smallBaseChangeChartRelativeSpecLeftIso :
    ((smallBaseChange B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'')).obj W.obj).obj.left ≅
      chartRelativeSpecSite B S hS X A hA W.obj hW :=
  chartRelativeSpecAtlasOverLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W hW

/-- `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverLeftIso_hom_comp_toChart` in the spelling
of `AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecLeftIso`: the comparison composed
with the structure morphism of the relative spectrum over `W` is the projection
`AlgebraicGeometry.Space.smallBaseChangeProjection` at `W`. -/
theorem smallBaseChangeChartRelativeSpecLeftIso_hom_comp_toChart :
    (smallBaseChangeChartRelativeSpecLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W hW).hom ≫
        chartRelativeSpecSiteToChart B S hS X A hA W.obj hW =
      (smallBaseChangeProjection B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'')).app W.obj :=
  chartRelativeSpecAtlasOverLeftIso_hom_comp_toChart B S hS X A hA pr₁ pr₂ hsq hsurj
    hV' hV₂ hV'' W hW

/-- The underlying morphism of the big fppf category over `S` of the comparison of charts is
`AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecLeftIso`. -/
theorem smallBaseChangeChartRelativeSpecIso_hom_hom_left :
    (smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W hW).hom.hom.left =
      (smallBaseChangeChartRelativeSpecLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
        W hW).hom :=
  rfl

end Chart

/-! ### Functoriality and naturality -/

section Naturality

variable (W W₂ : ChartOver B S hS X.1 V₂)
    (hW : B.Contains (chartRelativeSpec B S hS X A hA W.obj))
    (hW₂ : B.Contains (chartRelativeSpec B S hS X A hA W₂.obj))

include hsq hsurj hV''

/-- The morphism of étale scheme charts of `X'` induced by a morphism `k` of charts over `V₂`:
the morphism of relative spectra over `k`. -/
def chartRelativeSpecAtlasOverChartMap (k : W ⟶ W₂) :
    chartRelativeSpecAtlasOverChart B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W hW ⟶
      chartRelativeSpecAtlasOverChart B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' W₂ hW₂ :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (chartRelativeSpecSiteMap B S hS X A hA k.hom hW hW₂)
    (chartRelativeSpecSiteMap_comp_chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hsq
      hV' hV₂ W hW W₂ hW₂ k))

/-- The morphism of the big fppf category over `S` underlying
`AlgebraicGeometry.Space.chartRelativeSpecAtlasOverChartMap` is the morphism of relative
spectra. -/
@[simp]
theorem chartRelativeSpecAtlasOverChartMap_hom_left (k : W ⟶ W₂) :
    (chartRelativeSpecAtlasOverChartMap B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W W₂ hW hW₂ k).hom.left =
      chartRelativeSpecSiteMap B S hS X A hA k.hom hW hW₂ :=
  rfl

/-- The comparison `AlgebraicGeometry.Space.smallBaseChangeChartRelativeSpecIso` is natural in
the chart over `V₂`. -/
theorem smallBaseChangeChartRelativeSpecIso_naturality (k : W ⟶ W₂) :
    (smallBaseChange B S hS
            (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
            (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq
              hsurj hV' hV₂ hV'')).map k.hom ≫
        (smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W₂ hW₂).hom =
      (smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
            W hW).hom ≫
        chartRelativeSpecAtlasOverChartMap B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W W₂ hW hW₂ k := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (yoneda.map_injective ?_))
  refine (isPullback_chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
    W₂ hW₂).hom_ext ?_ ?_
  · exact (CostructuredArrow.w (((smallBaseChange B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq
            hsurj hV' hV₂ hV'')).map k.hom ≫
        (smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
          W₂ hW₂).hom).hom)).trans
      (CostructuredArrow.w
        (((smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
              W hW).hom ≫
          chartRelativeSpecAtlasOverChartMap B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
            W W₂ hW hW₂ k).hom)).symm
  · refine (yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map ?_).trans (yoneda.map_comp _ _))
    show (smallBaseChange B S hS
              (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
              (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq
                hsurj hV' hV₂ hV'') ⋙ SmallEtale.toOver B S hS
                (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1).map
            k.hom ≫
          (smallBaseChangeChartRelativeSpecLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj
              hV' hV₂ hV'' W₂ hW₂).hom ≫
            chartRelativeSpecSiteToChart B S hS X A hA W₂.obj hW₂ =
        (smallBaseChangeChartRelativeSpecLeftIso B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'' W hW).hom ≫
          chartRelativeSpecSiteMap B S hS X A hA k.hom hW hW₂ ≫
            chartRelativeSpecSiteToChart B S hS X A hA W₂.obj hW₂
    rw [smallBaseChangeChartRelativeSpecLeftIso_hom_comp_toChart,
      (isPullback_chartRelativeSpecSiteMap B S hS X A hA k.hom hW hW₂).w, ← Category.assoc,
      smallBaseChangeChartRelativeSpecLeftIso_hom_comp_toChart]
    exact (smallBaseChangeProjection B S hS
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
      (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
        hV' hV₂ hV'')).naturality k.hom

end Naturality

/-! ### The comparison as an isomorphism of functors -/

section Functor

variable (hcon : ∀ V : SmallEtale B S hS X.1, B.Contains (chartRelativeSpec B S hS X A hA V))

include hsq hsurj hV''

/-- The relative spectra of `A` over the charts over `V₂`, as a functor to the étale scheme
charts of `X'`: on objects it is `AlgebraicGeometry.Space.chartRelativeSpecAtlasOverChart` and on
morphisms the morphism of relative spectra. -/
def chartRelativeSpecAtlasOverFunctor :
    ChartOver B S hS X.1 V₂ ⥤
      SmallEtale B S hS
        (chartRelativeSpecQuotient B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').1 where
  obj W := chartRelativeSpecAtlasOverChart B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
    W (hcon W.obj)
  map {W W₂} k := chartRelativeSpecAtlasOverChartMap B S hS X A hA pr₁ pr₂ hsq hsurj
    hV' hV₂ hV'' W W₂ (hcon W.obj) (hcon W₂.obj) k
  map_id W := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact chartRelativeSpecSiteMap_id B S hS X A hA (hcon W.obj)
  map_comp {W W₂ W₃} k l := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact chartRelativeSpecSiteMap_comp B S hS X A hA (hcon W.obj) (hcon W₂.obj)
      (hcon W₃.obj) k.hom l.hom

/-- Base change along `ν` of the charts over `V₂` is isomorphic, as a functor to the étale scheme
charts of `X'`, to the relative spectrum of `A` over them. -/
def smallBaseChangeChartRelativeSpecFunctorIso :
    chartOverInclusion B S hS X.1 V₂ ⋙
        smallBaseChange B S hS
          (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')
          (relativelyRepresentable_chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hsurj
            hV' hV₂ hV'') ≅
      chartRelativeSpecAtlasOverFunctor B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV'' hcon :=
  NatIso.ofComponents
    (fun W ↦ smallBaseChangeChartRelativeSpecIso B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂ hV''
      W (hcon W.obj))
    (fun k ↦ smallBaseChangeChartRelativeSpecIso_naturality B S hS X A hA pr₁ pr₂ hsq hsurj
      hV' hV₂ hV'' _ _ _ _ k)

end Functor

end AlgebraicGeometry.Space

end
