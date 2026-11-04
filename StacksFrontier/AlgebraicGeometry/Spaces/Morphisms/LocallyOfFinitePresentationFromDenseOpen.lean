module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen

/-!
# Local finite presentation of a morphism of algebraic spaces from a dense open of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite type and flat, and let `V ⊆ Y` be an open subspace whose inclusion is
quasi-compact and scheme-theoretically dense.  If the restriction `f⁻¹V ⟶ V` of `f` is locally
of finite presentation, then `f` is locally of finite presentation.  This is Stacks 0877, the
algebraic-space form of Stacks 081P.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.locallyOfFinitePresentation_chartDiagram_of_fromPreimage` is
  **Stacks 0877** read on one commuting square of étale scheme charts, and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_fromPreimage` is Stacks 0877 itself.

## Implementation notes

Local finite presentation of a morphism of algebraic spaces is the every-étale-chart condition of
Tag 03MJ, so the conclusion is an assertion about an arbitrary commuting square of étale scheme
charts of `f`, and on such a square it is exactly Stacks 081P for the vertical morphism of
schemes: that morphism is flat and locally of finite type because `f` is, and the open subscheme
of the chart of `Y` cut out by `V` is retrocompact and scheme-theoretically dense by
`AlgebraicGeometry.Space.isRetrocompactOnCharts_of_isQuasiCompact` (Tag 03HD) and
`AlgebraicGeometry.Space.isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense`
(Tag 0836).  That is the same translation of the hypotheses on `V` that Stacks 0876 uses in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FinitePresentationFromDenseOpen.lean`.

What this file adds over that translation is the reading of the hypothesis on `f⁻¹V ⟶ V`.  The
restriction of `f` to the inverse image of `V` is `CategoryTheory.Subfunctor.fromPreimage`, and a
commuting square of étale charts of `f` is restricted to one of `f⁻¹V ⟶ V` by base change along
the two inclusions: the inverse image of `V` in the chart of `Y` is represented by the open
immersion `hV.2.rep.snd`, the inverse image of `f⁻¹V` in the chart of `X` by `hVf.2.rep.snd`,
and the morphism between them is the lift supplied by the first representing pullback square.
The images of those two open immersions are the chart-level `V` and `f⁻¹V`, by
`AlgebraicGeometry.Space.opensRange_snd_eq_chartOpenOfOpenSubspace` and
`AlgebraicGeometry.Space.preimage_chartOpenOfOpenSubspace`, so the vertical morphism of the
restricted square is the restriction of the vertical morphism of the original square, up to the
isomorphisms identifying an open immersion of schemes with the inclusion of its image.

That the inverse image of an open subspace is again one is Tag 083Q,
`AlgebraicGeometry.Space.isOpenSubspace_preimage`, which is why the source and target are
required to be algebraic spaces here, as they are in the source.

## References

* [Stacks Project, Tag 0877](https://stacks.math.columbia.edu/tag/0877)
* [Stacks Project, Tag 081P](https://stacks.math.columbia.edu/tag/081P)
* [Stacks Project, Tag 0876](https://stacks.math.columbia.edu/tag/0876)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A commuting square of schemes whose two vertical morphisms are open immersions with images an
open `W` of the target and its inverse image in the source computes the restriction of the
horizontal morphism to `W`: each vertical morphism is identified with the inclusion of its image,
and the horizontal morphism of the square becomes that restriction. -/
private theorem locallyOfFinitePresentation_morphismRestrict_of_opensRange
    {A A' Z Z' : Scheme.{u}} (g : Z ⟶ Z') (W : Z'.Opens)
    (ir : A ⟶ Z) (ip : A' ⟶ Z')
    [AlgebraicGeometry.IsOpenImmersion ir] [AlgebraicGeometry.IsOpenImmersion ip]
    (g' : A ⟶ A') (hsq : ir ≫ g = g' ≫ ip)
    (hp : ip.opensRange = W) (hr : ir.opensRange = g ⁻¹ᵁ W)
    [LocallyOfFinitePresentation g'] :
    LocallyOfFinitePresentation (g ∣_ W) := by
  have her : Set.range ir.base = Set.range (g ⁻¹ᵁ W).ι.base := by
    simp only [← Scheme.Hom.coe_opensRange, hr, Scheme.Opens.opensRange_ι]
  have hep : Set.range ip.base = Set.range W.ι.base := by
    simp only [← Scheme.Hom.coe_opensRange, hp, Scheme.Opens.opensRange_ι]
  let er := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ir (g ⁻¹ᵁ W).ι her
  let ep := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ip W.ι hep
  have herf : er.hom ≫ (g ⁻¹ᵁ W).ι = ir :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ her
  have hepf : ep.hom ≫ W.ι = ip :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hep
  have hkey : g ∣_ W = er.inv ≫ g' ≫ ep.hom := by
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, Category.assoc, hepf,
      ← hsq, ← herf]
    simp
  rw [hkey]
  infer_instance

open AlgebraicGeometry.FinitePresentationFromDenseOpen in
/-- **Stacks 0877, on one commuting square of étale scheme charts.** For `f : X ⟶ Y` locally of
finite type and flat and `V ⊆ Y` an open subspace whose inclusion is quasi-compact and
scheme-theoretically dense, with `f⁻¹V ⟶ V` locally of finite presentation, the morphism of
schemes underlying any commuting square of étale charts of `f` is locally of finite
presentation.

This is Stacks 081P for that morphism of schemes: the open subscheme of the chart of `Y` cut out
by `V` is retrocompact and scheme-theoretically dense, and the restriction of the morphism to it
is, up to isomorphism, the morphism of schemes underlying the square of charts of `f⁻¹V ⟶ V`
obtained by base change along the two inclusions. -/
theorem locallyOfFinitePresentation_chartDiagram_of_fromPreimage
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f) (hflat : IsFlat B S hS f)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompact B S hS V.ι)
    (hVdense : IsSchemeTheoreticallyDense B S hS V)
    (hfV : IsLocallyOfFinitePresentation B S hS (V.fromPreimage f))
    (d : ChartDiagram B S hS X Y f) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map d.g) := by
  have hVf : IsOpenSubspace B S hS (V.preimage f) :=
    isOpenSubspace_preimage B S hS f V hY hX hV
  have hcpb : IsPullback (hV.2.rep.fst d.V.obj.hom)
      (yoneda.map (hV.2.rep.snd d.V.obj.hom)) V.ι d.V.obj.hom :=
    hV.2.rep.isPullback d.V.obj.hom
  have harb : IsPullback (hVf.2.rep.fst d.U.obj.hom)
      (yoneda.map (hVf.2.rep.snd d.U.obj.hom)) (V.preimage f).ι d.U.obj.hom :=
    hVf.2.rep.isPullback d.U.obj.hom
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hcE := hbc.of_isPullback hcpb.flip d.V.property
  have haE := hbc.of_isPullback harb.flip d.U.property
  have hi : (hVf.2.rep.fst d.U.obj.hom ≫ V.fromPreimage f) ≫ V.ι =
      yoneda.map (hVf.2.rep.snd d.U.obj.hom ≫ d.g) ≫ d.V.obj.hom :=
    calc (hVf.2.rep.fst d.U.obj.hom ≫ V.fromPreimage f) ≫ V.ι
        = (hVf.2.rep.fst d.U.obj.hom ≫ (V.preimage f).ι) ≫ f := by
          simp only [Category.assoc, Subfunctor.fromPreimage_ι]
      _ = (yoneda.map (hVf.2.rep.snd d.U.obj.hom) ≫ d.U.obj.hom) ≫ f := by rw [harb.w]
      _ = yoneda.map (hVf.2.rep.snd d.U.obj.hom) ≫ yoneda.map d.g ≫ d.V.obj.hom := by
          rw [Category.assoc, d.comm]
      _ = yoneda.map (hVf.2.rep.snd d.U.obj.hom ≫ d.g) ≫ d.V.obj.hom := by
          simp only [Functor.map_comp, Category.assoc]
  have hlift_fst := hV.2.rep.lift_fst
    (hVf.2.rep.fst d.U.obj.hom ≫ V.fromPreimage f) (hVf.2.rep.snd d.U.obj.hom ≫ d.g) hi
  have hlift_snd := hV.2.rep.lift_snd
    (hVf.2.rep.fst d.U.obj.hom ≫ V.fromPreimage f) (hVf.2.rep.snd d.U.obj.hom ≫ d.g) hi
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d.g) :=
    hlft d.U.obj.left d.V.obj.left d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property
      d.comm.symm
  have : Flat ((BigFppfOver.toScheme B S hS).map d.g) :=
    hflat d.U.obj.left d.V.obj.left d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property
      d.comm.symm
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (hV.2.rep.lift (hVf.2.rep.fst d.U.obj.hom ≫ V.fromPreimage f)
        (hVf.2.rep.snd d.U.obj.hom ≫ d.g) hi)) :=
    hfV _ _ (hVf.2.rep.fst d.U.obj.hom) (hV.2.rep.fst d.V.obj.hom) _ haE hcE hlift_fst
  have : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd d.V.obj.hom)) :=
    hV.2.property_snd d.V.obj.hom
  have : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hVf.2.rep.snd d.U.obj.hom)) :=
    hVf.2.property_snd d.U.obj.hom
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map d.g ∣_
      chartOpenOfOpenSubspace B S hS V hV d.V) :=
    locallyOfFinitePresentation_morphismRestrict_of_opensRange
      ((BigFppfOver.toScheme B S hS).map d.g) (chartOpenOfOpenSubspace B S hS V hV d.V)
      ((BigFppfOver.toScheme B S hS).map (hVf.2.rep.snd d.U.obj.hom))
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd d.V.obj.hom)) _
      (by rw [← Functor.map_comp, ← Functor.map_comp, hlift_snd])
      (opensRange_snd_eq_chartOpenOfOpenSubspace B S hS V hV d.V)
      ((opensRange_snd_eq_chartOpenOfOpenSubspace B S hS (V.preimage f) hVf d.U).trans
        (preimage_chartOpenOfOpenSubspace B S hS V hV hVf d).symm)
  exact locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open
    ((BigFppfOver.toScheme B S hS).map d.g) (chartOpenOfOpenSubspace B S hS V hV d.V)
    (isRetrocompactOnCharts_of_isQuasiCompact B S hS V hV hVqc d.V)
    (isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense B S hS V hV hVdense d.V)

/-- **Stacks 0877.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B` which is locally of finite type and flat, and let `V ⊆ Y` be an
open subspace whose inclusion is quasi-compact and which is scheme-theoretically dense in the
sense of Tag 0834.  If the restriction `f⁻¹V ⟶ V` of `f` is locally of finite presentation, then
`f` is locally of finite presentation.

Local finite presentation is the every-étale-chart condition of Tag 03MJ, so this is
`AlgebraicGeometry.Space.locallyOfFinitePresentation_chartDiagram_of_fromPreimage` for the
commuting square of charts given by the chart data. -/
@[stacks 0877]
theorem isLocallyOfFinitePresentation_of_fromPreimage
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f) (hflat : IsFlat B S hS f)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompact B S hS V.ι)
    (hVdense : IsSchemeTheoreticallyDense B S hS V)
    (hfV : IsLocallyOfFinitePresentation B S hS (V.fromPreimage f)) :
    IsLocallyOfFinitePresentation B S hS f := fun _C _D a b g ha hb hcomm =>
  locallyOfFinitePresentation_chartDiagram_of_fromPreimage B S hS hX hY f hlft hflat V hV hVqc
    hVdense hfV
    { U := ⟨CostructuredArrow.mk a, ha⟩
      V := ⟨CostructuredArrow.mk b, hb⟩
      g := g
      comm := hcomm.symm }

end AlgebraicGeometry.Space

end
