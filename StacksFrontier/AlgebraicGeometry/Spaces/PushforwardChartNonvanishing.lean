module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartNonvanishingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Sections of a direct image cover the nonvanishing loci on a cartesian chart

Let `f : X ⟶ U` be a morphism of algebraic spaces and `P` an `𝒪_X`-module whose direct image
`f_*P` is quasi-coherent. Let `j : V' ⟶ V` be a morphism of affine étale charts of `U`, and let
the étale chart `W` of `X` represent `X ×_U V'`. Then every point of the scheme of `W` at which
some section of `P` over `W` does not vanish is a point at which the image in `P(W)` of some
section of `f_*P` over `V` does not vanish.

Indeed the sections of `P` over the cartesian chart `W` are the sections of `f_*P` over `V'`
(`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback`), and these are the
base change of the sections over `V`, `f_*P` being cartesian on affine charts (Stacks 03DX (2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`). So a section over
`W` is a linear combination of images of sections over `V`, and a linear combination can only fail
to vanish where one of its terms does.

This is the covering step of the proof of [Stacks, Tag 0D35], with `V' ⟶ V` the given
surjective étale morphism of affine schemes `V ⟶ U`, `P = L^{⊗ n}` and `W = Y = V ×_U X`: the
sections of `f_*P` over `U` are the sections of `L^{⊗ n}` on `X`.

## Main results

* `AlgebraicGeometry.Space.nonvanishingLocus_subset_iUnion_modulePushforwardCounitApp`: the
  statement above.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The commutativity of the chart diagram obtained by composing with a morphism of charts of
the target. -/
theorem chartDiagram_comm_comp {X U : AlgebraicSpaces B S hS} (f : X ⟶ U)
    {W : SmallEtale B S hS X.1} {V' V : SmallEtale B S hS U.1} (j : V' ⟶ V)
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS U.1).obj V')
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V'.1.hom) :
    W.1.hom ≫ f.hom = yoneda.map (b ≫ (SmallEtale.toOver B S hS U.1).map j) ≫ V.1.hom := by
  rw [hb, Functor.map_comp, Category.assoc]
  exact congrArg (yoneda.map b ≫ ·) (CostructuredArrow.w j.hom).symm

/-- **On a cartesian chart, the images of the sections of a quasi-coherent direct image cover
the nonvanishing loci.** See the module documentation. -/
theorem nonvanishingLocus_subset_iUnion_modulePushforwardCounitApp {X U : AlgebraicSpaces B S hS}
    (f : X ⟶ U) (P : Modules.{u, u} B S hS X.1 X.2) [P.IsQuasicoherentOnSite]
    (hfP : ((modulePushforward B S hS f).obj P).IsQuasicoherentOnSite)
    {V' V : SmallEtale B S hS U.1} (j : V' ⟶ V) (hV' : IsAffine (chartScheme V'))
    (hV : IsAffine (chartScheme V)) (W : SmallEtale B S hS X.1)
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS U.1).obj V')
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V'.1.hom)
    (hcart : IsPullback W.1.hom (yoneda.map b) f.hom V'.1.hom) (p : P.val.obj (op W)) :
    Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X P W)
        (chartRestrictionTopSection B S hS X P W p) ⊆
      ⋃ n : ((modulePushforward B S hS f).obj P).val.obj (op V),
        Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X P W)
          (chartRestrictionTopSection B S hS X P W
            (modulePushforwardCounitApp B S hS f P
              ⟨W, V, b ≫ (SmallEtale.toOver B S hS U.1).map j,
                chartDiagram_comm_comp f j b hb⟩ n)) := by
  set G := (modulePushforward B S hS f).obj P
  let e : ChartDiagram B S hS X.1 U.1 f.hom := ⟨W, V', b, hb⟩
  let d : ChartDiagram B S hS X.1 U.1 f.hom :=
    ⟨W, V, b ≫ (SmallEtale.toOver B S hS U.1).map j, chartDiagram_comm_comp f j b hb⟩
  obtain ⟨n', rfl⟩ := (bijective_modulePushforwardCounitApp_of_isPullback B S hS f P e hcart).2 p
  obtain ⟨t, rfl⟩ := (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS U.1 U.2 G hfP
    V V' hV hV' j).2 n'
  -- the image of a restricted section is the image of the section
  have hres (n : G.val.obj (op V)) : modulePushforwardCounitApp B S hS f P e
      (chartRestrictLinear G j n) = modulePushforwardCounitApp B S hS f P d n :=
    (modulePushforwardCounitApp_naturality B S hS f P d e (𝟙 W) j
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp]) n).trans
      (ConcreteCategory.congr_hom (P.val.presheaf.map_id _) _)
  let := chartAlgebra (hF := U.2) j
  induction t using TensorProduct.inductionOn with
  | tmul c n =>
    rw [chartBaseChange_tmul, modulePushforwardCounitApp_smul, hres]
    exact (nonvanishingLocus_chartRestrictionTopSection_smul_subset B S hS X P W _ _).trans
      (Set.subset_iUnion_of_subset n le_rfl)
  | add t t' ht ht' =>
    rw [map_add, modulePushforwardCounitApp_add]
    exact (nonvanishingLocus_chartRestrictionTopSection_add_subset B S hS X P W _ _).trans
      (Set.union_subset ht ht')

end AlgebraicGeometry.Space

end
