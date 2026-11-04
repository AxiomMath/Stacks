module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePreimageGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum, glued from its affine charts

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras. The
affine spectra `Spec A(U)`, for `U` an affine open of `S`, glue to a scheme `π : X ⟶ S` whose
fibre over each affine open `U` is `Spec A(U)`, compatibly with inclusions of affine opens.
This file packages that data and shows that it exists and is unique up to a unique isomorphism
over `S`.

## Main definitions

* `Stacks.RelativeSpec.GluedSpectrum` is a scheme over the base together with the compatible
  identifications of the inverse image of each affine open `U` with `Spec A(U)`.
* `Stacks.RelativeSpec.gluedSpectrum` is the relative spectrum, carrying this data.
* `Stacks.RelativeSpec.GluedSpectrum.chartIso` and
  `Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage` present a chart as the fibre product
  `X ×_S U`, respectively as the open subscheme `π⁻¹(U)`.

## Main results

* `Stacks.RelativeSpec.GluedSpectrum.chartIsoPreimage_hom_comp_morphismRestrict`: read through
  that identification, the structure morphism restricted over `U` is
  `Stacks.RelativeSpec.specSectionsToOpen`.
* `Stacks.RelativeSpec.existsUnique_gluedSpectrumIso`: any two schemes carrying this data are
  related by a unique isomorphism over the base compatible with all the charts.

## Implementation notes

The identification of `Spec A(U)` with the inverse image `π⁻¹(U)` is expressed as a cartesian
square with `Spec A(U)` in the upper left corner, so that no inverse has to be named; in this
form the compatibility with inclusions of affine opens is the naturality of the chart maps,
which for the glued scheme is the colimit relation.

The scheme is `Stacks.AffineAlgebraEquivalence.relativeSpec`, the colimit of the relative
gluing datum over the cover of `S` by all its affine opens; the charts are the colimit
inclusions and the cartesian squares are
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase`.

For uniqueness, a morphism between two such schemes is glued from the chartwise comparison
isomorphisms over the cover of the source by the inverse images of the affine opens of the
base, which is locally directed because the affine opens are. The two composites are the
identity because they are so on each chart.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

/-- The canonical morphism from the spectrum of the sections of the algebra over an affine open
`U` of the base to the open subscheme `U`, given by the structure morphism of the algebra
followed by the identification of `U` with the spectrum of its sections. -/
noncomputable abbrev specSectionsToOpen (s : RelativeSpecSituation.{u})
    (U : s.base.affineOpens) : Spec (s.algebra.sections U.1) ⟶ U.1.toScheme :=
  Spec.map (s.algebra.hom.hom.app (.op U.1)) ≫ U.2.isoSpec.inv

/-- A scheme over the base of a relative-spectrum situation, presented by its charts from the
affine spectra of the sections of the algebra over the affine opens of the base. The cartesian
squares identify each chart with the inverse image of its affine open, and `chart_naturality`
identifies the inclusion of one inverse image into another with the spectrum of the
restriction map of the algebra. -/
structure GluedSpectrum (s : RelativeSpecSituation.{u}) where
  /-- The scheme obtained by gluing the affine spectra. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the base scheme. -/
  toBase : scheme ⟶ s.base
  /-- The chart from the spectrum of the sections over an affine open of the base. -/
  chart (U : s.base.affineOpens) : Spec (s.algebra.sections U.1) ⟶ scheme
  /-- Each chart is the inverse image of its affine open in the base. -/
  chart_isPullback (U : s.base.affineOpens) :
    IsPullback (chart U) (specSectionsToOpen s U) toBase U.1.ι
  /-- The charts commute with the open immersions induced by restriction of sections along an
  inclusion of affine opens. -/
  chart_naturality {U V : s.base.affineOpens} (h : U.1 ≤ V.1) :
    Spec.map (s.algebra.right.obj.map (homOfLE h).op) ≫ chart V = chart U

/-- **Stacks Project, Tag 01LP, parts (1) and (2).** The affine spectra of the sections of a
quasi-coherent algebra glue to a scheme over the base, with the prescribed inverse images and
transition open immersions. -/
@[stacks 01LP "existence and local properties", ega "II 1.3.1" "existence", sga "3 I 4.2"]
noncomputable def gluedSpectrum (s : RelativeSpecSituation.{u}) : GluedSpectrum s where
  scheme := relativeSpec s.algebra
  toBase := relativeSpecToBase s.algebra
  chart U := colimit.ι (relativeSpecGluingData s.algebra).functor U
  chart_isPullback U :=
    ((relativeSpecGluingData s.algebra).isPullback_natTrans_ι_toBase U).flip
  chart_naturality h := colimit.w (relativeSpecGluingData s.algebra).functor (homOfLE h)

/-- The scheme of `Stacks.RelativeSpec.gluedSpectrum` is
`Stacks.AffineAlgebraEquivalence.relativeSpec`. -/
@[simp]
lemma gluedSpectrum_scheme (s : RelativeSpecSituation.{u}) :
    (gluedSpectrum s).scheme = relativeSpec s.algebra := rfl

/-- The structure morphism of `Stacks.RelativeSpec.gluedSpectrum` is the structure morphism of
the relative gluing datum. -/
@[simp]
lemma gluedSpectrum_toBase (s : RelativeSpecSituation.{u}) :
    (gluedSpectrum s).toBase = (relativeSpecGluingData s.algebra).toBase := rfl

/-- The chart of `Stacks.RelativeSpec.gluedSpectrum` over an affine open `U` is the colimit
inclusion at `U`. -/
@[simp]
lemma gluedSpectrum_chart (s : RelativeSpecSituation.{u}) (U : s.base.affineOpens) :
    (gluedSpectrum s).chart U = colimit.ι (relativeSpecGluingData s.algebra).functor U := rfl

namespace GluedSpectrum

variable {s : RelativeSpecSituation.{u}} (X Y : GluedSpectrum s)

/-- The comparison of a chart with the fibre product defining the inverse image of its affine
open. -/
noncomputable def chartIso (U : s.base.affineOpens) :
    Spec (s.algebra.sections U.1) ≅ pullback X.toBase U.1.ι :=
  (X.chart_isPullback U).isoPullback

/-- The comparison `chartIso`, followed by the first projection, is the chart. -/
@[reassoc]
lemma chartIso_hom_fst (U : s.base.affineOpens) :
    (X.chartIso U).hom ≫ pullback.fst X.toBase U.1.ι = X.chart U :=
  (X.chart_isPullback U).isoPullback_hom_fst

/-- The comparison `chartIso`, followed by the second projection, is
`Stacks.RelativeSpec.specSectionsToOpen`. -/
@[reassoc]
lemma chartIso_hom_snd (U : s.base.affineOpens) :
    (X.chartIso U).hom ≫ pullback.snd X.toBase U.1.ι =
      specSectionsToOpen s U :=
  (X.chart_isPullback U).isoPullback_hom_snd

/-- A chart, followed by the structure morphism, is the structure morphism of the algebra
followed by the inclusion of its affine open. -/
lemma chart_comp_toBase (U : s.base.affineOpens) :
    X.chart U ≫ X.toBase =
      Spec.map (s.algebra.hom.hom.app (.op U.1)) ≫ U.2.isoSpec.inv ≫ U.1.ι :=
  (X.chart_isPullback U).w.trans (Category.assoc _ _ _)

/-- A chart lies entirely over its affine open of the base. -/
lemma chart_preimage (U : s.base.affineOpens) :
    X.chart U ⁻¹ᵁ (X.toBase ⁻¹ᵁ U.1) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, (X.chart_isPullback U).w, Scheme.Hom.comp_preimage,
    U.1.ι_preimage_self, Scheme.Hom.preimage_top]

/-- The sections of a chart: the restriction of a chart to the sections over the inverse image
of its affine open. -/
noncomputable abbrev chartAppLE (U : s.base.affineOpens) :
    Γ(X.scheme, X.toBase ⁻¹ᵁ U.1) ⟶ Γ(Spec (s.algebra.sections U.1), ⊤) :=
  (X.chart U).appLE (X.toBase ⁻¹ᵁ U.1) ⊤ (X.chart_preimage U).ge

/-- Each chart is an open immersion. -/
instance chart_isOpenImmersion (U : s.base.affineOpens) : IsOpenImmersion (X.chart U) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (X.chart_isPullback U).flip inferInstance

/-- A chart identifies the spectrum of the sections over an affine open `U` of the base with the
open subscheme `π⁻¹(U)`. -/
noncomputable def chartIsoPreimage (U : s.base.affineOpens) :
    Spec (s.algebra.sections U.1) ≅ (X.toBase ⁻¹ᵁ U.1).toScheme :=
  X.chartIso U ≪≫ (Scheme.preimageIsoPullback X.toBase U.1).symm

/-- The identification `chartIsoPreimage`, followed by the inclusion of `π⁻¹(U)`, is the
chart. -/
@[reassoc]
lemma chartIsoPreimage_hom_ι (U : s.base.affineOpens) :
    (X.chartIsoPreimage U).hom ≫ (X.toBase ⁻¹ᵁ U.1).ι = X.chart U := by
  rw [chartIsoPreimage, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Scheme.preimageIsoPullback_inv_comp_ι, chartIso_hom_fst]

/-- **A chart, read as the inverse image of its affine open, lies over that open as the spectrum
of the structure map of the algebra**: the identification of `Spec A(U)` with `π⁻¹(U)`, followed
by the restriction of the structure morphism over `U`, is
`Stacks.RelativeSpec.specSectionsToOpen`. -/
@[reassoc]
lemma chartIsoPreimage_hom_comp_morphismRestrict (U : s.base.affineOpens) :
    (X.chartIsoPreimage U).hom ≫ X.toBase ∣_ U.1 = specSectionsToOpen s U := by
  rw [← cancel_mono U.1.ι, Category.assoc, morphismRestrict_ι,
    X.chartIsoPreimage_hom_ι_assoc, X.chart_comp_toBase]
  exact (Category.assoc _ _ _).symm

/-- The inverse of `chartIso`, followed by the chart, is the first projection of the fibre
product. -/
@[reassoc]
lemma chartIso_inv_comp_chart (U : s.base.affineOpens) :
    (X.chartIso U).inv ≫ X.chart U = pullback.fst X.toBase U.1.ι := by
  rw [← X.chartIso_hom_fst U, Iso.inv_hom_id_assoc]

/-- The charts are compatible with the canonical maps between the fibre products. -/
lemma chartIso_naturality {U V : s.base.affineOpens} (h : U.1 ≤ V.1) :
    (X.chartIso U).hom ≫
        pullback.map X.toBase U.1.ι X.toBase V.1.ι (𝟙 X.scheme) (s.base.homOfLE h)
          (𝟙 s.base) (by simp) (by simp) =
      Spec.map (s.algebra.right.obj.map (homOfLE h).op) ≫ (X.chartIso V).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, chartIso_hom_fst,
      Category.assoc, chartIso_hom_fst, X.chart_naturality h]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, chartIso_hom_snd,
      Category.assoc, chartIso_hom_snd]
    exact (isPullback_specMap_restriction s U.1 V.1 U.2 V.2 h).w.symm

private lemma compare_compatible :
    ∀ (U V : s.base.affineOpens) (h : U.1 ≤ V.1),
      pullback.map X.toBase U.1.ι X.toBase V.1.ι (𝟙 X.scheme) (s.base.homOfLE h) (𝟙 s.base)
          (by simp) (by simp) ≫ ((X.chartIso V).inv ≫ Y.chart V) =
        (X.chartIso U).inv ≫ Y.chart U := by
  intro U V h
  apply (cancel_epi (X.chartIso U).hom).mp
  rw [← Category.assoc, X.chartIso_naturality h, Category.assoc, Iso.hom_inv_id_assoc,
    Y.chart_naturality h, Iso.hom_inv_id_assoc]

/-- The comparison morphism between two schemes carrying the chart data, glued over the cover
of the source by the inverse images of the affine opens of the base. -/
private noncomputable def compare : X.scheme ⟶ Y.scheme :=
  Scheme.glueOverAffinePullbacks X.toBase (fun U => (X.chartIso U).inv ≫ Y.chart U)
    (X.compare_compatible Y)

private lemma chart_comp_compare (U : s.base.affineOpens) :
    X.chart U ≫ X.compare Y = Y.chart U := by
  rw [← X.chartIso_hom_fst U, Category.assoc, compare,
    Scheme.fst_comp_glueOverAffinePullbacks, Iso.hom_inv_id_assoc]

private lemma hom_ext {Z : Scheme.{u}} {f g : X.scheme ⟶ Z}
    (h : ∀ U, X.chart U ≫ f = X.chart U ≫ g) : f = g := by
  refine Scheme.hom_ext_of_affinePullbacks X.toBase fun U => ?_
  rw [← X.chartIso_inv_comp_chart U, Category.assoc, Category.assoc, h]

private lemma compare_comp_compare : X.compare Y ≫ Y.compare X = 𝟙 X.scheme :=
  X.hom_ext fun U => by
    rw [← Category.assoc, chart_comp_compare, chart_comp_compare, Category.comp_id]

/-- **Stacks Project, Tag 01LP, uniqueness.** Any two schemes over the base carrying the affine
charts of the relative spectrum admit a unique isomorphism over the base that respects all the
charts. -/
@[stacks 01LP "uniqueness"]
theorem _root_.Stacks.RelativeSpec.existsUnique_gluedSpectrumIso
    (s : RelativeSpecSituation.{u}) (X Y : GluedSpectrum s) :
    ∃! e : X.scheme ≅ Y.scheme,
      (e.hom ≫ Y.toBase = X.toBase) ∧ (∀ U, X.chart U ≫ e.hom = Y.chart U) := by
  refine ⟨⟨X.compare Y, Y.compare X, X.compare_comp_compare Y, Y.compare_comp_compare X⟩,
    ⟨?_, X.chart_comp_compare Y⟩, fun e he => ?_⟩
  · refine X.hom_ext fun U => ?_
    rw [← Category.assoc, chart_comp_compare]
    exact (Y.chart_isPullback U).w.trans (X.chart_isPullback U).w.symm
  · exact Iso.ext (X.hom_ext fun U => (he.2 U).trans (X.chart_comp_compare Y U).symm)

end GluedSpectrum

end Stacks.RelativeSpec

end
