module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Glueing
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# The relative spectrum of a quasi-coherent algebra

Let `S` be a scheme and `A` a quasi-coherent sheaf of commutative `𝒪_S`-algebras. For every
affine open `U` of `S` the ring of sections `A(U)` has an affine spectrum `Spec A(U)`, which
maps to `U`, and for nested affine opens `U ≤ V` the square

```
Spec A(V)  ⟵  Spec A(U)
   ↓              ↓
   V       ⟵      U
```

is cartesian. This file glues these affine spectra into a single scheme over `S`. The morphism
`Spec A(U) ⟶ U` is `Stacks.RelativeSpec.specSectionsToOpen`, from
`StacksFrontier.AlgebraicGeometry.RelativeSpec.Glueing`.

## Main definitions

* `Stacks.RelativeSpec.specSectionsMap` is the morphism `Spec A(U) ⟶ Spec A(V)` induced by an
  inclusion `U ≤ V` of opens of the base.
* `Stacks.RelativeSpec.RelativeSpectrum` is a scheme over the base together with charts from
  the affine spectra exhibiting it as their gluing.
* `Stacks.RelativeSpec.relativeSpectrum` constructs one.
* `Stacks.RelativeSpec.RelativeSpectrum.chartIso` identifies `Spec A(U)` with the inverse
  image of `U`, and `Stacks.RelativeSpec.RelativeSpectrum.cover` is the resulting open cover
  of the relative spectrum.
* `Stacks.RelativeSpec.RelativeSpectrum.isoComparison` is the isomorphism between two
  relative spectra of the same algebra.

## Main results

* `Stacks.RelativeSpec.RelativeSpectrum.chartIso_naturality` identifies the inclusion of one
  inverse image into another with restriction of sections of the algebra.
* `Stacks.RelativeSpec.RelativeSpectrum.glueCharts` maps out of a relative spectrum: a family
  of morphisms from the affine spectra compatible with restriction glues to a single morphism,
  and `Stacks.RelativeSpec.RelativeSpectrum.chart_glueCharts` computes it on each chart.
* `Stacks.RelativeSpec.RelativeSpectrum.hom_ext` says that two morphisms out of a relative
  spectrum agree as soon as they agree on every chart.
* `Stacks.RelativeSpec.existsUnique_relativeSpectrumIso` says that two relative spectra of the
  same algebra are uniquely isomorphic over the base, compatibly with all charts.

## Implementation notes

The gluing itself is `Stacks.AffineAlgebraEquivalence.relativeSpecGluingData`: Mathlib's
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData` applied to the cover of the base by *all*
its affine opens, `AlgebraicGeometry.Scheme.directedAffineCover`. That cover is locally
directed, so the relative gluing machinery applies verbatim once the cartesian squares of
`Stacks.RelativeSpec.isPullback_specMap_restriction` are packaged as an equifibered natural
transformation; the glued scheme is then a colimit and its structure morphism is the induced
map to the base. The charts are the colimit inclusions, and the two properties of the tag are
the cartesian squares of
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase` together with
the colimit relations.

The charts are indexed by all affine opens rather than by a chosen cover, which is what makes
`glueCharts` and `hom_ext` available without further hypotheses: the pullbacks of the base's
affine opens along the structure morphism already form an open cover of the relative spectrum,
and each member of it is identified with the corresponding affine spectrum by
`RelativeSpectrum.chartIso`.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u})

/-- The morphism of affine spectra induced by restriction of sections of the algebra along an
inclusion `U ≤ V` of opens of the base. -/
abbrev specSectionsMap {U V : s.base.Opens} (h : U ≤ V) :
    Spec (AlgebraSheaf.sections s.algebra U) ⟶ Spec (AlgebraSheaf.sections s.algebra V) :=
  Spec.map (s.algebra.right.obj.map (homOfLE h).op)

/-- A relative spectrum of a quasi-coherent algebra `A` on a scheme `S`: a scheme over `S`
together with a morphism from `Spec A(U)` for every affine open `U` of `S`, such that each of
these exhibits `Spec A(U)` as the inverse image of `U`, and such that they are compatible with
restriction of sections along inclusions of affine opens.

Such a datum is unique up to unique isomorphism over `S`, by
`Stacks.RelativeSpec.existsUnique_relativeSpectrumIso`, and one exists, by
`Stacks.RelativeSpec.relativeSpectrum`. -/
@[sga "3 VIB 3.8" "partial"]
structure RelativeSpectrum where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the base scheme. -/
  toBase : scheme ⟶ s.base
  /-- The chart from the affine spectrum over an affine open of the base. -/
  chart (U : s.base.affineOpens) : Spec (AlgebraSheaf.sections s.algebra U.1) ⟶ scheme
  /-- Each chart exhibits its affine spectrum as the inverse image of the affine open. -/
  chart_isPullback (U : s.base.affineOpens) :
    IsPullback (chart U) (specSectionsToOpen s U) toBase U.1.ι
  /-- The charts are compatible with restriction of sections. -/
  chart_naturality {U V : s.base.affineOpens} (h : U.1 ≤ V.1) :
    specSectionsMap s h ≫ chart V = chart U

/-- **Stacks Project, Tag 01LP**, existence. The affine spectra of the sections of a
quasi-coherent algebra glue to a scheme over the base, with the prescribed inverse images and
the prescribed transition morphisms.

The glued scheme and its structure morphism are
`Stacks.AffineAlgebraEquivalence.relativeSpec` and
`Stacks.AffineAlgebraEquivalence.relativeSpecToBase`; the content added here is that its
charts satisfy properties (1) and (2) of the tag. -/
@[stacks 01LP, ega "II 1.3.1" "existence", ega "IV 21.12.1" "more general", sga "3 I 4.2"]
def relativeSpectrum : RelativeSpectrum s where
  scheme := AffineAlgebraEquivalence.relativeSpec s.algebra
  toBase := AffineAlgebraEquivalence.relativeSpecToBase s.algebra
  chart U := colimit.ι (AffineAlgebraEquivalence.relativeSpecGluingData s.algebra).functor U
  chart_isPullback U :=
    ((AffineAlgebraEquivalence.relativeSpecGluingData
      s.algebra).isPullback_natTrans_ι_toBase U).flip
  chart_naturality h :=
    colimit.w (AffineAlgebraEquivalence.relativeSpecGluingData s.algebra).functor (homOfLE h)

/-- The structure morphism of the relative spectrum is an affine morphism. -/
instance : IsAffineHom (relativeSpectrum s).toBase :=
  AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase s.algebra

namespace RelativeSpectrum

variable {s} (X : RelativeSpectrum s)

/-- The open cover of a relative spectrum by the inverse images of the affine opens of the
base. Its member over an affine open `U` is identified with `Spec A(U)` by
`Stacks.RelativeSpec.RelativeSpectrum.chartIso`. -/
abbrev cover : X.scheme.OpenCover := s.base.directedAffineCover.pullback₁ X.toBase

/-- The identification of the affine spectrum of the sections over an affine open `U` of the
base with the inverse image of `U` in the relative spectrum. -/
def chartIso (U : s.base.affineOpens) :
    Spec (AlgebraSheaf.sections s.algebra U.1) ≅ pullback X.toBase U.1.ι :=
  (X.chart_isPullback U).isoPullback

/-- Composing `chartIso` with the first projection gives the chart. -/
@[simp]
lemma chartIso_hom_fst (U : s.base.affineOpens) :
    (X.chartIso U).hom ≫ pullback.fst X.toBase U.1.ι = X.chart U :=
  (X.chart_isPullback U).isoPullback_hom_fst

/-- Composing `chartIso` with the second projection gives `specSectionsToOpen`. -/
@[simp]
lemma chartIso_hom_snd (U : s.base.affineOpens) :
    (X.chartIso U).hom ≫ pullback.snd X.toBase U.1.ι = specSectionsToOpen s U :=
  (X.chart_isPullback U).isoPullback_hom_snd

/-- Each chart is an open immersion, being a base change of the inclusion of an affine open
of the base. -/
instance (U : s.base.affineOpens) : IsOpenImmersion (X.chart U) :=
  MorphismProperty.of_isPullback (X.chart_isPullback U).flip inferInstance

/-- Naturality of `Stacks.RelativeSpec.RelativeSpectrum.chartIso`: the inclusion of inverse
images induced by `U ≤ V` corresponds to restriction of sections of the algebra. -/
lemma chartIso_naturality {U V : s.base.affineOpens} (h : U.1 ≤ V.1) :
    (X.chartIso U).hom ≫ pullback.map X.toBase U.1.ι X.toBase V.1.ι (𝟙 X.scheme)
        (s.base.homOfLE h) (𝟙 s.base) (by simp) (by simp) =
      specSectionsMap s h ≫ (X.chartIso V).hom := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, chartIso_hom_fst]
    exact (X.chart_naturality h).symm
  · simp only [Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, chartIso_hom_snd, chartIso_hom_snd]
    exact (isPullback_specMap_restriction s U.1 V.1 U.2 V.2 h).w.symm

/-- Two morphisms out of a relative spectrum agree as soon as they agree after restriction to
the inverse image of every affine open of the base. -/
lemma pullbackFst_hom_ext {Z : Scheme.{u}} {f g : X.scheme ⟶ Z}
    (h : ∀ U : s.base.affineOpens,
      pullback.fst X.toBase U.1.ι ≫ f = pullback.fst X.toBase U.1.ι ≫ g) : f = g :=
  X.cover.hom_ext _ _ h

/-- The compatibility condition that lets a family of morphisms out of the affine spectra be
glued, transported to the inverse images of the affine opens. -/
lemma map_comp_chartIso_inv_comp {Z : Scheme.{u}}
    (g : ∀ U : s.base.affineOpens, Spec (AlgebraSheaf.sections s.algebra U.1) ⟶ Z)
    (hg : ∀ {U V : s.base.affineOpens} (h : U.1 ≤ V.1), specSectionsMap s h ≫ g V = g U)
    {U V : s.base.affineOpens} (h : U.1 ≤ V.1) :
    pullback.map X.toBase U.1.ι X.toBase V.1.ι (𝟙 X.scheme) (s.base.homOfLE h) (𝟙 s.base)
        (by simp) (by simp) ≫ (X.chartIso V).inv ≫ g V = (X.chartIso U).inv ≫ g U := by
  rw [← cancel_epi (X.chartIso U).hom, ← Category.assoc, X.chartIso_naturality h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hg h

/-- A family of morphisms out of the affine spectra of the sections of the algebra, compatible
with restriction of sections, glues to a single morphism out of the relative spectrum. -/
def glueCharts {Z : Scheme.{u}}
    (g : ∀ U : s.base.affineOpens, Spec (AlgebraSheaf.sections s.algebra U.1) ⟶ Z)
    (hg : ∀ {U V : s.base.affineOpens} (h : U.1 ≤ V.1), specSectionsMap s h ≫ g V = g U) :
    X.scheme ⟶ Z :=
  X.cover.glueMorphismsOfLocallyDirected (fun U => (X.chartIso U).inv ≫ g U)
    fun f => X.map_comp_chartIso_inv_comp g hg (leOfHom f)

/-- The glued morphism `glueCharts`, restricted to the inverse image of an affine open `U`, is the
given morphism out of `Spec A(U)` transported along `chartIso`. -/
lemma pullbackFst_comp_glueCharts {Z : Scheme.{u}}
    (g : ∀ U : s.base.affineOpens, Spec (AlgebraSheaf.sections s.algebra U.1) ⟶ Z)
    (hg : ∀ {U V : s.base.affineOpens} (h : U.1 ≤ V.1), specSectionsMap s h ≫ g V = g U)
    (U : s.base.affineOpens) :
    pullback.fst X.toBase U.1.ι ≫ X.glueCharts g hg = (X.chartIso U).inv ≫ g U :=
  X.cover.map_glueMorphismsOfLocallyDirected _
    (fun f => X.map_comp_chartIso_inv_comp g hg (leOfHom f)) U

/-- The glued morphism `glueCharts` restricts on each chart to the given morphism. -/
@[simp]
lemma chart_glueCharts {Z : Scheme.{u}}
    (g : ∀ U : s.base.affineOpens, Spec (AlgebraSheaf.sections s.algebra U.1) ⟶ Z)
    (hg : ∀ {U V : s.base.affineOpens} (h : U.1 ≤ V.1), specSectionsMap s h ≫ g V = g U)
    (U : s.base.affineOpens) : X.chart U ≫ X.glueCharts g hg = g U := by
  rw [← chartIso_hom_fst, Category.assoc, pullbackFst_comp_glueCharts, Iso.hom_inv_id_assoc]

/-- Two morphisms out of a relative spectrum that agree on every chart are equal. -/
lemma hom_ext {Z : Scheme.{u}} {f g : X.scheme ⟶ Z}
    (h : ∀ U : s.base.affineOpens, X.chart U ≫ f = X.chart U ≫ g) : f = g := by
  refine X.pullbackFst_hom_ext fun U => ?_
  rw [← cancel_epi (X.chartIso U).hom, ← Category.assoc, ← Category.assoc, chartIso_hom_fst]
  exact h U

/-- The structure morphism of a relative spectrum, read on the chart over an affine open `U`
of the base. -/
lemma chart_comp_toBase (U : s.base.affineOpens) :
    X.chart U ≫ X.toBase = specSectionsToOpen s U ≫ U.1.ι :=
  (X.chart_isPullback U).w

variable (Y : RelativeSpectrum s)

/-- The comparison morphism between two relative spectra of the same quasi-coherent algebra,
characterised by compatibility with the charts. -/
def comparison : X.scheme ⟶ Y.scheme :=
  X.glueCharts Y.chart fun h => Y.chart_naturality h

/-- The comparison morphism carries each chart of `X` to the corresponding chart of `Y`. -/
@[simp]
lemma chart_comparison (U : s.base.affineOpens) :
    X.chart U ≫ X.comparison Y = Y.chart U :=
  X.chart_glueCharts _ _ U

/-- The comparison morphism from `X` to `Y` followed by the one from `Y` to `X` is the identity. -/
lemma comparison_comp_comparison : X.comparison Y ≫ Y.comparison X = 𝟙 X.scheme :=
  X.hom_ext fun U => by
    rw [← Category.assoc, chart_comparison, chart_comparison, Category.comp_id]

/-- The canonical isomorphism between two relative spectra of the same quasi-coherent
algebra. -/
@[simps]
def isoComparison : X.scheme ≅ Y.scheme where
  hom := X.comparison Y
  inv := Y.comparison X
  hom_inv_id := X.comparison_comp_comparison Y
  inv_hom_id := Y.comparison_comp_comparison X

/-- The comparison morphism is a morphism over the base. -/
@[simp]
lemma comparison_comp_toBase : X.comparison Y ≫ Y.toBase = X.toBase :=
  X.hom_ext fun U => by
    rw [← Category.assoc, chart_comparison, chart_comp_toBase, chart_comp_toBase]

end RelativeSpectrum

/-- **Stacks Project, Tag 01LP**, uniqueness. Any two relative spectra of the same
quasi-coherent algebra admit a unique isomorphism over the base compatible with all the
charts. -/
@[stacks 01LP]
theorem existsUnique_relativeSpectrumIso (X Y : RelativeSpectrum s) :
    ∃! e : X.scheme ≅ Y.scheme,
      (e.hom ≫ Y.toBase = X.toBase) ∧ ∀ U, X.chart U ≫ e.hom = Y.chart U :=
  ⟨X.isoComparison Y, ⟨X.comparison_comp_toBase Y, X.chart_comparison Y⟩, fun _ he' =>
    Iso.ext <| X.hom_ext fun U => (he'.2 U).trans (X.chart_comparison Y U).symm⟩

end Stacks.RelativeSpec

end
