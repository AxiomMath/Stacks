module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartModule
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartRestriction
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.TwoTermComplex.DeterminantObjectBaseChange

/-!
# The determinant of a two-term perfect complex is compatible with change of chart

Let `X` be a scheme and let `L` be a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`.
Every affine open `V` of `X` carries the determinant
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` of `L` on the chart of `V`. This file produces
**the comparison isomorphism identifying the determinant on the chart of `V` with the
restriction to `V` of the determinant on the chart of a larger affine open `W`**, first as an
isomorphism of `Γ(X, V)`-modules, then as an isomorphism of sheaves of modules on the spectra,
and finally in the shape the glueing datum
`AlgebraicGeometry.AffineOpensGlue.ChartComparison` asks for.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.detLinearEquivOfIso`: the determinant of an isomorphism
  of perfect two-term complexes, read as a linear equivalence of determinant modules.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso`: **the chart comparison over the
  rings**: the base change along `Γ(X, W) → Γ(X, V)` of the determinant of `L` on the chart of
  `W` is the determinant of `L` on the chart of `V`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso`: **the chart comparison on the
  spectra**: the pullback along `Spec ρ` of `chartDetSpec L W` is `chartDetSpec L V`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`: the chart comparison on the open
  subschemes: `chartDet L V` is the restriction of `chartDet L W` along `X.homOfLE h`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetComp`: **the comparison in the shape the glueing
  datum wants**, the `comp` field of `AlgebraicGeometry.AffineOpensGlue.ChartComparison` for the
  family `chartDet L`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec_eq_tilde`: the determinant of `L` on the
  chart of an affine open is the sheaf associated with the determinant of
  `AlgebraicGeometry.DeterminantTwoTerm.chartComplex` there.
* `AlgebraicGeometry.DeterminantTwoTerm.isoSpec_hom_specMap_chartRestriction`: the two charts of
  an inclusion of affine opens form a commuting square with `Spec ρ` and `X.homOfLE h`.

## Implementation notes

The comparison is assembled over the rings first. Over `Γ(X, V)` there are two determinant
modules to compare: the base change of `det(K_W)` and `det(K_V)`. The first is reached by
`TwoTermDeterminant.detBaseChange`, which needs flatness of `ρ : Γ(X, W) → Γ(X, V)` — that is
`AlgebraicGeometry.IsAffineOpen.moduleFlat_presheaf_map` — and lands at the determinant of the
*derived extension of scalars* of `K_W`; the second is reached from it by the determinant of
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso`, read backwards, since that
isomorphism runs from `K_V` to the derived extension of scalars of `K_W`.

Passing from modules to sheaves is Tag 01I9, `AlgebraicGeometry.pullbackTildeIso`: the pullback
along `Spec ρ` of the sheaf associated with an `Γ(X, W)`-module is the sheaf associated with its
extension of scalars. The determinant on a chart is literally such an associated sheaf, by
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec_eq_tilde`, which holds by definitional
unfolding of `specDet`, `affineDet` and `tildeInvertible`.

The glueing datum of `StacksFrontier/AlgebraicGeometry/AffineOpensDirectedGlue.lean` asks for a
comparison between the restrictions to `V` of the *pushforwards* to `X` of the two members. Both
sides are peeled off: `Scheme.Modules.restrict ((pushforward V.ι).obj N) V.ι ≅ N` is the counit
of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, which is an isomorphism, and
`Scheme.Modules.restrict ((pushforward W.ι).obj M) V.ι ≅ Scheme.Modules.restrict M (X.homOfLE h)`
is that counit together with `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` at the
factorisation `X.homOfLE h ≫ W.ι = V.ι`. What is left is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`, which is the comparison on the
spectra transported along the two `AlgebraicGeometry.IsAffineOpen.isoSpec` by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.

The cocycle field `comp_trans` is not constructed here.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 26.7.3 (Tag 01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The comparison over the rings -/

/-- The restriction of functions `Γ(X, W) ⟶ Γ(X, V)` attached to an inclusion `V ≤ W` of
*affine* opens of `X`. This is the ring map the chart comparison is a base change along. -/
abbrev affineRestriction (X : Scheme.{u}) {V W : X.affineOpens} (h : V ≤ W) :
    Γ(X, (W.1 : X.Opens)) ⟶ Γ(X, (V.1 : X.Opens)) :=
  chartRestriction X (AffineOpensGlue.coe_le_coe h)

/-- The determinant of `L` on the chart of an affine open `V` is the sheaf on `Spec Γ(X, V)`
associated with the determinant of More on Algebra, Section 0FJI of the complex of
`Γ(X, V)`-modules `AlgebraicGeometry.DeterminantTwoTerm.chartComplex`.

This holds by unfolding `AlgebraicGeometry.DeterminantTwoTerm.specDet`,
`AlgebraicGeometry.DeterminantTwoTerm.affineDet` and
`AlgebraicGeometry.DeterminantTwoTerm.tildeInvertible`; it is recorded because the comparison on
the spectra is `AlgebraicGeometry.pullbackTildeIso` read at this module. -/
theorem chartDetSpec_eq_tilde (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartDetSpec L V =
      tilde ((det Γ(X, (V.1 : X.Opens))).obj ⟨chartComplex L V⟩).of.obj :=
  rfl

/-- **The determinant of an isomorphism of perfect two-term complexes**, as a linear equivalence
of determinant modules. The source category of `TwoTermDeterminant.det` is the core of a full
subcategory of the derived category, so an isomorphism of the underlying derived objects is
promoted to a morphism there by `CategoryTheory.ObjectProperty.isoMk` and
`CategoryTheory.CoreHom`; the value of the functor is then an isomorphism of invertible modules,
which is read as a linear equivalence through the inclusion of the full subcategory. -/
def detLinearEquivOfIso {R : Type u} [CommRing R] {K K' : PerfectTwoTermComplex R}
    (e : K.obj ≅ K'.obj) :
    ((det R).obj ⟨K⟩).of.obj ≃ₗ[R] ((det R).obj ⟨K'⟩).of.obj :=
  ((invertibleModuleProperty R).ι.mapIso
    ((det R).map (⟨ObjectProperty.isoMk (perfectTwoTermComplexProperty R) e⟩ :
      (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨K'⟩)).iso).toLinearEquiv

/-- **The chart comparison of determinants, over the rings.** Let `X` be a scheme, `L` a perfect
object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and `V ≤ W` affine opens of `X`. The base
change along the restriction of functions `ρ : Γ(X, W) ⟶ Γ(X, V)` of the determinant of More on
Algebra, Section 0FJI of the chart complex over `Γ(X, W)` is the determinant of the chart
complex over `Γ(X, V)`.

The determinant commutes with the flat base change `ρ` by
`TwoTermDeterminant.detBaseChange`, which produces the determinant of the derived extension of
scalars of the chart complex of `W`; that complex is the chart complex of `V` by
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso`, and the determinant of that
isomorphism finishes the comparison. -/
def chartDetModuleIso (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      (affineRestriction X h).hom.toAlgebra
    Γ(X, (V.1 : X.Opens)) ⊗[Γ(X, (W.1 : X.Opens))]
        ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj ≃ₗ[Γ(X, (V.1 : X.Opens))]
      ((det Γ(X, (V.1 : X.Opens))).obj ⟨chartComplex L V⟩).of.obj :=
  letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    (affineRestriction X h).hom.toAlgebra
  haveI hflat : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h)
  detBaseChange (affineRestriction X h).hom hflat (chartComplex L W) ≪≫ₗ
    detLinearEquivOfIso (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L).symm

/-! ### The comparison on the spectra -/

/-- **The chart comparison of determinants, on the spectra.** For affine opens `V ≤ W` of `X`,
the pullback along `Spec ρ : Spec Γ(X, V) ⟶ Spec Γ(X, W)` of the determinant of `L` on the chart
of `W` is the determinant of `L` on the chart of `V`.

The determinant on a chart is the sheaf associated with a module, by
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec_eq_tilde`, so Tag 01I9 turns its pullback
along `Spec ρ` into the sheaf associated with the extension of scalars of that module, and
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` identifies the latter. -/
def chartDetSpecPullbackIso (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).obj (chartDetSpec L W) ≅
      chartDetSpec L V :=
  (pullbackTildeIso Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) (affineRestriction X h)).app
      ((det Γ(X, (W.1 : X.Opens))).obj ⟨chartComplex L W⟩).of.obj ≪≫
    (tilde.functor Γ(X, (V.1 : X.Opens))).mapIso (chartDetModuleIso L h).toModuleIso

/-! ### The comparison on the open subschemes -/

/-- **The charts of an inclusion of affine opens form a commuting square.** For affine opens
`V ≤ W` of `X`, the identification `V ≅ Spec Γ(X, V)` followed by `Spec ρ` is the inclusion
`V ⟶ W` followed by the identification `W ≅ Spec Γ(X, W)`.

Both composites are morphisms into `Spec Γ(X, W)`; composing with the chart
`hW.fromSpec : Spec Γ(X, W) ⟶ X`, which is an open immersion and hence a monomorphism, turns
them into `V.ι` by `AlgebraicGeometry.IsAffineOpen.map_fromSpec` and
`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_fromSpec` on one side and by
`AlgebraicGeometry.Scheme.homOfLE_ι` on the other. -/
theorem isoSpec_hom_specMap_chartRestriction {V W : X.affineOpens} (h : V ≤ W) :
    V.2.isoSpec.hom ≫ Spec.map (affineRestriction X h) =
      X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ W.2.isoSpec.hom := by
  have : IsOpenImmersion (IsAffineOpen.fromSpec W.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec W.2
  rw [← cancel_mono W.2.fromSpec, Category.assoc, Category.assoc,
    W.2.map_fromSpec V.2 (homOfLE (AffineOpensGlue.coe_le_coe h)).op, W.2.isoSpec_hom_fromSpec,
    V.2.isoSpec_hom_fromSpec, Scheme.homOfLE_ι]

/-- **The chart comparison of determinants, on the open subschemes.** For affine opens `V ≤ W`
of `X`, the determinant of `L` on `V` is the restriction along `V ⟶ W` of the determinant of `L`
on `W`.

This is `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso` transported along the two
identifications `V ≅ Spec Γ(X, V)` and `W ≅ Spec Γ(X, W)`: the square
`isoSpec_hom_specMap_chartRestriction` identifies the two composites, and
`AlgebraicGeometry.Scheme.Modules.pullbackComp` splits the pullback along each of them. -/
def chartDetRestrictIso (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    chartDet L V ≅
      Scheme.Modules.restrict (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h)) :=
  (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPullbackIso L h).symm ≪≫
    (Scheme.Modules.pullbackComp V.2.isoSpec.hom
        (Spec.map (affineRestriction X h))).app (chartDetSpec L W) ≪≫
    (Scheme.Modules.pullbackCongr
        (isoSpec_hom_specMap_chartRestriction h)).app (chartDetSpec L W) ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
        W.2.isoSpec.hom).app (chartDetSpec L W)).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback
        (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app (chartDet L W)).symm

/-! ### The comparison in the shape the glueing datum wants -/

/-- **The chart comparison of determinants, in the shape the glueing datum wants.** This is the
`comp` field of `AlgebraicGeometry.AffineOpensGlue.ChartComparison` for the family
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` of determinants of `L` on the affine opens of
`X`: for affine opens `V ≤ W`, an isomorphism between the restrictions to `V` of the
pushforwards to `X` of the determinant on `V` and of the determinant on `W`.

Both pushforwards are peeled off by
`AffineOpensGlue.restrictPushforwardIso` and
`AffineOpensGlue.restrictPushforwardLeIso`, leaving
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`. -/
def chartDetComp (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    Scheme.Modules.restrict
        ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V))
        (V.1 : X.Opens).ι ≅
      Scheme.Modules.restrict
        ((Scheme.Modules.pushforward (AffineOpensGlue.chart X W)).obj (chartDet L W))
        (V.1 : X.Opens).ι :=
  AffineOpensGlue.restrictPushforwardIso (chartDet L V) ≪≫ chartDetRestrictIso L h ≪≫
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h) (chartDet L W)).symm

end AlgebraicGeometry.DeterminantTwoTerm

end
