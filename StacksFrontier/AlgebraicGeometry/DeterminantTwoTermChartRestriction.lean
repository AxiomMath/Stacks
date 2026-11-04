module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel

/-!
# The chart complex of a two-term perfect object is compatible with restriction

Let `X` be a scheme and `L` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`. An
affine open `V` of `X` carries the chart `hV.fromSpec : Spec Γ(X, V) ⟶ X`, and the derived
pullback of `L` along it corresponds, under the affine derived equivalence of Stacks 06Z0, to a
perfect object `K_V` of `D(Γ(X, V))` of Tor amplitude in `[-1, 0]`, namely
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplex`.

This file proves that the assignment `V ↦ K_V` is a base-change datum: for affine opens
`V ≤ W`, writing `ρ : Γ(X, W) ⟶ Γ(X, V)` for the restriction of functions, `K_V` is the derived
extension of scalars of `K_W` along `ρ`. This is the transition datum from which the gluing in
the proof of Stacks 0FJX reads its determinant lines, and it is the geometric half of that
gluing: nothing about determinants enters.

The argument has two steps. First, a purely formal one with no affineness and no determinant in
sight: the two charts are related by `Spec ρ`, so derived pullback along the chart of `V` is
derived pullback along the chart of `W` followed by derived pullback along `Spec ρ`. Second, the
affine comparison square of Stacks 08DW part (2) identifies the latter, on a complex of
associated sheaves, with derived extension of scalars; descending along the full faithfulness of
derived sheafification then gives the statement over `Γ(X, V)`.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartRestriction`: the restriction
  `Γ(X, W) ⟶ Γ(X, V)` of functions along an inclusion `V ≤ W` of opens.
* `AlgebraicGeometry.DeterminantTwoTerm.chartFactorIso`,
  `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackIso` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso`: the derived-pullback half, as a
  natural isomorphism of functors in both directions and at a single object.
* `AlgebraicGeometry.DeterminantTwoTerm.chartSpecRestrictionComp`: the comparison
  `L(Spec ρ_{V,V'})^* ∘ L(Spec ρ_{V',W})^* ≅ L(Spec ρ_{V,W})^*` for `V ≤ V' ≤ W`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso`: for affine opens `V ≤ W` of `X`
  and `K` in `D(𝒪_X)`, the restriction of `K` to the chart of `V` is the derived pullback along
  `Spec ρ` of its restriction to the chart of `W`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartFactorIso_assoc` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso_trans`: the cocycle for three
  affine opens `V ≤ V' ≤ W`, in both directions.
* `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso`: **the chart complex
  restricts to the base change.** For affine opens `V ≤ W` and `L` a perfect object of `D(𝒪_X)`
  of Tor amplitude in `[-1, 0]`, the complex over `Γ(X, V)` attached to `L` is the derived
  extension of scalars along `ρ` of the complex over `Γ(X, W)`.

## Implementation notes

*Which derived pullback.* `AlgebraicGeometry.DeterminantTwoTerm.derivedPullbackObj` is built on
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom`, while
`AlgebraicGeometry.affinePullbackComparison` is stated for `Stacks.Duality.derivedPullback`.
The second is an `abbrev` for the first, so there is one functor and no bridge is needed; the
statements below use the first spelling, which is the determinant development's.

*Which model of the derived category.* `CategoryTheory.HasDerivedCategory` carries the localized
category as data, so a functor built at one model is not a functor at any other.
`AlgebraicGeometry.affinePullbackComparison` is pinned to the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whereas the determinant development is
at `CategoryTheory.HasDerivedCategory.standard`. The input used here is therefore
`AlgebraicGeometry.StandardModel.affinePullbackComparison`, the same mathematics at the standard
model. For the same reason this file must write
`attribute [local instance 10000] HasDerivedCategory.standard`, not the plain attribute: the
import closure carries the locally small *global* instances, which beat a default-priority local
one. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`.

*The derived-pullback half is pseudo-functoriality.* `Stacks.DerivedPullback.schemeFactorIso` is
the composition isomorphism of Stacks 0D5S attached to a factorisation `f ≫ g = k` of morphisms
of schemes, and `AlgebraicGeometry.IsAffineOpen.map_fromSpec` is exactly such a factorisation of
the chart of `V` through the chart of `W`. The cocycle is `Stacks.DerivedPullback.factorIso_assoc`,
the associativity coherence of Stacks 0D5S, at the two factorisations.

*No flatness.* The restriction `Γ(X, W) → Γ(X, V)` between affine opens is flat
(`AlgebraicGeometry.IsAffineOpen.flat_presheaf_map`), but nothing below uses it: Stacks 08DW part
(2) is unconditional, so the base-change statement holds for the *derived* extension of scalars
with no hypothesis. Flatness is what will later let the derived extension of scalars be replaced
by the ordinary one on the determinant line.

*No `@[stacks]` attribute.* Stacks 0FJX is the determinant functor, its canonical section and
their affine-local description; this file constructs none of the three. Stacks 08DW is not
covered either, its part (1) being unproved in the library, and the comparison used here is
already carried at two models elsewhere.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Lemma 36.9.2 (Tag 08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 20.28.2 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback (factorIso_assoc schemeFactorIso)

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

/-- The restriction `Γ(X, W) ⟶ Γ(X, V)` of functions along an inclusion `V ≤ W` of opens of a
scheme `X`. -/
abbrev chartRestriction (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W) : Γ(X, W) ⟶ Γ(X, V) :=
  X.presheaf.map (homOfLE h).op

variable {X : Scheme.{u}} {V V' W : X.Opens}

/-- Restriction of functions is transitive: for `V ≤ V' ≤ W` the restriction to `V` is the
restriction to `V'` followed by the restriction from `V'`. -/
theorem chartRestriction_comp (h₁ : V ≤ V') (h₂ : V' ≤ W) :
    chartRestriction X h₂ ≫ chartRestriction X h₁ = chartRestriction X (h₁.trans h₂) := by
  rw [← Functor.map_comp]
  rfl

/-- The two charts of an inclusion `V ≤ W` of affine opens are related by `Spec` of the
restriction of functions: for `V ≤ V' ≤ W` the morphisms of affine schemes attached to the two
restrictions compose to the one attached to `V ≤ W`. -/
theorem specMap_chartRestriction_comp (h₁ : V ≤ V') (h₂ : V' ≤ W) :
    Spec.map (chartRestriction X h₁) ≫ Spec.map (chartRestriction X h₂) =
      Spec.map (chartRestriction X (h₁.trans h₂)) := by
  rw [← Spec.map_comp, chartRestriction_comp]

/-! ### The derived-pullback half -/

/-- **The chart of a smaller affine open factors through the chart of a larger one.** For affine
opens `V ≤ W` of a scheme `X`, derived pullback along `hW.fromSpec : Spec Γ(X, W) ⟶ X` followed
by derived pullback along `Spec ρ`, where `ρ : Γ(X, W) ⟶ Γ(X, V)` is the restriction of
functions, is derived pullback along `hV.fromSpec`.

This is the composition isomorphism of Stacks 0D5S at the factorisation
`Spec ρ ≫ hW.fromSpec = hV.fromSpec` of `AlgebraicGeometry.IsAffineOpen.map_fromSpec`. No
affineness is used beyond the existence of the two charts, and no determinant occurs. -/
def chartFactorIso (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W) :
    derivedPullback hW.fromSpec.toLRSHom.toShHom ⋙
        derivedPullback (Spec.map (chartRestriction X h)).toLRSHom.toShHom ≅
      derivedPullback hV.fromSpec.toLRSHom.toShHom :=
  schemeFactorIso (Spec.map (chartRestriction X h)) hW.fromSpec hV.fromSpec
    (hW.map_fromSpec hV (homOfLE h).op)

/-- **Restriction to the chart of an affine open is derived pullback from the chart of a larger
one.** The inverse of `chartFactorIso`, read in the direction the chart datum of the determinant
uses it: derived pullback along the chart of `V` is derived pullback along the chart of `W`
followed by derived pullback along `Spec ρ`. -/
def chartPullbackIso (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W) :
    derivedPullback hV.fromSpec.toLRSHom.toShHom ≅
      derivedPullback hW.fromSpec.toLRSHom.toShHom ⋙
        derivedPullback (Spec.map (chartRestriction X h)).toLRSHom.toShHom :=
  (chartFactorIso hV hW h).symm

/-- **The restriction of a complex to a chart is the base change of its restriction to a larger
chart.** The object-level form of `chartPullbackIso`: for affine opens `V ≤ W` of `X` and an
object `K` of `D(𝒪_X)`, the derived pullback of `K` to `Spec Γ(X, V)` is the derived pullback
along `Spec ρ` of the derived pullback of `K` to `Spec Γ(X, W)`. -/
def chartPullbackObjIso (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W)
    (K : DerivedCategory X.Modules) :
    (derivedPullback hV.fromSpec.toLRSHom.toShHom).obj K ≅
      (derivedPullback (Spec.map (chartRestriction X h)).toLRSHom.toShHom).obj
        ((derivedPullback hW.fromSpec.toLRSHom.toShHom).obj K) :=
  ((chartFactorIso hV hW h).app K).symm

/-- `chartPullbackObjIso` is `chartPullbackIso` read at an object. -/
theorem chartPullbackIso_app (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W)
    (K : DerivedCategory X.Modules) :
    (chartPullbackIso hV hW h).app K = chartPullbackObjIso hV hW h K :=
  rfl

/-- The comparison `L(Spec ρ_{V,V'})^* ∘ L(Spec ρ_{V',W})^* ≅ L(Spec ρ_{V,W})^*` attached to a
chain `V ≤ V' ≤ W` of opens, at a single object: the composition isomorphism of Stacks 0D5S at
the factorisation `Spec ρ_{V,V'} ≫ Spec ρ_{V',W} = Spec ρ_{V,W}`. -/
def chartSpecRestrictionComp (h₁ : V ≤ V') (h₂ : V' ≤ W)
    (N : DerivedCategory (Spec Γ(X, W)).Modules) :
    (derivedPullback (Spec.map (chartRestriction X h₁)).toLRSHom.toShHom).obj
        ((derivedPullback (Spec.map (chartRestriction X h₂)).toLRSHom.toShHom).obj N) ≅
      (derivedPullback
        (Spec.map (chartRestriction X (h₁.trans h₂))).toLRSHom.toShHom).obj N :=
  (schemeFactorIso (Spec.map (chartRestriction X h₁)) (Spec.map (chartRestriction X h₂))
    (Spec.map (chartRestriction X (h₁.trans h₂)))
    (specMap_chartRestriction_comp h₁ h₂)).app N

/-- **The cocycle for the chart factorisations.** For affine opens `V ≤ V' ≤ W` of `X`, the
comparison of the two `Spec` of restriction maps followed by `chartFactorIso` for `V ≤ W` is the
derived pullback along `Spec ρ_{V,V'}` of `chartFactorIso` for `V' ≤ W` followed by
`chartFactorIso` for `V ≤ V'`.

This is `Stacks.DerivedPullback.factorIso_assoc`, the associativity coherence of Stacks 0D5S, at
the two two-step factorisations of `hV.fromSpec` through `hV'.fromSpec` and through
`hW.fromSpec`. -/
theorem chartFactorIso_assoc (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hW : IsAffineOpen W) (h₁ : V ≤ V') (h₂ : V' ≤ W) (K : DerivedCategory X.Modules) :
    chartSpecRestrictionComp h₁ h₂ ((derivedPullback hW.fromSpec.toLRSHom.toShHom).obj K) ≪≫
        (chartFactorIso hV hW (h₁.trans h₂)).app K =
      (derivedPullback (Spec.map (chartRestriction X h₁)).toLRSHom.toShHom).mapIso
          ((chartFactorIso hV' hW h₂).app K) ≪≫
        (chartFactorIso hV hV' h₁).app K := by
  have key := factorIso_assoc
    (Spec.map (chartRestriction X h₁)).toLRSHom.toShHom
    (Spec.map (chartRestriction X h₂)).toLRSHom.toShHom
    hW.fromSpec.toLRSHom.toShHom hV'.fromSpec.toLRSHom.toShHom
    (Spec.map (chartRestriction X (h₁.trans h₂))).toLRSHom.toShHom
    hV.fromSpec.toLRSHom.toShHom
    (congrArg (fun m : Spec Γ(X, V') ⟶ X => m.toLRSHom.toShHom)
      (hW.map_fromSpec hV' (homOfLE h₂).op))
    (congrArg (fun m : Spec Γ(X, V) ⟶ Spec Γ(X, W) => m.toLRSHom.toShHom)
      (specMap_chartRestriction_comp h₁ h₂))
    (congrArg (fun m : Spec Γ(X, V) ⟶ X => m.toLRSHom.toShHom)
      (hW.map_fromSpec hV (homOfLE (h₁.trans h₂)).op))
    (congrArg (fun m : Spec Γ(X, V) ⟶ X => m.toLRSHom.toShHom)
      (hV'.map_fromSpec hV (homOfLE h₁).op)) K
  exact key

/-- **The cocycle for the chart comparisons.** For affine opens `V ≤ V' ≤ W` of `X`, the
comparison of `chartPullbackObjIso` for `V ≤ W`, followed by the inverse of the comparison of
the two `Spec` of restriction maps, is the comparison for `V ≤ V'` followed by the derived
pullback along `Spec ρ_{V,V'}` of the comparison for `V' ≤ W`.

This is `chartFactorIso_assoc` read on the inverse isomorphisms, and it is the cocycle from
which the chart datum of the determinant of Stacks 0FJX reads its transitions. -/
theorem chartPullbackObjIso_trans (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hW : IsAffineOpen W) (h₁ : V ≤ V') (h₂ : V' ≤ W) (K : DerivedCategory X.Modules) :
    chartPullbackObjIso hV hW (h₁.trans h₂) K ≪≫
        (chartSpecRestrictionComp h₁ h₂
          ((derivedPullback hW.fromSpec.toLRSHom.toShHom).obj K)).symm =
      chartPullbackObjIso hV hV' h₁ K ≪≫
        (derivedPullback (Spec.map (chartRestriction X h₁)).toLRSHom.toShHom).mapIso
          (chartPullbackObjIso hV' hW h₂ K) := by
  have key := congrArg Iso.symm (chartFactorIso_assoc hV hV' hW h₁ h₂ K)
  simpa only [chartPullbackObjIso, Iso.trans_symm, Functor.mapIso_symm] using key

/-! ### The chart complex restricts to the base change -/

/-- **The chart complex of a two-term perfect object restricts to the base change.** Let `X` be
a scheme, `L` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`, and `V ≤ W` affine
opens of `X`. The perfect object of `D(Γ(X, V))` corresponding under the affine derived
equivalence of Stacks 06Z0 to the restriction of `L` to the chart of `V` is the derived
extension of scalars, along the restriction of functions `ρ : Γ(X, W) ⟶ Γ(X, V)`, of the one
corresponding to the restriction of `L` to the chart of `W`.

Both sides are compared after derived sheafification: on the chart of `V` the left side becomes
`L` restricted there, which by `chartPullbackIso` is the derived pullback along `Spec ρ` of `L`
restricted to the chart of `W`, which by the affine comparison square of Stacks 08DW part (2) is
the sheafification of the derived extension of scalars. Derived sheafification is fully faithful
by Stacks 06Z0, so the comparison descends. -/
def sourceComplexRestrictionIso (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ W)
    (L : PerfectTwoTermAmplitude X) :
    (sourceComplex Γ(X, V) (derivedPullbackObj hV.fromSpec L)).obj ≅
      (totalDerivedExtensionScalars.{u, u, u} (chartRestriction X h).hom).functor.obj
        ((sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L)).obj) :=
  (StandardModel.mapDerivedCategoryFullyFaithful Γ(X, V)).preimageIso
    ((IsPerfectTwoTermAmplitude (Spec Γ(X, V))).ι.mapIso
        (tildeSourceComplexIso Γ(X, V) (derivedPullbackObj hV.fromSpec L)) ≪≫
      chartPullbackObjIso hV hW h L.obj ≪≫
      (StandardModel.specDerivedPullback (chartRestriction X h)).mapIso
        ((IsPerfectTwoTermAmplitude (Spec Γ(X, W))).ι.mapIso
          (tildeSourceComplexIso Γ(X, W) (derivedPullbackObj hW.fromSpec L))).symm ≪≫
      (StandardModel.affinePullbackComparison Γ(X, W) Γ(X, V) (chartRestriction X h)).app
        ((sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L)).obj))

end AlgebraicGeometry.DeterminantTwoTerm

end
