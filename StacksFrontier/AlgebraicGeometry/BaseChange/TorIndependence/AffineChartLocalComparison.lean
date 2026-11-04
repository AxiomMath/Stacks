module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkAlgebra
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareCube

/-!
# The Tag 065Z comparison of a chart, read at the four local rings of a point of `U'`

Let `ch` be a Cartesian affine-open chart for a base-change square of schemes and `y` a point of
`Spec 𝒪_{X'}(U')`, with image `x'` in `X'`. The square of coordinate rings of the chart and the
square of local rings of the square of schemes at `x'` sit in a cube: the two source corners
`𝒪_S(V)`, `𝒪_X(U)` map to `𝒪_{S, f(g' x')}`, `𝒪_{X, g' x'}` by localizations, and the two target
corners `𝒪_{S'}(V')`, `𝒪_{X'}(U')` map to `𝒪_{S', f' x'}`, `𝒪_{X', x'}`.

`RingTheory.TorIndependence.squareComparison_cube` is the naturality of the Tag 065Z comparison
across such a cube. This module supplies it with the chart's geometry: the four ring maps of
`AffineChartStalkAlgebra`, their three localization properties, and the four compatibilities
saying that they carry the chart's square of rings to the square of stalk maps. The result is
that, on a complex already living over `𝒪_{X, g' x'}` — the derived stalk of `K`, say — the
comparison of the four local rings of the *schemes* is the chart's own comparison, extended along
`𝒪_{S'}(V') → 𝒪_{S', f' x'}` and followed by the comparison of the bottom square.

## Main results

* `AlgebraicGeometry.BaseChangeChart.squareComparison_localRings`: the displayed identification.

## Implementation notes

The square of local rings is the one `AlgebraicGeometry.baseChangeCohomologyMap` is built from:
its four ring maps are `f.stalkMap`, `AlgebraicGeometry.baseStalkMap`, `g'.stalkMap` and
`f'.stalkMap`, and its commutation is `AlgebraicGeometry.stalkMap_square`. So the identification
below is stated at exactly the square that the pointwise condition (1) of Stacks 0DJ8 uses, with
no transport along a ring isomorphism anywhere: the localizations are taken to *be* the local
rings of the schemes rather than the local rings of the spectra of the coordinate rings.

The inverse of the germ comparison at `U'` is data, as in
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` and in the hypothesis `hsource` of
`AlgebraicGeometry.baseChange_tfae_of_sourceBridge`.

The two transports `RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr` are
unavoidable: the mixed square of the localization law has edges
`baseStalkMap ∘ (𝒪_S(V) → 𝒪_{S, f(g' x')})` and `g'.stalkMap ∘ (𝒪_X(U) → 𝒪_{X, g' x'})`, while
the outer rectangle of the pasting law has edges `(𝒪_{S'}(V') → 𝒪_{S', f' x'}) ∘ ch.b` and
`(𝒪_{X'}(U') → 𝒪_{X', x'}) ∘ ch.c`; those are equal ring maps with different spellings, and a
comparison's type mentions its edges.

No tag attribute is placed here: nothing below is a clause of Stacks 0DJ8.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
  (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
  (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
  (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z)

/-- **The Tag 065Z comparison of the four local rings of a chart at a point of `U'`.** On a
complex already living over `𝒪_{X, g' x'}`, the comparison of the square of local rings of the
square of schemes at `x'` is the chart's own comparison, extended along
`𝒪_{S'}(V') → 𝒪_{S', f' x'}` and followed by the comparison of the bottom square
`(𝒪_{S'}(V'), 𝒪_{X'}(U'), 𝒪_{S', f' x'}, 𝒪_{X', x'})`, under the two source identifications of
`RingTheory.TorIndependence.localizedSquareDomainIso` and
`RingTheory.TorIndependence.localizedSquareCodomainIso`.

This is `RingTheory.TorIndependence.squareComparison_cube` supplied with the chart's geometry. -/
public theorem squareComparison_localRings :
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkR y
    haveI := ch.isLocalization_toStalkA y
    (RingTheory.TorIndependence.localizedSquareDomainIso.{u, u} (ch.primeComplR y) ch.a.hom
          (f.stalkMap (g' (ch.incU' y))).hom (baseStalkMap f g f' g' w (ch.incU' y))
          (ch.toStalkA_a y)).hom ≫
        RingTheory.TorIndependence.squareComparison.{u, u}
          (f.stalkMap (g' (ch.incU' y))).hom (baseStalkMap f g f' g' w (ch.incU' y))
          (g'.stalkMap (ch.incU' y)).hom (f'.stalkMap (ch.incU' y)).hom
          (stalkMap_square f g f' g' w (ch.incU' y)) =
      Functor.whiskerLeft
          ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory)
          (Functor.whiskerLeft ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory)
              (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                (ch.toStalkR'_b y w)).hom ≫
            RingTheory.TorIndependence.pastedComparison.{u, u} ch.a.hom ch.b.hom ch.c.hom
                ch.d.hom (ch.toStalkR' y) (ch.toStalkA' y ε') (f'.stalkMap (ch.incU' y)).hom
                ch.isPushout_hom (ch.toStalkA'_d y ε' h₁ h₂) ≫
              Functor.whiskerRight
                (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                  (ch.toStalkA'_c y ε' h₁ h₂)).inv
                ((ModuleCat.restrictScalars.{u}
                  (f'.stalkMap (ch.incU' y)).hom).mapDerivedCategory)) ≫
        (RingTheory.TorIndependence.localizedSquareCodomainIso.{u, u} (ch.primeComplA y)
          (g'.stalkMap (ch.incU' y)).hom (f'.stalkMap (ch.incU' y)).hom).hom := by
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkR y
  have := ch.isLocalization_toStalkA y
  exact RingTheory.TorIndependence.squareComparison_cube.{u, u} (ch.primeComplR y)
    (ch.primeComplA y) ch.a.hom ch.b.hom ch.c.hom ch.d.hom (ch.toStalkR' y)
    (ch.toStalkA' y ε') (f.stalkMap (g' (ch.incU' y))).hom
    (baseStalkMap f g f' g' w (ch.incU' y)) (g'.stalkMap (ch.incU' y)).hom
    (f'.stalkMap (ch.incU' y)).hom ch.isPushout_hom (ch.toStalkA'_d y ε' h₁ h₂)
    (ch.toStalkA_a y) (stalkMap_square f g f' g' w (ch.incU' y)) (ch.toStalkR'_b y w)
    (ch.toStalkA'_c y ε' h₁ h₂)

end BaseChangeChart

end AlgebraicGeometry

end
