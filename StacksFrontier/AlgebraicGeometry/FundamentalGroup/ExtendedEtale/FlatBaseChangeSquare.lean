module

public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.SpectrumComparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.LargerOpen
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The Cartesian square for flat base change of the extension algebra

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement carries
depth at least two and `π : V ⟶ U` a finite étale cover, so that `𝓑 = (π ≫ j)_* 𝒪_V` is the
extension algebra of the cover, and let `g : X' ⟶ X` be flat with `j'` the base change of `j`
and `π'` the base change of `π`. The last assertion of the flat-base-change clause of
[Stacks, Tag 0EY6] is that the square
```
Spec_{X'}(𝓑') ⟶ Spec_X(𝓑)
     ↓               ↓
    X'      ⟶       X
```
is Cartesian, where `𝓑' = (π' ≫ j')_* 𝒪_{V'}`.
`Stacks.FundamentalGroup.extendedEtaleSpectrum_flatBaseChange_of_isPullback` proves exactly
this given a morphism of relative spectra over `g` whose own square is Cartesian. This file
supplies that morphism and its square, and so states the assertion outright.

The morphism and the square are the base-change assertion [Stacks, Tag 01LX] part (2), which
this library proves as `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`: an
isomorphism, in the slice category over `X'`, between the restriction of `Spec_X(𝓑)` along `g`
and the relative spectrum of the extension of scalars `g^*𝓑`. An isomorphism of that shape *is*
a Cartesian square, by `coverMapOfPullbackIso` and `isPullback_coverMapOfPullbackIso`.

## Main definitions

* `Stacks.RelativeSpec.relativeSpectrumBaseChangeMap` — the canonical morphism from the
  relative spectrum of the extension of scalars to the original relative spectrum.

## Main results

* `Stacks.RelativeSpec.isPullback_relativeSpectrumBaseChangeMap` — its square over the
  base-change morphism is Cartesian; this is [Stacks, Tag 01LX] part (2) read as a square.
* `Stacks.FundamentalGroup.extendedEtaleSpectrum_flatBaseChange` — the `flat_base_change`
  clause of [Stacks, Tag 0EY6].

## Implementation notes

The extension of scalars used here is the canonical one,
`Stacks.RelativeSpec.pullbackAlgebra`, which exists over an arbitrary morphism of bases; the
flatness of `g` enters the clause only through the comparison of algebras
`Stacks.FundamentalGroup.extendedEtaleAlgebraComparison`, not through the square.

**The six companion assertions of this clause carry no attribute, and none is written here.**
The docstring of `Stacks.FundamentalGroup.extendedEtaleDepth_flatBaseChange` records why they
are unattributed: a clause string on part of a covering set would register the whole clause as
formalized. The clause string belongs on all six as a group, and no `add_to_stacks` command
attaching it is written, so the clause remains unregistered on this side. The final section below is
the place
they would go.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence Stacks.FundamentalGroup.ExtendedEtaleFold

universe u

namespace Stacks.RelativeSpec

/-! ### The base-change morphism of relative spectra and its Cartesian square -/

/-- **The canonical base-change morphism of relative spectra.** For a relative-spectrum
situation `s` on a base `S` and a morphism `g : S' ⟶ S`, this is the morphism
`Spec_{S'}(g^*A) ⟶ Spec_S(A)` over `g`, read off the isomorphism
`Spec_S(A) ×_S S' ≅ Spec_{S'}(g^*A)` of [Stacks, Tag 01LX] part (2) by composing its inverse
with the first projection. -/
public def relativeSpectrumBaseChangeMap (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}}
    (g : S' ⟶ s.base) :
    (gluedSpectrum (pullbackAlgebra s g).situation).scheme ⟶ (gluedSpectrum s).scheme :=
  coverMapOfPullbackIso g (Over.mk (relativeSpecToBase s.algebra))
    (relativeSpecToBase ((algebraPullback g).obj s.algebra))
    (relativeSpecBaseChangeIso g s.algebra)

/-- **[Stacks, Tag 01LX] part (2), as a Cartesian square.** The relative spectrum of the
extension of scalars of `A` along `g : S' ⟶ S` is the fibre product of `Spec_S(A)` with `S'`
over `S`, by way of `relativeSpectrumBaseChangeMap`. An isomorphism in the slice category over
`S'` between the restriction of `Spec_S(A)` along `g` and `Spec_{S'}(g^*A)` is the same data as
such a square, which is `isPullback_coverMapOfPullbackIso`. -/
public theorem isPullback_relativeSpectrumBaseChangeMap (s : RelativeSpecSituation.{u})
    {S' : Scheme.{u}} (g : S' ⟶ s.base) :
    IsPullback (gluedSpectrum (pullbackAlgebra s g).situation).toBase
      (relativeSpectrumBaseChangeMap s g) g (gluedSpectrum s).toBase :=
  isPullback_coverMapOfPullbackIso g (Over.mk (relativeSpecToBase s.algebra)) _
    (relativeSpecBaseChangeIso g s.algebra)

end Stacks.RelativeSpec

namespace Stacks.FundamentalGroup

open Stacks.RelativeSpec

/-! ### The flat-base-change clause of Tag 0EY6 -/

/-- **The `flat_base_change` clause of [Stacks, Tag 0EY6], the Cartesian square of relative
spectra.** Let `X` be locally Noetherian, `j : U ⟶ X` an open immersion whose complement
carries depth at least two and `π : V ⟶ U` a finite étale cover, and let `g : X' ⟶ X` be flat
with `j'` the base change of `j` and `π'` the base change of `π`. Then
`Spec_{X'}((π' ≫ j')_* 𝒪_{V'})` is the fibre product of `Spec_X((π ≫ j)_* 𝒪_V)` with `X'` over
`X`.

The morphism exhibiting it is the comparison
`extendedEtaleSpectrumComparison` of the two algebras on `X'` — an isomorphism over `X'`,
because flat base change identifies the extension of scalars of `(π ≫ j)_* 𝒪_V` with
`(π' ≫ j')_* 𝒪_{V'}` — followed by the canonical base-change morphism
`Stacks.RelativeSpec.relativeSpectrumBaseChangeMap`, whose square is Cartesian by
[Stacks, Tag 01LX] part (2). Transporting the latter square along the former isomorphism is
`extendedEtaleSpectrum_flatBaseChange_of_isPullback`. -/
@[stacks 0EY6 "flat_base_change"]
public theorem extendedEtaleSpectrum_flatBaseChange {U X V U' X' V' : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π]
    (g : X' ⟶ X) [Flat g]
    (j' : U' ⟶ X') [IsOpenImmersion j'] (gU : U' ⟶ U)
    (π' : V' ⟶ U') [IsFinite π'] [Etale π'] (gV : V' ⟶ V)
    (hj : IsPullback j' gU g j)
    (hπ : IsPullback π' gV gU π)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) :
    IsPullback
      (gluedSpectrum (ExtendedEtaleFold.extendedEtaleSituation j' π'
        (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth))).toBase
      (extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth
            (pullbackAlgebra (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) ≫
        relativeSpectrumBaseChangeMap (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g)
      g (gluedSpectrum (ExtendedEtaleFold.extendedEtaleSituation j π hdepth)).toBase :=
  extendedEtaleSpectrum_flatBaseChange_of_isPullback j π g j' gU π' gV hj hπ hdepth
    (pullbackAlgebra (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g)
    (relativeSpectrumBaseChangeMap (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g)
    (isPullback_relativeSpectrumBaseChangeMap
      (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g)

end Stacks.FundamentalGroup

end

/-! ### The rest of the covering set of the `flat_base_change` clause -/

-- NOTHING IS REGISTERED HERE. This section is empty: the `add_to_stacks` commands that would
-- attach the clause string to the six assertions proved in sibling files were never written,
-- so the `flat_base_change` clause of Stacks 0EY6 is unregistered on this side. Whoever holds
-- 0EY6 should write them here, as a group, after checking the six declarations do cover the
-- clause. A `/-- -/` docstring in this section would be a parse error, because
-- `add_to_stacks` is a command and not a declaration; use `--` comments.
