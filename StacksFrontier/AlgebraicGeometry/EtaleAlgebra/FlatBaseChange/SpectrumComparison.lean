module

public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.ExtensionAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraIsoComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change of the relative spectrum of the extension algebra

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` an open immersion whose complement carries
depth at least two, and `π : V ⟶ U` a finite étale cover, so that `𝓑 = (π ≫ j)_* 𝒪_V` is the
extension algebra of the cover.  Let `g : X' ⟶ X` be flat, with `j'` the base change of `j` and
`π'` the base change of `π`.
`Stacks.FundamentalGroup.exists_extendedEtaleAlgebraComparison` says that any extension of
scalars of `𝓑` along `g` is isomorphic to the extension algebra `(π' ≫ j')_* 𝒪_{V'}` of the
base-changed cover.  This file *chooses* that isomorphism and pushes it to the relative spectra:
the two algebras live on the same scheme `X'`, so their relative spectra are canonically
isomorphic by `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso`.

Everything is stated for an arbitrary extension of scalars
`d : Stacks.RelativeSpec.AlgebraPullback (extendedEtaleSituation j π hdepth) g`, with the
statement [Stacks, Tag 0EY6] actually makes — at the extension of scalars
`Stacks.FundamentalGroup.extendedEtaleAlgebraPullback` produced by flatness — recorded beside
it as a specialization.

## Main definitions

* `Stacks.FundamentalGroup.extendedEtaleAlgebraComparison` is the chosen comparison of algebras,
  and `Stacks.FundamentalGroup.extendedEtaleAlgebraComparison_map` is the compatibility that
  specifies it.
* `Stacks.FundamentalGroup.extendedEtaleSpectrumComparison` is the induced morphism of relative
  spectra.

## Main results

* `Stacks.FundamentalGroup.extendedEtaleSpectrumComparison_universalMap` characterizes the
  spectrum comparison by its universal element.
* `Stacks.FundamentalGroup.isIso_extendedEtaleSpectrumComparison` — it is an isomorphism.
* `Stacks.FundamentalGroup.extendedEtaleSpectrumComparison_toBase` — it is a morphism over the
  new base `X'`.
* `Stacks.FundamentalGroup.extendedEtaleSpectrum_flatBaseChange_of_isPullback` — the Cartesian
  square of the tag, against any morphism of relative spectra that is already Cartesian over
  `g`;  the canonical such morphism is [Stacks, Tag 01LX]'s, supplied by
  `Stacks.RelativeSpec.relativeSpectrumBaseChangeMap`.

## Implementation notes

The algebra comparison is `Classical.choose` of
`Stacks.FundamentalGroup.exists_extendedEtaleAlgebraComparison`, and this is not a weak
existence:  `Stacks.FundamentalGroup.algebraIso_eq_of_isPushout` shows the isomorphism with the
stated compatibility is *unique*, so the choice is forced.

The spectrum comparison is the specified morphism of
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso` rather than an unspecified isomorphism
between representing schemes;  its defining property and its invertibility are that file's
`relativeSpectrumMapOfAlgebraIso_homEquiv` and
`isIso_relativeSpectrumMapOfAlgebraIso`, which rest on the representability of the relative
spectrum over an *arbitrary* base, [Stacks, Tag 01LV] — the base `X'` here is only locally
Noetherian, not affine.

The three results below are members of the covering set of tag 0EY6's `flat_base_change`
clause and carry `@[stacks 0EY6 "flat_base_change"]`.  That clause is now complete:  its last
member was the Cartesian square
```
Spec_{X'}(𝓑') ⟶ Spec_X(𝓑)
     ↓               ↓
    X'      ⟶       X
```
which needs the canonical base-change morphism of relative spectra of [Stacks, Tag 01LX] part
(2).  That part is in this library after all --- `relativeSpecBaseChangeIso` of
`StacksFrontier/AlgebraicGeometry/RelativeSpecOpenRestriction/RelativeSpecBaseChange.lean` --- and
converting it to an `IsPullback` square is
`Stacks.RelativeSpec.isPullback_relativeSpectrumBaseChangeMap`, after which the square follows
by transport along `isIso_extendedEtaleSpectrumComparison`.  Note that the `@[stacks 01LX]`
declaration in `RelativeSpecEssSurj/Basic.lean` is part (3), not part (2), which is why an
earlier reading of this file recorded part (2) as missing.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup

/-! ### The chosen comparison of algebras -/

/-- **The canonical isomorphism from an extension of scalars of the extension algebra to the
extension algebra of the base-changed cover.**  This is `Classical.choose` of
`Stacks.FundamentalGroup.exists_extendedEtaleAlgebraComparison`;  the isomorphism with the
compatibility of `extendedEtaleAlgebraComparison_map` is unique, by
`Stacks.FundamentalGroup.algebraIso_eq_of_isPushout`, so nothing is lost by choosing. -/
public def extendedEtaleAlgebraComparison {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    d.algebra ≅
      (ExtendedEtaleFold.extendedEtaleSituation j' π'
        (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth)).algebra :=
  Classical.choose
    (exists_extendedEtaleAlgebraComparison j π g j' gU π' gV hj hπ hdepth d)

/-- **The comparison carries the canonical map of the extension of scalars to the base-change
morphism**, transported along the Cartesian comparison of covers.  This is the property that
specifies `Stacks.FundamentalGroup.extendedEtaleAlgebraComparison`. -/
@[stacks 0EY6 "flat_base_change"]
public theorem extendedEtaleAlgebraComparison_map {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    d.map ≫
        (extendedEtaleAlgebraComparison j π g j' gU π' gV hj hπ hdepth d).hom.right =
      pushforwardBaseChangeMap g (Over.mk (π ≫ j)) ≫
        (pushforwardAlgebraMap
          (Over.isoMk (hπ.paste_horiz hj).flip.isoPullback (by simp) :
            Over.mk (π' ≫ j') ≅ (Over.pullback g).obj (Over.mk (π ≫ j))).hom).right :=
  Classical.choose_spec
    (exists_extendedEtaleAlgebraComparison j π g j' gU π' gV hj hπ hdepth d)

/-! ### The induced comparison of relative spectra -/

/-- **The morphism of relative spectra induced by the algebra comparison.**  Both algebras live
on `X'`, so this is `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso`:  the morphism
corresponding, under the representing bijection of [Stacks, Tag 01LV], to the structure morphism
of the relative spectrum of `(π' ≫ j')_* 𝒪_{V'}` paired with its universal algebra map
precomposed with the comparison.  It is a specified morphism, not an unspecified isomorphism of
representing schemes. -/
public def extendedEtaleSpectrumComparison {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    (gluedSpectrum (ExtendedEtaleFold.extendedEtaleSituation j' π'
      (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth))).scheme ⟶
    (gluedSpectrum d.situation).scheme :=
  relativeSpectrumMapOfAlgebraIso d.situation
    (ExtendedEtaleFold.extendedEtaleSituation j' π'
      (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth)).algebra
    (ExtendedEtaleFold.extendedEtaleSituation j' π'
      (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth)).isQuasicoherent
    (extendedEtaleAlgebraComparison j π g j' gU π' gV hj hπ hdepth d)

/-- **[Stacks, Tag 0EY6], the universal-map equation for the spectrum comparison.**  Under the
representing bijection of [Stacks, Tag 01LV] the comparison is the structure morphism of the
base-changed relative spectrum together with its universal algebra map precomposed with the
algebra comparison.  This is the defining property of
`Stacks.FundamentalGroup.extendedEtaleSpectrumComparison`, so it holds by
`Equiv.apply_symm_apply`. -/
@[stacks 0EY6 "flat_base_change"]
public theorem extendedEtaleSpectrumComparison_universalMap {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    let e := ExtendedEtaleFold.extendedEtaleSituation j' π'
      (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth)
    (relativeSpecRepresentableBy d.situation).homEquiv
        (extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth d) =
      ⟨(gluedSpectrum e).toBase,
        algebraHomAsUnder
            (extendedEtaleAlgebraComparison j π g j' gU π' gV hj hπ hdepth d).hom ≫
          universalAlgebraMap e⟩ :=
  relativeSpectrumMapOfAlgebraIso_homEquiv d.situation _ _ _

/-- **[Stacks, Tag 0EY6], the spectrum comparison is an isomorphism.**  The two relative spectra
represent functors identified by
`Stacks.RelativeSpec.relativeSpecFunctorIsoOfAlgebraIso`, and the comparison is the induced
comparison of representing objects. -/
@[stacks 0EY6 "flat_base_change"]
public theorem isIso_extendedEtaleSpectrumComparison {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    IsIso (extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth d) :=
  isIso_relativeSpectrumMapOfAlgebraIso d.situation _ _ _

/-- **The spectrum comparison is a morphism over the new base.** -/
public theorem extendedEtaleSpectrumComparison_toBase {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g) :
    extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth d ≫
        (gluedSpectrum d.situation).toBase =
      (gluedSpectrum (ExtendedEtaleFold.extendedEtaleSituation j' π'
        (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth))).toBase :=
  relativeSpectrumMapOfAlgebraIso_toBase d.situation _ _ _

/-! ### The Cartesian square, modulo the base-change morphism of Tag 01LX -/

/-- **[Stacks, Tag 0EY6], the Cartesian square for the relative spectrum of the extension
algebra**, stated against an arbitrary morphism `bc` of relative spectra whose square over `g` is
Cartesian.  At `bc = relativeSpectrumBaseChangeMap s g` and its square
([Stacks, Tag 01LX], base change) this *is* the last clause of the flat-base-change part of
[Stacks, Tag 0EY6];  that morphism is the one piece of the clause absent from this library, so
the clause is recorded here in the form that the single missing input completes.

The content is that the comparison of the two relative spectra over `X'` is an isomorphism over
`X'` (`isIso_extendedEtaleSpectrumComparison` and
`extendedEtaleSpectrumComparison_toBase`), so the square for the extension of scalars `d`
transports to the square for the extension algebra of the base-changed cover. -/
public theorem extendedEtaleSpectrum_flatBaseChange_of_isPullback {U X V U' X' V' : Scheme.{u}}
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
        (X.presheaf.stalk x))
    (d : AlgebraPullback (ExtendedEtaleFold.extendedEtaleSituation j π hdepth) g)
    (bc : (gluedSpectrum d.situation).scheme ⟶
      (gluedSpectrum (ExtendedEtaleFold.extendedEtaleSituation j π hdepth)).scheme)
    (hbc : IsPullback (gluedSpectrum d.situation).toBase bc g
      (gluedSpectrum (ExtendedEtaleFold.extendedEtaleSituation j π hdepth)).toBase) :
    let s := ExtendedEtaleFold.extendedEtaleSituation j π hdepth
    let e := ExtendedEtaleFold.extendedEtaleSituation j' π'
      (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth)
    IsPullback (gluedSpectrum e).toBase
      (extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth d ≫ bc)
      g (gluedSpectrum s).toBase := by
  have := isIso_extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth d
  exact isPullback_comp_of_isIso hbc
    (extendedEtaleSpectrumComparison j π g j' gU π' gV hj hπ hdepth d)
    (extendedEtaleSpectrumComparison_toBase j π g j' gU π' gV hj hπ hdepth d)

end Stacks.FundamentalGroup

end
