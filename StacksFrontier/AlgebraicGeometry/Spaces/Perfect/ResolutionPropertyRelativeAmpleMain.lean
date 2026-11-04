module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleChartEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple

/-!
# Stacks 0GUT: the resolution property along a morphism carrying an invertible relatively ample
module

**Stacks 0GUT.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Assume

1. `Y` is quasi-compact, quasi-separated and has the resolution property, and
2. there is an `f`-ample **invertible** `𝒪_X`-module `L` (Stacks 0D31).

Then `X` has the resolution property.

This file assembles the proof out of the steps prepared in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleTwist` (the twist
and its chart sections, and untwisting) and
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleChartEpi` (the
finite locally free module surjecting onto a twist), on the chart that
`AlgebraicGeometry.Space.exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple`
chooses.

## Main results

* `AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_of_isRelativelyAmple`: under the
  hypotheses of Stacks 0GUT, every quasi-coherent `𝒪_X`-module of finite type is the target of an
  epimorphism from a finite locally free `𝒪_X`-module.
* `AlgebraicGeometry.Space.hasResolutionProperty_source_of_isRelativelyAmple`: **Stacks 0GUT**,
  that statement packaged as `AlgebraicGeometry.Space.HasResolutionProperty` of `X`.

## Implementation notes

**The hypotheses are exactly (1) and (2), and nothing more.**

* `hLinv : AlgebraicGeometry.Space.IsInvertibleModule X L` and
  `hL : AlgebraicGeometry.Space.IsRelativelyAmple B S hS f L` are the two halves of (2).
  Invertibility is part of the hypothesis of Stacks 0GUT, not an addition: Stacks 0D31 defines
  `f`-ampleness of a module on an algebraic space by invertibility and relative ampleness of its
  base changes to scheme charts, and the tag asks for an *invertible* `f`-ample module.  In this
  tree `AlgebraicGeometry.Space.IsRelativelyAmple` records the invertibility of those base
  changes only, so invertibility of `L` itself is carried separately — and it is what makes
  `AlgebraicGeometry.Space.intTensorPowModule`, hence the negative powers the proof untwists by,
  exist at all.  The statements
  `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmpleSmall` and
  `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple` of this tree quantify over `L`
  with relative ampleness alone and are therefore *stronger* than Stacks 0GUT; proving them would
  additionally need descent of invertibility along the chart, which is a separate statement and
  no part of this tag.
* `hYqc`, `hYqs` and `hYres` are (1).  Quasi-separatedness of `Y` is Stacks 03BS (3),
  `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`, whose statement needs the containment
  `hZ : B.Contains (⊤_ Scheme.{u})` of the terminal scheme in the ambient site; `hZ` is a property
  of the site, not of `f` or `Y`, and is used for nothing else.

Quasi-compactness and quasi-separatedness of `f` itself are **not** hypotheses: they are
Stacks 0D34 for `L`, by `AlgebraicGeometry.Space.IsRelativelyAmple.isQuasiCompact` and
`AlgebraicGeometry.Space.IsRelativelyAmple.isSeparated` followed by Stacks 03KK.

**The module universe.** Everything is at `AlgebraicGeometry.Space.Modules.{u, u}`, the module
universe of the schemes.  That is forced twice over: `AlgebraicGeometry.Space.modulePushforward`
and `AlgebraicGeometry.Space.modulePullback` are defined only there, and so are the tensor powers
`AlgebraicGeometry.Space.intTensorPowModule`.  The conclusion is accordingly
`AlgebraicGeometry.Space.HasResolutionProperty.{u, u}`, which is how
`AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmpleSmall` reads the resolution
property too.

**The shape of the resolution produced.**  For `𝓕` quasi-coherent of finite type the resolution is
`f^*ℰ ⊗ L^{⊗ -n} ⟶ 𝓕` for a finite locally free `𝒪_Y`-module `ℰ` and an `n` large enough for
Stacks 01Q3 (7) on the chart; the source is finite locally free by Stacks 03DL (2) for a tensor
product (`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorObj`) out of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_intTensorPowModule` and the finite local
freeness of `f^*ℰ`.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D34](https://stacks.math.columbia.edu/tag/0D34)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GUT, for one module.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over a
scheme with `Y` quasi-compact, quasi-separated and carrying the resolution property, and let `L`
be an invertible `f`-ample `𝒪_X`-module.  Then every quasi-coherent `𝒪_X`-module `𝓕` of finite
type is the target of an epimorphism from a finite locally free `𝒪_X`-module.

The proof is the source's.  Stacks 03H6 gives an affine scheme `V` with a surjective étale
morphism to `Y`, and relative ampleness presents `V ×_Y X` as a scheme `U`, an étale chart of `X`
on whose scheme `L` restricts to an ample module
(`AlgebraicGeometry.Space.exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple`
and `AlgebraicGeometry.Space.isAmple_chartRestrictionSchemeModule_of_isRelativelyAmple`).  On that
chart Stacks 01Q3 (7) generates the twist `𝓕 ⊗ L^{⊗ n}` for `n` large, in the form
`AlgebraicGeometry.Space.exists_chartSections_hgen_sheafTensor_intTensorPowModule_of_isAmple`;
`AlgebraicGeometry.Space.exists_finiteLocallyFree_modulePullback_epi_of_chartSections` turns that
into an epimorphism `f^*ℰ ⟶ 𝓕 ⊗ L^{⊗ n}` with `ℰ` finite locally free on `Y`; and
`AlgebraicGeometry.Space.epi_sheafTensorIntTensorPowUntwistMap` untwists it to an epimorphism
`f^*ℰ ⊗ L^{⊗ -n} ⟶ 𝓕`. -/
theorem exists_finiteLocallyFree_epi_of_isRelativelyAmple (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : IsInvertibleModule X L) (hL : IsRelativelyAmple B S hS f L)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (ψ : E ⟶ F), Epi ψ := by
  have := hLinv
  have := hFqc
  obtain ⟨V, gV, hVaff, hVsurj, hVet, U, q, p, hsq, -, -⟩ :=
    exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple hL hYqc
  obtain ⟨_hinv, hamp⟩ :=
    isAmple_chartRestrictionSchemeModule_of_isRelativelyAmple B S hS X L hLinv hL hVaff hVet hsq
  obtain ⟨n₀, hn₀⟩ := exists_chartSections_hgen_sheafTensor_intTensorPowModule_of_isAmple B S hS X L
    (chartDiagramOfIsPullback B S hS f q p gV hVet hsq).U hamp F hFft
  obtain ⟨I, hI, a, hgen⟩ := hn₀ n₀ le_rfl
  have := hI
  obtain ⟨E, hflf, ψ, hψ⟩ :=
    exists_finiteLocallyFree_modulePullback_epi_of_chartSections hZ f hL.isQuasiCompact
      (isQuasiSeparated_of_isSeparated B S hS hL.isSeparated) hYqc hYqs hYres _
      (isQuasicoherentOnSite_sheafTensor_intTensorPowModule B S hS X L F n₀)
      (chartDiagramOfIsPullback B S hS f q p gV hVet hsq) hsq hVaff
      (isSurjective_etaleChartOfIsPullback B S hS X hVet hVsurj hsq) a hgen
  exact ⟨(modulePullback B S hS f).obj E ⊗ intTensorPowModule B S hS X L (-n₀),
    isFiniteLocallyFreeOnSite_tensorObj B S hS X.1 X.2 _ _ hflf
      (isFiniteLocallyFreeOnSite_intTensorPowModule B S hS X L (-n₀)),
    sheafTensorIntTensorPowUntwistMap B S hS X L F _ n₀ ψ,
    epi_sheafTensorIntTensorPowUntwistMap B S hS X L F _ n₀ ψ hψ⟩

/-- **Stacks 0GUT.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` such
that `Y` is quasi-compact, quasi-separated and has the resolution property, and such that there
is an `f`-ample invertible `𝒪_X`-module `L`.  Then `X` has the resolution property.

This is `AlgebraicGeometry.Space.exists_finiteLocallyFree_epi_of_isRelativelyAmple` packaged as
the class `AlgebraicGeometry.Space.HasResolutionProperty` of Stacks 0GUS.

The hypotheses are exactly the tag's.  `hLinv` is part of hypothesis (2): Stacks 0D31 defines an
`f`-ample module to be invertible, and in this tree `IsRelativelyAmple` records invertibility only
of the base changes of `L` to the scheme charts, so it is carried separately.  `hZ` is needed only
to state `IsAbsolutelyQuasiSeparated`, this tree's spelling of quasi-separatedness of `Y`.
Quasi-compactness and quasi-separatedness of `f` are *derived* from `hL` by Stacks 0D34 and 03KK,
not assumed. -/
@[stacks 0GUT]
theorem hasResolutionProperty_source_of_isRelativelyAmple (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : IsInvertibleModule X L) (hL : IsRelativelyAmple B S hS f L)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, u} B S hS X.1 X.2 := by
  constructor
  intro M _
  exact exists_finiteLocallyFree_epi_of_isRelativelyAmple hZ f L hLinv hL hYqc hYqs hYres
    M.obj M.property inferInstance

end AlgebraicGeometry.Space

end
