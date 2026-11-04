module

public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Predicate
public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.Restriction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Finite presentation of a quasi-coherent algebra is local on the base

`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation` asks for finite
presentation of the structural ring map over *every* affine open of `X`.  This file shows the
condition is local: for a quasi-coherent algebra it can be checked on basic opens covering an
affine open, and hence on the members of any family of affine opens covering `X`.

The companion file `Stacks.QcohAlgebraFPColimit.Restriction` proves the other direction, that
the condition descends along an inclusion of affine opens; the two together are what make the
"every affine open" quantifier of [Stacks, Tag 05JS] a checkable condition rather than an
unbounded one.

## Main results

* `Stacks.FPAlgebraSheaf.finitePresentation_app_of_span`: **for a quasi-coherent algebra, if the
  structural ring map over an affine open `U` is of finite presentation over each basic open
  `D(f)`, `f` in a set spanning `Γ(X, U)`, then it is of finite presentation over `U`.**
* `Stacks.FPAlgebraSheaf.isLocalization_away_sections`: for a quasi-coherent algebra, the
  sections over a basic open `D(f)` of an affine open are the localization of the sections over
  that affine open away from the image of `f`.
* `Stacks.FPAlgebraSheaf.isOfFinitePresentation_of_iSup_eq_top`: **finite presentation of a
  quasi-coherent algebra follows from finite presentation over the members of a family of affine
  opens covering `X`.**

## Implementation notes

The localization statement is the content, and it is read off the base-change square of
[Stacks, Tag 01LN] already available as
`Stacks.RelativeSpec.AlgebraSheaf.isPushout_sections`: for affine opens `D(f) ≤ U` and `A`
quasi-coherent, `A(D(f)) = A(U) ⊗_{Γ(X, U)} Γ(X, D(f))`, and `Γ(X, D(f))` is `Γ(X, U)` localized
away from `f`.  `Algebra.isLocalization_iff_isPushout` turns the square into the assertion that
`A(D(f))` is `A(U)` localized at the image of the powers of `f`, which
`Algebra.algebraMapSubmonoid_powers` rewrites into a localization away from the image of `f`.

With that, locality over an affine open is Mathlib's
`RingHom.OfLocalizationSpan.ofIsLocalization` applied to
`RingHom.finitePresentation_isLocal.ofLocalizationSpan`.  That form of the hypothesis is what
makes the proof short: it accepts arbitrary rings carrying `IsLocalization.Away` instances
rather than demanding the literal `Localization.Away`, so no transport along a localization
comparison isomorphism is needed, and the commuting square it also asks for is the naturality of
the structure morphism of `A`.

Passing from a cover of `X` to an arbitrary affine open `V` uses
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` to cover `V` by basic opens of `V`, each
contained in a member of the cover; finite presentation over such a basic open comes from
`Stacks.QcohAlgebraFPColimit.finitePresentation_app_of_le`, and the basic opens exhaust `V`, so
`AlgebraicGeometry.IsAffineOpen.basicOpen_union_eq_self_iff` returns the spanning set that
`finitePresentation_app_of_span` consumes.  No quasi-compactness is used anywhere: the spanning
set may be infinite.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.FPAlgebraSheaf

variable {X : Scheme.{u}}

/-- **For a quasi-coherent algebra, the sections over a basic open of an affine open are a
localization of the sections over that affine open.**  This is the base-change square of
[Stacks, Tag 01LN] read as a localization: `A(D(f)) = A(U) ⊗_{Γ(X, U)} Γ(X, U)_f`. -/
theorem isLocalization_away_sections (A : AlgebraSheaf X) [A.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI := AlgebraSheaf.algebraRestrict A (X.basicOpen_le f)
    IsLocalization.Away ((A.hom.hom.app (op U)).hom f)
      (AlgebraSheaf.sections A (X.basicOpen f)) := by
  let _ := AlgebraSheaf.algebraSections A U
  let _ := AlgebraSheaf.algebraSections A (X.basicOpen f)
  let _ := AlgebraSheaf.algebraRestrict A (X.basicOpen_le f)
  let _ := AlgebraSheaf.algebraSectionsOfLE A (X.basicOpen_le f)
  let _ := AlgebraSheaf.isScalarTower_restrict A (X.basicOpen_le f)
  let _ := AlgebraSheaf.isScalarTower_sections A (X.basicOpen_le f)
  let _ := hU.isLocalization_basicOpen f
  have h : IsLocalization
      (Algebra.algebraMapSubmonoid (AlgebraSheaf.sections A U) (Submonoid.powers f))
      (AlgebraSheaf.sections A (X.basicOpen f)) :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers f) Γ(X, X.basicOpen f)).mpr
      (AlgebraSheaf.isPushout_sections A (hU.basicOpen f) hU (X.basicOpen_le f)).symm
  rwa [Algebra.algebraMapSubmonoid_powers] at h

/-- **Finite presentation of a quasi-coherent algebra over an affine open follows from finite
presentation over basic opens covering it.**  The sections over `D(f)` are the sections over `U`
localized away from the image of `f` (`isLocalization_away_sections`), and finite presentation of
ring maps satisfies `RingHom.OfLocalizationSpan`. -/
theorem finitePresentation_app_of_span (A : AlgebraSheaf X) [A.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤)
    (hfp : ∀ f : s, RingHom.FinitePresentation
      (A.hom.hom.app (op (X.basicOpen f.1))).hom) :
    RingHom.FinitePresentation (A.hom.hom.app (op U)).hom := by
  refine RingHom.OfLocalizationSpan.ofIsLocalization
    RingHom.finitePresentation_isLocal.ofLocalizationSpan
    RingHom.finitePresentation_respectsIso _ s hs fun f ↦ ?_
  refine ⟨Γ(X, X.basicOpen f.1), AlgebraSheaf.sections A (X.basicOpen f.1), inferInstance,
    inferInstance, algebraOfLE X (X.basicOpen_le f.1),
    AlgebraSheaf.algebraRestrict A (X.basicOpen_le f.1), hU.isLocalization_basicOpen f.1,
    isLocalization_away_sections A hU f.1, (A.hom.hom.app (op (X.basicOpen f.1))).hom, ?_,
    hfp f⟩
  ext x
  exact congr($(AlgebraSheaf.presheaf_map_comp_app A (X.basicOpen_le f.1)).hom x)

/-- **Finite presentation of a quasi-coherent algebra is local on the base.**  It suffices to
know finite presentation over the members of a family of affine opens covering `X`: an arbitrary
affine open is covered by its own basic opens, each inside a member of the family, and finite
presentation descends to those by base change and then rises to the affine open by
`finitePresentation_app_of_span`. -/
theorem isOfFinitePresentation_of_iSup_eq_top (A : X.QuasicoherentAlgebra)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] {ι : Type*} (W : ι → X.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hcov : ⨆ i, W i = ⊤)
    (hfp : ∀ i, RingHom.FinitePresentation (A.hom.hom.app (op (W i))).hom) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation A := by
  intro V hV
  -- The basic opens of `V` that lie inside some member of the cover.
  set s : Set Γ(X, V) := {f | ∃ i, X.basicOpen f ≤ W i} with hsdef
  have hspan : Ideal.span s = ⊤ := by
    rw [← hV.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f ↦ X.basicOpen_le f.1) fun x hx ↦ ?_
    obtain ⟨i, hxi⟩ : ∃ i, x ∈ W i := by
      have hx' : x ∈ (⨆ i, W i) := hcov ▸ (show x ∈ (⊤ : X.Opens) from trivial)
      exact TopologicalSpace.Opens.mem_iSup.mp hx'
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W i) ⟨x, hxi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hfW⟩, hxf⟩
  refine finitePresentation_app_of_span A hV s hspan fun f ↦ ?_
  obtain ⟨i, hfW⟩ := f.2
  exact Stacks.QcohAlgebraFPColimit.finitePresentation_app_of_le A
    (hV.basicOpen f.1) (hW i) hfW (hfp i)

end Stacks.FPAlgebraSheaf
