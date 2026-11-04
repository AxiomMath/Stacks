module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocalKunneth
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras

/-!
# The comparison of Section 0FMK is an isomorphism, with no splitting assumed

Let `f : X ⟶ Y` be a smooth morphism of schemes over a base `S` and `n = k + 1 + m`. [Stacks,
Section 0FMK] asserts that the canonical morphism

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`

is an isomorphism. `StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece` proves it for a
short exact sequence that *splits*, and the transitivity sequence of a smooth morphism splits
only locally; `StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras` carries
the comparison across restriction to an open subspace and reduces the general case to a splitting
over the members of an open covering. This file joins the two: it converts a splitting of the
restricted presentation from Mathlib's restriction along the open immersion to the spelling the
crossing is stated at, and concludes the section's claim for every smooth `f`, with no splitting
and no local hypothesis of any kind.

## Main results

* `SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor`: **a splitting of a short
  complex restricted along an open immersion splits the restriction to the open subspace** —
  `SheafOfModules.openSubspaceRestrictionIsoRestrictFunctor` read as an isomorphism of short
  complexes and `CategoryTheory.ShortComplex.Splitting.ofIso`. This is the only thing between the
  local splitting of [Stacks, Tag 02G1] and the globalization of Section 0FMK.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsExteriorGradedComparison`:
  **`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ≅ gr^kΩ^n_{X/S}` for every smooth `f`** — the
  statement of [Stacks, Section 0FMK].

## Implementation notes

Every figure is a measurement against the default budget of 200,000 heartbeats, taken on this
branch. No compiler option is set and no heartbeat limit is raised.

| declaration | heartbeats |
| --- | --- |
| `openSubspaceShortComplexSplittingOfRestrictFunctor` | 19,277 |
| `isIso_relativeDifferentialsExteriorGradedComparison` | 11,066 |

**Why the conversion is `CategoryTheory.ShortComplex.isoMk` and not `ShortComplex.mapNatIso`.**
The natural isomorphism `SheafOfModules.openSubspaceRestrictionIsoRestrictFunctor` would give the
isomorphism of short complexes in one step as `S.mapNatIso`, but that expression is
`CategoryTheory.ShortComplex.map` of *both* functors at once, and each functor's
`[Functor.PreservesZeroMorphisms]` is findable only at its own spelling of the category of
`𝒪_X`-modules — the measurements are in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Modules.ExteriorGradedOpenSubspaceAlgebras`. Built by hand from
the isomorphism's components and the naturality of its inverse, only the `restrictFunctor` side is
a `ShortComplex.map`, the other side is the `CategoryTheory.ShortComplex.mk` of
`SheafOfModules.openSubspaceShortComplex`, and no instance is wanted at a spelling that does not
carry it.

**The short complex is stated at `X.Modules`, not at `SheafOfModules.structureSheafRing`.** That
is the spelling in which `S.map (Scheme.Modules.restrictFunctor U.ι)` elaborates, and it is the
one `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsShortComplex` is written at; passing such a
complex to `SheafOfModules.openSubspaceShortComplex`, whose binder is the `structureSheafRing`
spelling, costs 1,467 heartbeats, and that is the only
place the two spellings meet.

**No `@[stacks]` attribute.** The tags of the graded piece are carried by the declarations in
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece`.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits AlgebraicGeometry Opposite
  PresheafOfModules TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)

universe u

namespace SheafOfModules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- **A splitting of a short complex of `𝒪_X`-modules restricted along the open immersion of an
open `U` splits the complex restricted to the open subspace `U`.** The two spellings of
restriction are isomorphic as functors
(`SheafOfModules.openSubspaceRestrictionIsoRestrictFunctor`), so applying the isomorphism
componentwise and using the naturality of its inverse for the two commuting squares identifies
the two restricted complexes, and `CategoryTheory.ShortComplex.Splitting.ofIso` carries the
splitting across.

This is what lets a consumer feed
`SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split` with the local splitting
`AlgebraicGeometry.Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict` produces,
which is stated at Mathlib's restriction. Costs 19,277 heartbeats against the default budget of
200,000; see the implementation notes for why it is not `CategoryTheory.ShortComplex.mapNatIso`. -/
def openSubspaceShortComplexSplittingOfRestrictFunctor (U : X.Opens)
    (sp : (S.map (Scheme.Modules.restrictFunctor U.ι)).Splitting) :
    (openSubspaceShortComplex (X := X.toRingedSpace) U (T := S)).Splitting :=
  sp.ofIso (ShortComplex.isoMk
    ((openSubspaceRestrictionIsoRestrictFunctor X U).symm.app S.X₁)
    ((openSubspaceRestrictionIsoRestrictFunctor X U).symm.app S.X₂)
    ((openSubspaceRestrictionIsoRestrictFunctor X U).symm.app S.X₃)
    ((openSubspaceRestrictionIsoRestrictFunctor X U).inv.naturality S.f).symm
    ((openSubspaceRestrictionIsoRestrictFunctor X U).inv.naturality S.g).symm)

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- **Stacks Project, Section 0FMK.** For `f : X ⟶ Y` smooth over a base `S` and `n = k + 1 + m`
the canonical morphism

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`

is an isomorphism. Nothing is assumed beyond smoothness of `f`: no splitting of the transitivity
sequence `0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` is chosen and no open is fixed.

The sequence is short exact by [Stacks, Tags 06B6 and 02K4] and its quotient `Ω_{X/Y}` is finite
locally free by [Stacks, Tag 02G1], so it splits over an open neighbourhood of every point
(`AlgebraicGeometry.Scheme.Hom.exists_nonempty_splitting_relativeDifferentialsRestrict`); each of
those splittings splits the presentation restricted to the open subspace
(`SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor`); and a splitting over the
members of an open covering makes the comparison an isomorphism
(`SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split`), because invertibility
reduces to monomorphy of the quotient-level form, that is local, and the quotient-level form
crosses restriction to an open subspace.

Costs 11,066 heartbeats against the default budget of 200,000. -/
theorem isIso_relativeDifferentialsExteriorGradedComparison (f : X ⟶ Y) (g : Y ⟶ S) [Smooth f]
    (k m : ℕ) : IsIso (relativeDifferentialsExteriorGradedComparison f g k m) :=
  _root_.SheafOfModules.isIso_exteriorGradedQuotientComparison_of_locally_split _ _ _ _ _ k m
    (fun x => (exists_nonempty_splitting_relativeDifferentialsRestrict f g x).imp
      (fun U h => ⟨h.1, h.2.map (fun sp =>
        _root_.SheafOfModules.openSubspaceShortComplexSplittingOfRestrictFunctor U sp)⟩))

end AlgebraicGeometry.Scheme.Hom

end
