module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoofUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.LocalizationFromComplexes
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentativeUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `S⁻¹K^b(A) = D_perf(𝒪_X)`, where no hypothesis is left over

The last clause of [Stacks, Tag 0F8I] is that the canonical functor `K^b(A) ⥤ D_perf(𝒪_X)`
factors through an equivalence `S⁻¹K^b(A) ⥤ D_perf(𝒪_X)`, which is
`CategoryTheory.Functor.IsLocalization` for the system `S` of quasi-isomorphisms.
`StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/LocalizationFromComplexes.lean`
reduces it to the complex-level forms of [Stacks, Tag 0F8F], [Stacks, Tag 0F8G] and
[Stacks, Tag 0F8H]; this file discharges those.

Each of the three is proved in this library for a scheme with *affine diagonal*, and the
affine diagonal now follows from the source's own hypotheses: [Stacks, Tag 0F8C] is
unconditional, the converse of [Stacks, Tag 0F8B] it rests on being available at Noetherian
stages (`AlgebraicGeometry.hasResolutionProperty_stage`).  So the localization predicate is
proved here on a scheme with affine diagonal, on the classes of schemes where that is automatic
(separated, Noetherian, carrying an ample invertible module, affine), and — this being the clause
of the tag — under exactly the source's hypotheses.

Only the last carries the Stacks tag.  The hypotheses of the other five are *narrower* than the
source's, so each is a special case of Tag 0F8I and not the statement of it.

## Main results

* `perfectComplexFunctor_isLocalization_of_affineDiagonal`: the localization predicate on a
  quasi-compact quasi-separated scheme with the resolution property and affine diagonal.
* `..._of_isSeparated`, `..._of_isNoetherian`, `..._of_isAmple`, `..._of_isAffine`: the same with
  the affine diagonal discharged.
* `..._spec` and `..._projectiveSpace`: the predicate at two instances with every binder filled
  in — `Spec R` for an arbitrary ring and `ℙⁿ_S` for an affine base.  They assume nothing at all,
  so they are what shows the statement is not vacuous; `ℙⁿ_S` is there because an affine scheme
  would leave the witness inside a class where the quasi-coherent comparison is full for trivial
  reasons.
* `..._of_hasResolutionProperty`: **the equivalence clause of [Stacks, Tag 0F8I]** — the
  predicate under exactly the source's hypotheses on `X` and nothing else.

## Implementation notes

The reductions are the ones the two sibling `Unconditional` files use: separatedness makes the
diagonal a closed immersion, hence affine; the Noetherian case of [Stacks, Tag 0F8C] gives the
affine diagonal outright; and an ample invertible module gives quasi-compactness, the resolution
property ([Stacks, Tag 0F87]) and separatedness at once.  Nothing is restated here — the three
complex-level inputs are the `_of_affineDiagonal` forms in
`StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/PerfectRepresentative.lean`, `StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/DerivedRoof.lean` and `StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/DerivedHomotopy.lean`.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0F8H](https://stacks.math.columbia.edu/tag/0F8H)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
* [Stacks Project, Tag 0F8B](https://stacks.math.columbia.edu/tag/0F8B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.AmpleProjectiveImmersion
open Stacks.ProjectiveSpace

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`K^b(A) ⥤ D_perf(𝒪_X)` presents `D_perf(𝒪_X)` as `S⁻¹K^b(A)`, for a scheme with affine
diagonal.**  The three inputs are the affine-diagonal forms of [Stacks, Tag 0F8F],
[Stacks, Tag 0F8G] and [Stacks, Tag 0F8H]. -/
theorem perfectComplexFunctor_isLocalization_of_affineDiagonal (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  perfectComplexFunctor_isLocalization_of_complexes X
    (exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X)
    (exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X)
    (exists_boundedFiniteLocallyFree_homotopy_of_affineDiagonal X)

/-- **`S⁻¹K^b(A) = D_perf(𝒪_X)` on a quasi-compact separated scheme with the resolution
property.**  A separated scheme has a closed, hence affine, diagonal. -/
theorem perfectComplexFunctor_isLocalization_of_isSeparated (X : Scheme.{u})
    [CompactSpace X] [X.IsSeparated] [HasResolutionProperty X] :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  perfectComplexFunctor_isLocalization_of_affineDiagonal X

/-- **`S⁻¹K^b(A) = D_perf(𝒪_X)` on a Noetherian scheme with the resolution property.**  The
affine diagonal comes from the Noetherian case of [Stacks, Tag 0F8C], which assumes nothing
beyond the resolution property. -/
theorem perfectComplexFunctor_isLocalization_of_isNoetherian (X : Scheme.{u})
    [IsNoetherian X] [HasResolutionProperty X] :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  have _ : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  have _ := isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian X
  perfectComplexFunctor_isLocalization_of_affineDiagonal X

/-- **`S⁻¹K^b(A) = D_perf(𝒪_X)` on a scheme carrying an ample invertible module.**  Ampleness
supplies quasi-compactness, the resolution property ([Stacks, Tag 0F87]) and separatedness, hence
the affine diagonal, so no hypothesis on the scheme beyond the ample module is left. -/
@[sga "6 0 3.1" "more general"]
theorem perfectComplexFunctor_isLocalization_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  have _ : CompactSpace X := hL.1
  have _ : HasResolutionProperty X := hasResolutionProperty_of_isAmple L hL
  have _ : X.IsSeparated :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL).isSeparated
  perfectComplexFunctor_isLocalization_of_isSeparated X

/-- **`S⁻¹K^b(A) = D_perf(𝒪_X)` on an affine scheme.**  The structure sheaf is ample, so every
hypothesis on the scheme is discharged. -/
theorem perfectComplexFunctor_isLocalization_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  perfectComplexFunctor_isLocalization_of_isAmple X (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X)

/-- **`S⁻¹K^b(A) = D_perf(𝒪_{Spec R})` for an arbitrary ring `R`.**  Every binder of the clause is
filled in and nothing is assumed: this is the instance at which the clause is exhibited as not
vacuous. -/
theorem perfectComplexFunctor_isLocalization_spec (R : CommRingCat.{u}) :
    (perfectComplexFunctor (Spec R)).IsLocalization (quasiIsomorphisms (Spec R)) :=
  perfectComplexFunctor_isLocalization_of_isAffine (Spec R)

/-- **`S⁻¹K^b(A) = D_perf(𝒪_X)` for `X = ℙⁿ_S` with `S` affine.**  Every binder is filled in, at a
scheme that is not affine: the hyperplane sheaf `𝒪(1)` is ample on `ℙⁿ_S`. -/
theorem perfectComplexFunctor_isLocalization_projectiveSpace (n : ℕ) (S : Scheme.{u})
    [IsAffine S] :
    (perfectComplexFunctor (projectiveSpaceOver n S)).IsLocalization
      (quasiIsomorphisms (projectiveSpaceOver n S)) :=
  perfectComplexFunctor_isLocalization_of_isAmple (projectiveSpaceOver n S)
    (projectiveSpaceTwistingSheaf n S) (isAmple_projectiveSpaceTwistingSheaf n S)

/-- **The equivalence clause of [Stacks, Tag 0F8I].**  On a quasi-compact and quasi-separated
scheme with the resolution property, the canonical functor `K^b(A) ⥤ D_perf(𝒪_X)` presents
`D_perf(𝒪_X)` as the localization of `K^b(A)` at the quasi-isomorphisms.

The three assumptions on `X` are exactly the source's.  The affine diagonal is supplied
by [Stacks, Tag 0F8C] (`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`), which
rests on the converse of [Stacks, Tag 0F8B] at Noetherian stages
(`AlgebraicGeometry.hasResolutionProperty_stage`). -/
@[stacks 0F8I "the canonical functor presents the perfect derived category as the localization \
of the bounded homotopy category at the quasi-isomorphisms"]
theorem perfectComplexFunctor_isLocalization_of_hasResolutionProperty (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X] :
    (perfectComplexFunctor X).IsLocalization (quasiIsomorphisms X) :=
  have := HasResolutionProperty.isAffineHom_diagonal X
  perfectComplexFunctor_isLocalization_of_affineDiagonal X

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
