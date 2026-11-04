module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.PerfectLift
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import Mathlib.CategoryTheory.Retract

/-!
# A perfect object on a quasi-compact open is a summand of a restriction

Let `X` be a quasi-compact quasi-separated scheme and `U ⊆ X` a quasi-compact open. Every perfect
object `P` of `D(𝒪_U)` is a direct summand of `R|_U` for some perfect object `R` of `D(𝒪_X)`:
[Stacks, Tag 09IQ].

## Main results

* `Stacks.Duality.OpenImmersion.exists_isPerfect_retract_derivedRestrict` — [Stacks, Tag 09IQ].

## Implementation notes

The source deduces the tag from [Stacks, Tag 09IM] for `T = X` and `E = 0`. The lifting step of
09IM, for a quasi-compact open of a quasi-compact quasi-separated scheme and an arbitrary target in
`D_QCoh(𝒪_X)`, is `Stacks.Duality.OpenImmersion.exists_isPerfect_lift`: it produces a perfect `R`
on `X` with `R|_U ≅ P ⊕ P[1]`. Taking the target to be `0` (whose cohomology sheaves are zero,
hence quasi-coherent) and reading off the first biproduct injection and projection exhibits `P`
as a retract of `R|_U`. "Direct summand" is `CategoryTheory.Retract`, which asserts nothing about
the complementary summand, exactly as the tag does.

The derived categories are those at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, where the lifting step lives; perfectness
is `Stacks.Cohomology.PerfectComplexes.IsPerfect`, and restriction is
`Stacks.Duality.OpenImmersion.derivedRestrict` along the inclusion `U.ι`.

The affine case, at the standard model and with a perfect *complex* on `X`, is
`Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_retract_restrict_of_isPerfect`.

## References

* [Stacks Project, Tag 09IQ](https://stacks.math.columbia.edu/tag/09IQ)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

universe u

namespace Stacks.Duality.OpenImmersion

/-- **[Stacks, Tag 09IQ].** Let `X` be a quasi-compact quasi-separated scheme and `U ⊆ X` a
quasi-compact open. Every perfect object `P` of `D(𝒪_U)` is a direct summand -- a retract -- of
the restriction to `U` of a perfect object `R` of `D(𝒪_X)`. -/
@[stacks 09IQ]
theorem exists_isPerfect_retract_derivedRestrict (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (P : DerivedCategory U.toScheme.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := U.toScheme.toRingedSpace) P) :
    ∃ R : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) R ∧
        Nonempty (Retract P ((derivedRestrict U.ι).obj R)) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  have : AlgebraicGeometry.QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
      ((QuasiSeparatedSpace.isRetrocompact_iff_isCompact U.isOpen).mpr hU))
  have h0 : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj 0).IsQuasicoherent := fun i =>
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules i).map_isZero (isZero_zero _)).isoZero.symm
      (isQuasicoherent_zero X)
  obtain ⟨R, e, -, hR, -⟩ := exists_isPerfect_lift U.ι P hP 0 h0 0
  exact ⟨R, hR, ⟨{ i := biprod.inl ≫ e.inv, r := e.hom ≫ biprod.fst, retract := by simp }⟩⟩

end Stacks.Duality.OpenImmersion

end
