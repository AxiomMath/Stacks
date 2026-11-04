module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsUniverseLift
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology sheaves of the naive cotangent complex of a morphism of algebraic spaces

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`.  Stacks 0D0Y
asserts that the cohomology sheaves of the naive cotangent complex `NL_{X/Y}` of Stacks 0D0V are
quasi-coherent, that they vanish outside degrees `-1` and `0`, and that the degree-`0` cohomology
sheaf is the sheaf of differentials `Ω_{X/Y}`.  This file proves all three, for an arbitrary
morphism `f`, as `AlgebraicGeometry.Space.naiveCotangentComplex_homology`.

* **Degree `-1`.**  The degree `-1` cohomology sheaf is the kernel `𝒦` of the differential of
  `NL_{X/Y}`, and `AlgebraicGeometry.Space.isQuasicoherentOnSite_naiveCotangentKernel` proves it
  quasi-coherent: on a chart `V = Spec A` of `X` lying over a chart `W = Spec R` of `Y` it is the
  sheaf attached to the module `H₁(L_{A/R})`, by a comparison which is checked at the geometric
  points, where it is the base change map of Stacks 0D08.  The charts carrying such a diagram
  cover `X`.
* **Degree `0`.**  The degree `0` cohomology sheaf is the module of differentials of
  `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` (Stacks 08TY), and that module is the universe lift of the sheaf of
  differentials `Ω_{X/Y}` of Stacks 04CT
  (`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSiteIsoUlift`), which is
  quasi-coherent by Stacks 04CV.
* **Other degrees.**  `NL_{X/Y}` has no terms outside degrees `-1` and `0`.

## Main results

* `AlgebraicGeometry.Space.naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials`: the
  degree `0` cohomology sheaf of `NL_{X/Y}` is `Ω_{X/Y}`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_naiveCotangentComplex`: every
  cohomology sheaf of `NL_{X/Y}` is quasi-coherent.
* `AlgebraicGeometry.Space.naiveCotangentComplex_homology`: **Stacks 0D0Y**.

## Implementation notes

The small étale site of an algebraic space over `S : Scheme.{u}` has its objects in
`Type (u + 1)` and its structure rings in `Type u`, so the sections of `NL_{X/Y}` and of its
cohomology sheaves lie in `Type (u + 1)`, while `Ω_{X/Y}` of Stacks 04CT has its sections in
`Type u`.  The degree `0` clause therefore compares the degree `0` cohomology sheaf with the
universe lift `SheafOfModules.uliftForPresentation` of `Ω_{X/Y}`, which changes nothing but the
universe of the sections.

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 04CV](https://stacks.math.columbia.edu/tag/04CV)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The degree `0` cohomology sheaf of `NL_{X/Y}` is `Ω_{X/Y}`**, the sheaf of differentials
of Stacks 04CT, with its sections lifted to the universe of the sections of `NL_{X/Y}`. -/
def naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials :
    (naiveCotangentComplex B S hS f).homology 0 ≅
      SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (sheafOfDifferentials B S hS f) :=
  naiveCotangentComplexHomologyZeroIso B S hS f ≪≫
    SheafOfModules.moduleOfDifferentialsOfSiteIsoUlift.{u, u, u, u + 1}
      (structureSharpInverseImage B S hS f)

/-- **The degree `0` cohomology sheaf of `NL_{X/Y}` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_homology_zero_naiveCotangentComplex :
    ((naiveCotangentComplex B S hS f).homology 0).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials B S hS f).symm
    (SheafOfModules.isQuasicoherentOnSite_uliftForPresentation
      (isQuasicoherentOnSite_sheafOfDifferentials B S hS f))

/-- **Every cohomology sheaf of `NL_{X/Y}` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_homology_naiveCotangentComplex (i : ℤ) :
    ((naiveCotangentComplex B S hS f).homology i).IsQuasicoherentOnSite := by
  by_cases hneg : i = -1
  · subst hneg
    exact isQuasicoherentOnSite_homology_negOne_naiveCotangentComplex B S hS f
  by_cases hzero : i = 0
  · subst hzero
    exact isQuasicoherentOnSite_homology_zero_naiveCotangentComplex B S hS f
  exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
    (isZero_homology_naiveCotangentComplex B S hS f i hneg hzero)

/-- **Stacks 0D0Y.**  Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`.  The cohomology sheaves of the naive cotangent complex `NL_{X/Y}` are quasi-coherent,
zero outside degrees `-1` and `0`, and equal to `Ω_{X/Y}` in degree `0`.

`Ω_{X/Y}` is the sheaf of differentials of Stacks 04CT, with its sections lifted to the universe
of the sections of `NL_{X/Y}`; see the implementation notes. -/
@[stacks 0D0Y]
theorem naiveCotangentComplex_homology :
    (∀ i : ℤ, ((naiveCotangentComplex B S hS f).homology i).IsQuasicoherentOnSite) ∧
      (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero ((naiveCotangentComplex B S hS f).homology i)) ∧
      Nonempty ((naiveCotangentComplex B S hS f).homology 0 ≅
        SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (sheafOfDifferentials B S hS f)) :=
  ⟨isQuasicoherentOnSite_homology_naiveCotangentComplex B S hS f,
    isZero_homology_naiveCotangentComplex B S hS f,
    ⟨naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials B S hS f⟩⟩

end AlgebraicGeometry.Space
