module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.GlobalFunctions

/-!
# The cohomology of the structure sheaf of the Fermat quartic

Let `k` be a field and `X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k` the Fermat quartic. The ideal
sheaf sequence `0 → 𝒪(-4) → 𝒪 → i_* 𝒪_X → 0` and the cohomology of the twists of `𝒪` on
`𝐏³_k` give

* `H¹(X, 𝒪_X) ≅ H²(𝐏³_k, 𝒪(-4)) = 0`, and
* `H⁰(X, 𝒪_X) ≅ H⁰(𝐏³_k, 𝒪) = k`.

Hence the global functions on `X` are the constants, so `X`, being proper over `k`, is connected;
when `X` is smooth over `k` it is therefore integral.

## Main results

* `AlgebraicGeometry.FermatQuartic.isZero_structureSheafCohomology_one`: `H¹(X, 𝒪_X) = 0`.
* `AlgebraicGeometry.FermatQuartic.isZero_cohomology_one_unit`: the same, for the right derived
  functor of evaluation on the whole space.
* `AlgebraicGeometry.FermatQuartic.nonempty_structureSheafCohomology_zero_iso`:
  `H⁰(X, 𝒪_X) ≅ k`.
* `AlgebraicGeometry.FermatQuartic.isIso_globalSections`: `k → Γ(X, 𝒪_X)` is an isomorphism.
* `AlgebraicGeometry.FermatQuartic.connectedSpace`: `X` is connected.
* `AlgebraicGeometry.FermatQuartic.isIntegral_fermatQuartic_of_smooth`: if `X` is smooth over
  `k`, it is integral.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveSpace.Cohomology

universe u

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k]

/-- **`H¹` of the structure sheaf of the Fermat quartic vanishes**: it is
`H²(𝐏³_k, 𝒪(-4)) = 0`. -/
theorem isZero_structureSheafCohomology_one :
    IsZero (AlgebraicGeometry.structureSheafCohomology (toSpec k) 1) := by
  obtain ⟨e⟩ := nonempty_structureSheafCohomologyIsoTwistCohomology k 3 1 4
    (toProjectiveSpace k) (fermatPolynomial k) (fermatPolynomial_ne_zero k)
    (ker_toProjectiveSpace k) (isZero_twistCohomology k 3 0 1 (by omega))
    (isZero_twistCohomology k 3 0 2 (by omega))
  exact e.isZero_iff.2 (isZero_twistCohomology k 3 _ _ (by omega))

/-- **`H¹(X, 𝒪_X) = 0` for the Fermat quartic**, for the right derived functor of evaluation on
the whole space, as a module over the global functions. -/
theorem isZero_cohomology_one_unit :
    IsZero (((SheafOfModules.evaluation (fermatQuartic k).ringCatSheaf
      (Opposite.op ⊤)).rightDerived 1).obj (SheafOfModules.unit _)) := by
  have h := (structureSheafCohomologyIsoCohomologyOverField k (toSpec k) 1).isZero_iff.1
    (isZero_structureSheafCohomology_one k)
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact h

/-- **`H⁰` of the structure sheaf of the Fermat quartic is `k`**: it is `H⁰(𝐏³_k, 𝒪) = k`, since
`H⁰` and `H¹` of `𝒪(-4)` on `𝐏³_k` vanish. -/
theorem nonempty_structureSheafCohomology_zero_iso :
    Nonempty (AlgebraicGeometry.structureSheafCohomology (toSpec k) 0 ≅ ModuleCat.of k k) := by
  obtain ⟨e⟩ := nonempty_structureSheafCohomologyIsoTwistCohomologyZero k 3 0 4
    (toProjectiveSpace k) (fermatPolynomial k) (fermatPolynomial_ne_zero k)
    (ker_toProjectiveSpace k) (isZero_twistCohomology k 3 _ 0 (by omega))
    (isZero_twistCohomology k 3 _ 1 (by omega))
  exact ⟨e ≪≫ twistCohomologyZeroIsoCoeff k 3⟩

/-- `H⁰(X, 𝒪_X)` of the Fermat quartic is one-dimensional over `k`. -/
theorem finrank_cohomologyOverField_unit_zero :
    Module.finrank k
      (cohomologyOverField k (toSpec k) (SheafOfModules.unit (fermatQuartic k).ringCatSheaf) 0) =
      1 := by
  obtain ⟨e⟩ := nonempty_structureSheafCohomology_zero_iso k
  exact (((structureSheafCohomologyIsoCohomologyOverField k (toSpec k) 0).symm ≪≫
    e).toLinearEquiv.finrank_eq).trans (Module.finrank_self k)

/-- **The global functions on the Fermat quartic are the constants**: the structure map
`k → Γ(X, 𝒪_X)` is an isomorphism. -/
instance isIso_globalSections : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k).appTop) :=
  isIso_globalSections_of_finrank_cohomologyOverField_unit_zero_eq_one (toSpec k)
    (finrank_cohomologyOverField_unit_zero k)

/-- The Fermat quartic is proper over `k`: it is a closed subscheme of `𝐏³_k`. -/
instance isProper_toSpec : IsProper (toSpec k) :=
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 3
  inferInstanceAs (IsProper (toProjectiveSpace k ≫ projToSpecCoeff k 3))

/-- **The Fermat quartic is connected**: its global functions are `k`. -/
instance connectedSpace : ConnectedSpace (fermatQuartic k) :=
  connectedSpace_of_isIso_globalSections k (toSpec k)

/-- **A smooth Fermat quartic is integral**: a connected scheme smooth over a field is
integral. -/
theorem isIntegral_fermatQuartic_of_smooth (h : Smooth (toSpec k)) :
    IsIntegral (fermatQuartic k) :=
  Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (toSpec k)

end AlgebraicGeometry.FermatQuartic

end
