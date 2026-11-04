module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic

/-!
# Finite dimensionality of the cohomology of a coherent module on a proper scheme over a field

Let `k` be a field, let `f : X ⟶ Spec k` be proper and let `F` be a coherent `𝒪_X`-module. Then
`Hⁿ(X, F)`, with the `k`-module structure of `AlgebraicGeometry.cohomologyOverField`, is a
finite-dimensional `k`-vector space. This is [Stacks, Tag 02O6] over the base `Spec k`.

## Main results

* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`: for `f : X ⟶ Spec k`
  proper and `F` coherent, `Hⁿ(X, F)` is a finite-dimensional `k`-vector space.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`: the same
  statement for all coherent modules and all degrees at once.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase

universe u

namespace AlgebraicGeometry

/-- Let `k` be a field, let `f : X ⟶ Spec k` be proper and let `F` be a coherent `𝒪_X`-module.
Then `Hⁿ(X, F)`, as a `k`-module through `AlgebraicGeometry.cohomologyOverField`, is a
finite-dimensional `k`-vector space, for every `n`. -/
theorem finiteDimensional_cohomologyOverField_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [F.IsCoherent]
    (n : ℕ) : FiniteDimensional k (cohomologyOverField k f F n) := by
  rw [cohomologyOverField_eq_restrictScalars_appTop k f F n]
  have hA := ProperCoherenceWitness.moduleFinite_cohomology f F n
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))

/-- Let `k` be a field and let `f : X ⟶ Spec k` be proper. Then for every coherent `𝒪_X`-module
`G` and every `n`, `Hⁿ(X, G)` is a finite-dimensional `k`-vector space. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] :
    ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) := fun G hG n =>
  have := hG
  finiteDimensional_cohomologyOverField_of_isProper k f G n

end AlgebraicGeometry

end
