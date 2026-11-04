module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IntegralGenericWitness
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.RankN
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic of `ℰ ⊗ ℱ` on a proper curve

Let `X` be a proper curve over a field `k`, let `ℰ` be a finite locally free `𝒪_X`-module of rank
`n` and let `ℱ` be a coherent `𝒪_X`-module. If the cohomology over `k` of `𝒪_X` and of every
coherent module supported in a proper closed subset is finite-dimensional, then
`χ(X, ℰ ⊗ ℱ) = r·deg(ℰ) + n·χ(X, ℱ)`, where `r` is the rank of `ℱ` at the generic point.

## Main results

* `exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6`: the formula
  `χ(X, ℰ ⊗ ℱ) = r·deg(ℰ) + n·χ(X, ℱ)` under the two finiteness hypotheses.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Let `k` be a field, let `X` be a proper curve over `k` with generic point `ξ`, let `ℰ` be
locally free of rank `n` and let `ℱ` be coherent. If the cohomology over `k` of `𝒪_X` (`hunit`) and
of every coherent module supported in a proper closed subset (`hclosed`) is finite-dimensional,
then `χ(X, ℰ ⊗ ℱ) = r·deg(ℰ) + n·χ(X, ℱ)`, where `r = dim_{κ(ξ)} ℱ_ξ` is the rank of `ℱ`. -/
public theorem exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (F : X.Modules) [SheafOfModules.IsCoherent F] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))).IsCoherent,
      @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
          (n : ℤ) * eulerCharacteristic k f F :=
  have _ : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k f
  exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage_rank
    k f E n
    (Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_isIntegral X)
    hclosed hunit F

end AlgebraicGeometry

end
