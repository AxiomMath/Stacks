module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamPushData
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingIsoCriterion

/-!
# The property of the trace of [Stacks, Tag 0G8K] as perfectness of a pushed pairing

The pairing `(ξ, ξ') ↦ t(ξ ∪ ξ')` of [Stacks, Tag 0G8K] is the push of the multiplication of the
de Rham complex along `AlgebraicGeometry.Scheme.Hom.deRhamPushData`
(`AlgebraicGeometry.Scheme.Hom.deRhamPoincarePairing_eq_pushedPairing`), and a pairing is perfect
for the tensor–internal-Hom adjunction exactly when it is universal
(`TensorHomAdjunction.isIso_homEquiv_symm_iff`). So `t` has the property of [Stacks, Tag 0G8K]
exactly when the two complexes are perfect and the pushed pairing is perfect in the sense of
`CategoryTheory.Functor.PairingPushData.Perf`, which is what the induction over the stupid
truncations produces.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.isDeRhamPoincareTrace_iff`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi (TensorHomAdjunction)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- **The property of the trace of [Stacks, Tag 0G8K] is perfectness of a pushed pairing**:
`t : Rf_*(Ω^•[2n]) ⟶ 𝒪_S` has it exactly when `Rf_*Ω^•` and `Rf_*(Ω^•[2n])` are perfect and the
push of the multiplication of `Ω^•` along `deRhamPushData f (2n)` and `t` is perfect. -/
theorem isDeRhamPoincareTrace_iff
    (t : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).obj
        ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)).obj
          (Scheme.deRhamDerived D.f)) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) :
    D.IsDeRhamPoincareTrace t ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := D.S.toRingedSpace)
        D.f.deRhamDirectImage ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := D.S.toRingedSpace)
        ((derivedPushforward (inverseImageBaseProjection D.f)).obj
          ((Scheme.deRhamDerived D.f)⟦(2 * D.n : ℤ)⟧)) ∧
      letI := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
      (D.f.deRhamPushData (2 * D.n)).Perf t (SheafOfModules.deRhamDerivedMul _ _) := by
  let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
  unfold IsDeRhamPoincareTrace IsPerfectDerivedPairing
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine (TensorHomAdjunction.isIso_homEquiv_symm_iff _ _).trans ?_
  rw [Scheme.Hom.deRhamPoincarePairing_eq_pushedPairing]
  rfl

end AlgebraicGeometry.RelativeDualitySituation
