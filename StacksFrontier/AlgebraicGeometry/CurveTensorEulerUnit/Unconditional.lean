module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.IntegralDevissage
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYV] with no hypothesis

**The prefix `AlgebraicGeometry.` is elided from every declaration name below.**

`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6`
(`StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/IntegralDevissage.lean`) proves
[Stacks, Tag 0AYV] — for `ℰ` finite locally free of rank `n` and `ℱ` coherent on a proper curve
`X` over a field `k`,

`χ(X, ℰ ⊗ ℱ) = r·deg(ℰ) + n·χ(X, ℱ)`, `r = dim_{κ(ξ)} ℱ_ξ`,

from two hypotheses `hclosed` and `hunit`, each an instance of [Stacks, Tag 02O6] over a field
at one of the base sheaves of the dévissage. Both are discharged by
`finiteDimensional_cohomologyOverField_of_isProper`, which is [Stacks, Tag 02O6] over a field
with no hypothesis, so [Stacks, Tag 0AYV] holds with no hypothesis at all.

## Main results

* `exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve`:
  **[Stacks, Tag 0AYV], with no hypothesis.**
* `eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`: the same formula with the
  coherence of `ℰ ⊗ ℱ` taken as an argument rather than produced.

## Implementation notes

**`hclosed` is applied at strictly less than it offers.** It is quantified over a coherent `G`
whose support lies in a proper closed subset; the discharge ignores the support condition
entirely, since [Stacks, Tag 02O6] holds for every coherent module on `X`. The hypothesis is
therefore discharged, not merely matched.

**`hunit` needs the coherence of `𝒪_X` as an instance**, which instance search finds once `X` is
known to be locally Noetherian; properness of `f` gives that through
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0AYV], with no hypothesis.** Let `k` be a field, let `X` be a proper curve
over `k` with generic point `ξ`, let `ℰ` be finite locally free of rank `n` and let `ℱ` be
coherent. Then

`χ(X, ℰ ⊗ ℱ) = r·deg(ℰ) + n·χ(X, ℱ)`,

where `r = dim_{κ(ξ)} ℱ_ξ` is the rank of `ℱ` at the generic point. -/
@[stacks 0AYV]
public theorem exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (F : X.Modules) [SheafOfModules.IsCoherent F] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))).IsCoherent,
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
          (n : ℤ) * eulerCharacteristic k f F :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6 k f E n
    (fun G _ _ _ _ hG m =>
      have := hG
      finiteDimensional_cohomologyOverField_of_isProper k f G m)
    (fun m => finiteDimensional_cohomologyOverField_of_isProper k f
      (SheafOfModules.unit X.ringCatSheaf) m)
    F

/-- **[Stacks, Tag 0AYV]**, with the coherence `h` of `ℰ ⊗ ℱ` taken as an argument instead of
produced existentially: for `ℰ` finite locally free of rank `n` and `ℱ` coherent on a proper curve
`X` over a field `k`, `χ(X, ℰ ⊗ ℱ) = r·deg(ℰ) + n·χ(X, ℱ)`, where `r = dim_{κ(ξ)} ℱ_ξ` is the
rank of `ℱ` at the generic point `ξ`. -/
@[stacks 0AYV]
public theorem eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (F : X.Modules) [SheafOfModules.IsCoherent F]
    (h : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))).IsCoherent) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) h =
      (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
          curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
        (n : ℤ) * eulerCharacteristic k f F :=
  (exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve k f E n F).2

end AlgebraicGeometry

end
