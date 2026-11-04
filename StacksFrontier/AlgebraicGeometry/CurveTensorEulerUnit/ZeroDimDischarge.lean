module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Devissage
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank

/-!
# [Stacks, Tag 0AYV] with its zero-dimensional input discharged

`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`
(`StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/Devissage.lean`) derives the conclusion of
[Stacks, Tag 0AYV] from three hypotheses: the finite dimensionality of [Stacks, Tag 02O6], the
dévissage of [Stacks, Tag 01YH], and clause (5) of [Stacks, Tag 0AYT] for a module with
zero-dimensional support. The third is a theorem,
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank`,
so this file restates Tag 0AYV's conclusion with that hypothesis removed.

## Main results

* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_curveDegree_of_h02O6_of_hdev`:
  [Stacks, Tag 0AYV] from Tag 02O6 and the Tag 01YH dévissage alone.

## Implementation notes

The hypothesis `h0AYT` of the predecessor in `CurveTensorEulerUnit/Devissage.lean` takes
coherence of its module as an explicit argument and mentions that proof term in its conclusion,
while `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank`
takes it as an instance binder. The discharge therefore applies that theorem with `@`, putting
the given proof into the instance slot, so that the two Euler characteristics are the same term.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **[Stacks, Tag 0AYV] from Tag 02O6 and the Tag 01YH dévissage alone.** For `ℰ` finite
locally free of rank `n` and `ℱ` coherent on a proper curve over a field,
`χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + n · χ(X, ℱ)` with `r` the fibre rank of `ℱ` at the generic point.

This is
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add` with
its hypothesis `h0AYT` discharged by
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank`. -/
theorem exists_eulerCharacteristic_tensorSheaf_curveDegree_of_h02O6_of_hdev
    [IsCurve k f] [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (F : X.Modules) [SheafOfModules.IsCoherent F] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
          (n : ℤ) * eulerCharacteristic k f F :=
  exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add k f E n h02O6 hdev
    (fun G hG hdim =>
      @exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank X k _ f _
        E G n ‹_› hG hdim)
    F

end AlgebraicGeometry

end
