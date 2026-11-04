module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.ZeroDimDischarge
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessCoproduct.Basic

/-!
# [Stacks, Tag 0AYV] with [Stacks, Tag 02O6] replaced by a family of twists

`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_curveDegree_of_h02O6_of_hdev`
(`StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/ZeroDimDischarge.lean`) derives the
conclusion of [Stacks, Tag 0AYV] from two hypotheses: finite dimensionality of the cohomology of
every coherent module, which is [Stacks, Tag 02O6] over a field, and the dévissage of
[Stacks, Tag 01YH].

This file removes the first, in favour of the hypotheses the source's own route to
[Stacks, Tag 02O6] supplies: a family `𝒯` of coherent modules whose cohomology is
finite-dimensional in every degree, such that every coherent module is a quotient of a finite
coproduct of members of `𝒯`. On projective space those are the Čech computation of
[Stacks, Tag 01XT] and clause (1) of [Stacks, Tag 01YS] — at the *heterogeneous* shape, the
degrees of the summands allowed to vary, which is what clause (1) says; the single-degree form is
the stronger [Stacks, Tag 01QB].

`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct` concludes
exactly the proposition standing in the `h02O6` binder.

## Main results

* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_curveDegree_of_coproduct_of_hdev`:
  Tag 0AYV's conclusion from the dévissage of [Stacks, Tag 01YH] and the family of twists.

## Implementation notes

The binders `[IsCurve k f] [IsProper f]` are satisfied by `ℙ¹_k`, by
`AlgebraicGeometry.isCurve_projectiveSpaceOver_one` and the instance
`AlgebraicGeometry.projectiveSpaceOver_isProper`. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0AYV] from the dévissage of [Stacks, Tag 01YH] and a family of twists.** For
`ℰ` finite locally free of rank `n` and `ℱ` coherent on a proper curve over a field,
`χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + n · χ(X, ℱ)` with `r` the fibre rank of `ℱ` at the generic point.

This is
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_curveDegree_of_h02O6_of_hdev` with its
`h02O6` hypothesis replaced by the three hypotheses of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct`, which imply
it. -/
theorem exists_eulerCharacteristic_tensorSheaf_curveDegree_of_coproduct_of_hdev
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] {ι : Type v} (T : ι → X.Modules) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (m : ℕ), FiniteDimensional k (cohomologyOverField k f (T a) m))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ)
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
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
        (E)).obj (F))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (E)).obj (F))) h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
          (n : ℤ) * eulerCharacteristic k f F :=
  exists_eulerCharacteristic_tensorSheaf_curveDegree_of_h02O6_of_hdev k f E n
    (forall_finiteDimensional_cohomologyOverField_of_epi_coproduct k f T hTcoh hTfin hgen)
    hdev F

end AlgebraicGeometry

end
