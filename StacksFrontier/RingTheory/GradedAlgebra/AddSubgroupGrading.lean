module

public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# A `SetLike` grading of a module, re-seated in additive subgroups

A `ℤ`-grading of a module is given by a family `𝒨 : ℤ → τ` for an arbitrary `SetLike` type `τ`
with `AddSubgroupClass τ M`. Such a family carries the same data as a family valued in
`AddSubgroup M`, and `Stacks.GradedModule.addSubgroupGrading` moves between them: the degree-`n`
piece is `AddSubgroup.ofClass (𝒨 n)`, whose carrier is the carrier of `𝒨 n`, so membership is
definitionally unchanged and the decomposition is transported field by field.

## Main definitions

* `Stacks.GradedModule.addSubgroupGrading`: the grading, re-seated in `AddSubgroup M`.

## Main results

* `Stacks.GradedModule.mem_addSubgroupGrading`: membership is unchanged.
* `Stacks.GradedModule.addSubgroupGradingDecomposition` and
  `Stacks.GradedModule.addSubgroupGradingGradedSMul`: the decomposition and the compatibility
  with the grading of the ring, transported from the original grading.

## Implementation notes

The decomposition is transported by copying the three fields rather than by a transport lemma:
`↥(AddSubgroup.ofClass (𝒨 n))` and `↥(𝒨 n)` are the same subtype, so the direct sums are the same
type and the fields typecheck unchanged.

The `VAdd ℕ ℤ` on degrees is the shared scoped instance `Stacks.GradedLocalization.instVAddNatInt`.
-/

@[expose] public section

open scoped Stacks.GradedLocalization

namespace Stacks.GradedModule

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ)
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)

/-- A `SetLike` grading of a module, read as a grading by additive subgroups. The degree-`n`
piece has the same carrier, so nothing about the grading changes. -/
def addSubgroupGrading : ℤ → AddSubgroup M := fun n => AddSubgroup.ofClass (𝒨 n)

/-- An element lies in the degree-`n` piece of `addSubgroupGrading 𝒨` if and only if it lies in
`𝒨 n`. -/
@[simp] theorem mem_addSubgroupGrading {n : ℤ} {x : M} :
    x ∈ addSubgroupGrading 𝒨 n ↔ x ∈ 𝒨 n := Iff.rfl

/-- The re-seated grading decomposes the module, the pieces being unchanged. -/
noncomputable instance addSubgroupGradingDecomposition [DirectSum.Decomposition 𝒨] :
    DirectSum.Decomposition (addSubgroupGrading 𝒨) :=
  let e : DirectSum.Decomposition 𝒨 := inferInstance
  { decompose' := e.decompose', left_inv := e.left_inv, right_inv := e.right_inv }

/-- The re-seated grading is compatible with the grading of the ring, the pieces being unchanged
on both sides. -/
instance addSubgroupGradingGradedSMul [SetLike.GradedSMul 𝒮 𝒨] :
    SetLike.GradedSMul 𝒮 (addSubgroupGrading 𝒨) := by
  refine ⟨?_⟩
  intro i j a b ha hb
  exact SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) ha hb

end Stacks.GradedModule

end
