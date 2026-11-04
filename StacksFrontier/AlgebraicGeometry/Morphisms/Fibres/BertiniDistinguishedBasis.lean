module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Basis
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartCodimension

/-!
# A basis of the linear system beginning with the three distinguished vectors

Under the hypotheses of [Stacks, Tag 0G4F], the linear system `V` has a basis indexed by
`Fin (m + 3)` whose members at `0, 1, 2` are the three distinguished vectors `v₁, v₂, v₃` of
hypothesis (3).

## Main results

* `Module.Basis.exists_sumExtend`: the extension of a linearly independent family to a basis agrees
  with the family on the left summand of the index.
* `Stacks.Bertini.FamilyDivisors.Hypotheses.exists_basis_distinguished`: there are an `m` and a
  basis of `V` indexed by `Fin (m + 3)` whose values at `0, 1, 2` are `v₁, v₂, v₃`.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

universe u v w

/-- A linearly independent family `v : ι → V` extends to a basis of `V` indexed by `ι ⊕ T`, for
some type `T`, whose value at `Sum.inl i` is `v i`. -/
theorem Module.Basis.exists_sumExtend {ι K : Type*} {V : Type w} [DivisionRing K]
    [AddCommGroup V] [Module K V] {v : ι → V} (hv : LinearIndependent K v) :
    ∃ (T : Type w) (W : Module.Basis (ι ⊕ T) K V), ∀ i, W (Sum.inl i) = v i := by
  classical
  refine ⟨↥((hv.linearIndepOn_id.extend (Set.subset_univ _)) \ Set.range v : Set V),
    (Module.Basis.extend hv.linearIndepOn_id).reindex
      (((Equiv.ofInjective v hv.injective).sumCongr (Equiv.refl _)).trans
        (Equiv.Set.sumDiffSubset (Module.Basis.subset_extend hv.linearIndepOn_id))).symm,
    fun i ↦ ?_⟩
  simp [Module.Basis.coe_reindex, Equiv.Set.sumDiffSubset_apply_inl, Set.inclusion]

namespace Stacks.Bertini.FamilyDivisors.Hypotheses

variable {D : FamilyDivisors.{u, v}} (h : D.Hypotheses)

include h

/-- The linear system has a basis indexed by `Fin (m + 3)`, for some `m`, whose members at
`0, 1, 2` are the three distinguished vectors `v₁, v₂, v₃` of hypothesis (3). -/
@[stacks 0G4F "the three distinguished vectors as the first members of a basis"]
theorem exists_basis_distinguished :
    ∃ (m : ℕ) (W : Module.Basis (Fin (m + 3)) D.k D.V),
      W ⟨0, by omega⟩ = h.v₁ ∧ W ⟨1, by omega⟩ = h.v₂ ∧ W ⟨2, by omega⟩ = h.v₃ := by
  classical
  obtain ⟨T, B, hB⟩ := Module.Basis.exists_sumExtend h.linearIndependent_distinguished
  have : Fintype (Fin 3 ⊕ T) := FiniteDimensional.fintypeBasisIndex B
  have : Finite T := Finite.of_injective (Sum.inr : T → Fin 3 ⊕ T) Sum.inr_injective
  have : Fintype T := Fintype.ofFinite T
  set m := Fintype.card T with hm
  set E : Fin 3 ⊕ T ≃ Fin (m + 3) :=
    (Equiv.sumCongr (Equiv.refl (Fin 3)) (Fintype.equivFin T)).trans
      (finSumFinEquiv.trans (finCongr (Nat.add_comm 3 m))) with hE
  have hEinl : ∀ x : Fin 3, E (Sum.inl x) = ⟨x.val, by omega⟩ := fun x ↦ by
    ext
    simp [hE]
  have hW : ∀ x : Fin 3, B.reindex E ⟨x.val, by omega⟩ = ![h.v₁, h.v₂, h.v₃] x := by
    intro x
    rw [show (⟨x.val, by omega⟩ : Fin (m + 3)) = E (Sum.inl x) from (hEinl x).symm,
      Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  exact ⟨m, B.reindex E, hW 0, hW 1, hW 2⟩

end Stacks.Bertini.FamilyDivisors.Hypotheses

end
