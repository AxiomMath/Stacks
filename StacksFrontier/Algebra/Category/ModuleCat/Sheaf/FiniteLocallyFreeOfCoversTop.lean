module

public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Finite local freeness from finite free restrictions to a covering family

A sheaf of modules `M` on a ringed site is finite locally free (Stacks 01C6, part (2)) as soon
as there is a family `V_k` covering the final object such that each restriction `M|_{V_k}` is
isomorphic to a finite free module `𝒪_{V_k}^{⊕ I_k}`. The index types `I_k` may differ from
member to member: no rank is fixed. This is the form in which finite local freeness is glued
in the proof of Stacks 0E1J, where the rank of `R¹f_*𝒪_X` is constant only on the open and
closed pieces of the base.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_coversTop`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public section

open CategoryTheory

universe u v u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A sheaf of modules which is finite free on the members of a covering is finite locally
free.** If `V_k` covers the final object and each restriction `M|_{V_k}` is isomorphic to a free
module on a finite type `I_k`, then `M` is finite locally free; the `I_k` need not have the same
cardinality. -/
theorem isFiniteLocallyFree_of_coversTop {ι : Type u₁} {V : ι → C} (hV : J.CoversTop V)
    (M : _root_.SheafOfModules.{u} R)
    (e : ∀ k, ∃ I : Type u, Finite I ∧
      Nonempty (_root_.SheafOfModules.free (R := R.over (V k)) I ≅ M.over (V k))) :
    IsFiniteLocallyFree.{u, v, u₁} M := by
  choose I hI σ using e
  let q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M :=
    { I := ι, X := V, coversTop := hV
      generators := fun k =>
        { I := I k
          s := (M.over (V k)).freeHomEquiv (σ k).some.hom
          epi := by simp only [Equiv.symm_apply_apply]; infer_instance } }
  have hπ : ∀ k, (q.generators k).π = (σ k).some.hom := fun k => Equiv.symm_apply_apply _ _
  refine ⟨q, ⟨fun k => ?_⟩, ⟨fun k => ⟨hI k⟩⟩⟩
  rw [hπ k]
  infer_instance

end AlgebraicGeometry.SheafOfModules

end
