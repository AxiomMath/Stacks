module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Units
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Associated primes of a tensor product with an adically complete module

Let `R → S` be a ring map, let `I` be an ideal of `R` and let `N` be an `S`-module which is
`I`-adically complete as an `R`-module. Then every associated prime of `N ⊗[R] M`, for an
arbitrary `R`-module `M`, meets the closed subset of `Spec S` cut out by the extension of `I`.

The proof passes to the `IS`-adic completion of `S`, in which the extension of `I` lies in the
Jacobson radical; an associated prime that were comaximal with `IS` would extend to the unit
ideal there, forcing its witness to vanish.

## Main results

* `Stacks.PureModules.associatedPrime_add_map_ne_top_of_isAdicComplete`: an associated prime of
  `N ⊗[R] M` is not comaximal with the extended ideal.

## Implementation notes

The extended ideal `IS` is `I.map (algebraMap R S)`. Associatedness is
`IsAssociatedPrimeStacks`, which asks the prime to be the exact annihilator of an element.
The tensor product is written `N ⊗[R] M` so that it carries its standard `S`-module structure.

## References

* [Stacks Project, Tag 05IT](https://stacks.math.columbia.edu/tag/05IT)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Stacks.PureModules

/-- **Stacks Project, Tag 05IT.** An associated prime of the tensor product of an adically
complete module with any base module is not comaximal with the ideal of completion. -/
@[stacks 05IT]
theorem associatedPrime_add_map_ne_top_of_isAdicComplete
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [IsAdicComplete I N]
    (M : Type x) [AddCommGroup M] [Module R M]
    (q : Ideal S) (hq : IsAssociatedPrimeStacks S (N ⊗[R] M) q) :
    q + I.map (algebraMap R S) ≠ ⊤ := by
  let J : Ideal S := I.map (algebraMap R S)
  let A := AdicCompletion J S
  let P := AdicCompletion J N
  have hcomplete : IsAdicComplete J N :=
    (IsAdicComplete.map_algebraMap_iff I N).2 inferInstance
  let eN : N ≃ₗ[S] P := AdicCompletion.ofLinearEquiv J N
  let eT : N ⊗[R] M ≃ₗ[S] P ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.congr eN (LinearEquiv.refl R M)
  obtain ⟨z, hz⟩ := hq.2
  have hz_ne : z ≠ 0 := fun hzero => hq.1.ne_top (by rw [← hz]; simp [hzero])
  let z' : P ⊗[R] M := eT z
  have hz'_ne : z' ≠ 0 := fun hzero => hz_ne (eT.injective hzero)
  let _ : IsScalarTower R A P :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := A) (M := P) fun r x => by
      show algebraMap S A (algebraMap R S r) • x = r • x
      rw [IsScalarTower.algebraMap_smul A, IsScalarTower.algebraMap_smul S]
  let _ : Module A (P ⊗[R] M) := TensorProduct.leftModule
  let _ : IsScalarTower S A (P ⊗[R] M) := inferInstance
  let qA : Ideal A := q.map (algebraMap S A)
  have hqA_le : qA ≤ (⊥ : Submodule A (P ⊗[R] M)).colon (Submodule.span A {z'}) := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [Ideal.mem_comap, Submodule.mem_colon_span_singleton]
    have hkill : a • z = 0 := by
      have ha' : a ∈ (⊥ : Submodule S (N ⊗[R] M)).colon (Submodule.span S {z}) := hz.symm ▸ ha
      simpa [Submodule.mem_colon_span_singleton] using ha'
    show (algebraMap S A a) • z' ∈ (⊥ : Submodule A (P ⊗[R] M))
    rw [IsScalarTower.algebraMap_smul, ← eT.map_smul, hkill, map_zero]
    simp
  have hqA_ne : qA ≠ ⊤ := fun htop => hz'_ne <| by
    simpa [Submodule.mem_colon_span_singleton] using
      hqA_le (show (1 : A) ∈ qA by rw [htop]; simp)
  obtain ⟨m, hmmax, hqAm⟩ := Ideal.exists_le_maximal qA hqA_ne
  have hJm : J.map (algebraMap S A) ≤ m :=
    (AdicCompletion.isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot
        J).2.2.2.1.trans
      (by rw [Ideal.jacobson_bot]; exact Ring.jacobson_le_of_isMaximal m)
  intro htop
  have hone' : (1 : A) ∈ qA + J.map (algebraMap S A) := by
    rw [Ideal.add_eq_sup, show qA = q.map (algebraMap S A) from rfl, ← Ideal.map_sup,
      ← Ideal.add_eq_sup, htop]
    exact Ideal.mem_map_of_mem _ (by simp)
  exact hmmax.ne_top (m.eq_top_iff_one.2 (sup_le hqAm hJm hone'))

end Stacks.PureModules
