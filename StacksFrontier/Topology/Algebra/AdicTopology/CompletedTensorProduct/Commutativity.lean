module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.Algebra.UniformRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct

/-!
# The completed tensor product is symmetric

The tensor product topology of Tag 0AMU is symmetric in its two factors: the flip
`M ⊗[R] N ≃ N ⊗[R] M` carries the basic open submodule `P ⊗ N + M ⊗ Q` to `Q ⊗ M + N ⊗ P`, so it
is a homeomorphism, and therefore extends to a ring isomorphism of completed tensor products of
linearly topologized algebras.

## Main definitions

* `TopologicalRing.completedTensorProductComm` is the canonical ring isomorphism
  `A ⊗̂[B] C ≃+* C ⊗̂[B] A`.

## Main results

* `TopologicalRing.tensorProductSubmodule_map_comm`: the flip carries a basic open submodule of
  the tensor product topology to the corresponding one on the other side.
* `TopologicalRing.continuous_tensorProduct_comm`: the flip is continuous for the tensor
  product topologies.

## Implementation notes

Both tensor product topologies have to be supplied by hand at every statement, since
`TopologicalRing.tensorProductTopology` is not a global instance; the type ascriptions use
`@Continuous` with both topologies written out, as elsewhere in this directory.

The ring isomorphism of completions is `UniformSpace.Completion.mapRingEquiv` applied to
`Algebra.TensorProduct.comm`, whose continuity in both directions is the symmetric statement
`continuous_tensorProduct_comm` read in the two possible orders.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

namespace TopologicalRing

section

open scoped TensorProduct

/-- The flip of a tensor product carries the range of `f ⊗ g` to the range of `g ⊗ f`. -/
private theorem map_range_map_comm
    {R M N M' N' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (f : M' →ₗ[R] M) (g : N' →ₗ[R] N) :
    (LinearMap.range (TensorProduct.map f g)).map (TensorProduct.comm R M N).toLinearMap =
      LinearMap.range (TensorProduct.map g f) := by
  rw [← LinearMap.range_comp, ← TensorProduct.map_comp_comm_eq g f, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

/-- The flip of a tensor product carries the basic open submodule of the tensor product topology
attached to a pair of coordinate submodules to the one attached to the swapped pair. -/
public theorem tensorProductSubmodule_map_comm
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : Submodule R M) (Q : Submodule R N) :
    (tensorProductSubmodule P Q).map (TensorProduct.comm R M N).toLinearMap =
      tensorProductSubmodule Q P := by
  unfold tensorProductSubmodule
  rw [Submodule.map_sup, map_range_map_comm, map_range_map_comm, sup_comm]

/-- The flip of a tensor product is continuous for the tensor product topologies. -/
public theorem continuous_tensorProduct_comm
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N] :
    @Continuous (M ⊗[R] N) (N ⊗[R] M)
      (tensorProductTopology (R := R) (M := M) (N := N))
      (tensorProductTopology (R := R) (M := N) (N := M))
      (TensorProduct.comm R M N) := by
  let := tensorProductTopology (R := R) (M := M) (N := N)
  let := tensorProductTopology (R := R) (M := N) (N := M)
  apply continuous_of_continuousAt_zero (TensorProduct.comm R M N).toLinearMap
  change Filter.Tendsto (TensorProduct.comm R M N).toLinearMap (nhds 0) (nhds 0)
  refine ((hasBasis_tensorProductTopology (R := R) (M := M) (N := N)).tendsto_iff
    (hasBasis_tensorProductTopology (R := R) (M := N) (N := M))).mpr ?_
  intro i _
  refine ⟨(i.2, i.1), trivial, fun x hx ↦ ?_⟩
  change (TensorProduct.comm R M N) x ∈ tensorProductSubmodule i.1.1 i.2.1
  rw [← tensorProductSubmodule_map_comm i.2.1 i.1.1]
  exact Submodule.mem_map_of_mem (show x ∈ tensorProductSubmodule i.2.1 i.1.1 from hx)

/-- The flip of a tensor product of algebras is continuous for the tensor product topologies. -/
public theorem continuous_algebraTensorProduct_comm
    {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C] [TopologicalSpace A] [TopologicalSpace C] :
    @Continuous (A ⊗[B] C) (C ⊗[B] A)
      (tensorProductTopology (R := B) (M := A) (N := C))
      (tensorProductTopology (R := B) (M := C) (N := A))
      (Algebra.TensorProduct.comm B A C).toRingEquiv :=
  continuous_tensorProduct_comm

/-- The canonical ring isomorphism `A ⊗̂[B] C ≃+* C ⊗̂[B] A` between completed tensor products of
linearly topologized `B`-algebras, obtained by completing the flip of the tensor product. -/
@[ega "0 7.7.4" "special case"]
public noncomputable def completedTensorProductComm
    {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] :
    CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      CompletedTensorProduct (R := B) (M := C) (N := A) :=
  letI : TopologicalSpace (A ⊗[B] C) := tensorProductTopology (R := B) (M := A) (N := C)
  letI : TopologicalSpace (C ⊗[B] A) := tensorProductTopology (R := B) (M := C) (N := A)
  letI : UniformSpace (A ⊗[B] C) := tensorProductUniformSpace (R := B) (M := A) (N := C)
  letI : UniformSpace (C ⊗[B] A) := tensorProductUniformSpace (R := B) (M := C) (N := A)
  letI : IsTopologicalRing (A ⊗[B] C) := tensorProduct_isTopologicalRing (R := B) (A := A) (B := C)
  letI : IsTopologicalRing (C ⊗[B] A) := tensorProduct_isTopologicalRing (R := B) (A := C) (B := A)
  UniformSpace.Completion.mapRingEquiv (Algebra.TensorProduct.comm B A C).toRingEquiv
    (show Continuous (TensorProduct.comm B A C) from continuous_algebraTensorProduct_comm)
    (show Continuous (TensorProduct.comm B C A) from continuous_algebraTensorProduct_comm)

end

end TopologicalRing

end
