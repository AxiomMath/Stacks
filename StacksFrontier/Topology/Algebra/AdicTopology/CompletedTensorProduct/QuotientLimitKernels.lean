module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.WeakIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kernels of the projections of a completed tensor product

For linearly topologized rings `A` and `C` over `B` with fundamental systems of ideals `I` and
`J`, the completed tensor product maps onto each quotient `A ⧸ I i ⊗[B] C ⧸ J j`. This module
studies these projections and their kernels.

## Main definitions

* `TopologicalRing.projectionKernelQuotientRingEquiv`: The quotient of the completed tensor
  product by a projection kernel is the corresponding quotient tensor product.

## Main results

* `TopologicalRing.projectionRingHom_surjective_of_continuousAdd`: Each projection is
  surjective.
* `TopologicalRing.projectionKernel_mono`: Projection kernels are monotone in the two ideals.
* `TopologicalRing.isWeakIdealOfDefinition_projectionKernel`: A projection kernel is a weak
  ideal of definition when both ideals are.
* `TopologicalRing.exists_projectionKernel_le`: The projection kernels are cofinal among the
  open ideals.
-/

@[expose] public section

namespace TopologicalRing

section

open Filter Set

open scoped TensorProduct Topology

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
  [Algebra B A] [Algebra B C]
  [TopologicalSpace A] [TopologicalSpace C]
  [ContinuousAdd A] [ContinuousAdd C]
  [IsLinearTopology A A] [IsLinearTopology C C]

variable {ι κ : Type*} (I : ι → Ideal A) (J : κ → Ideal C)
  (bI : (nhds (0 : A)).HasBasis (fun _ : ι => True) (fun i => (I i : Set A)))
  (bJ : (nhds (0 : C)).HasBasis (fun _ : κ => True) (fun j => (J j : Set C)))

/-- On the image of the algebraic tensor product a canonical projection is the evident
quotient map of tensor products, for topologies on `A` and `C` that are only assumed to have
continuous addition (not to be topological rings), unlike
`TopologicalRing.projectionRingHom_coe`. -/
public theorem projectionRingHom_coe_of_continuousAdd (i : ι) (j : κ) (z : A ⊗[B] C) :
    letI := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
    projectionRingHom (B := B) I J bI bJ i j
        (↑z : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I i))
        (Ideal.Quotient.mkₐ B (J j)) z :=
  (Classical.choose_spec (exists_completedTensorProductRingEquivQuotientLimit
    (B := B) (A := A) (C := C) I J bI bJ)).2.2 z i j

/-- **A canonical projection is surjective**, for topologies on `A` and `C` that are only
assumed to have continuous addition, unlike `TopologicalRing.projectionRingHom_surjective`. The
quotient map of the algebraic tensor product already is, and the algebraic tensor product maps
into the completion. -/
public theorem projectionRingHom_surjective_of_continuousAdd (i : ι) (j : κ) :
    Function.Surjective (projectionRingHom (B := B) (A := A) (C := C) I J bI bJ i j) := by
  let := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  intro d
  obtain ⟨z, rfl⟩ := Algebra.TensorProduct.map_surjective
    (f := Ideal.Quotient.mkₐ B (I i)) (g := Ideal.Quotient.mkₐ B (J j))
    (Ideal.Quotient.mkₐ_surjective B (I i)) (Ideal.Quotient.mkₐ_surjective B (J j)) d
  exact ⟨(z : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)),
    projectionRingHom_coe_of_continuousAdd I J bI bJ i j z⟩

/-- **The quotient of the completed tensor product by a projection kernel is the
corresponding quotient tensor product**: the projection is surjective with that kernel. -/
public noncomputable def projectionKernelQuotientRingEquiv (i : ι) (j : κ) :
    (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ⧸
        projectionKernel (B := B) I J bI bJ i j) ≃+* (A ⧸ I i) ⊗[B] (C ⧸ J j) :=
  RingHom.quotientKerEquivOfSurjective
    (projectionRingHom_surjective_of_continuousAdd (B := B) (A := A) (C := C) I J bI bJ i j)

/-- **Projection kernels grow with the two ideals cutting them out**: the projection to the
larger pair of quotients factors through the projection to the smaller pair. -/
public theorem projectionKernel_mono {i i' : ι} {j j' : κ}
    (hi : I i ≤ I i') (hj : J j ≤ J j') :
    projectionKernel (B := B) I J bI bJ i j ≤ projectionKernel (B := B) I J bI bJ i' j' := by
  classical
  intro x hx
  let e : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      quotientLimit (B := B) I J :=
    completedTensorProductRingEquivQuotientLimit I J bI bJ
  have hcompat := (e x).2 (i, j) (i', j') hi hj
  change (e x).1 (i, j) = 0 at hx
  change (e x).1 (i', j') = 0
  rw [← hcompat, hx, map_zero]

end

section WeakIdeals

open Filter Set

open scoped TensorProduct Topology

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
  [Algebra B A] [Algebra B C]
  [TopologicalSpace A] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing C]
  [IsLinearTopology A A] [IsLinearTopology C C]
  {ι κ : Type*} (I : ι → Ideal A) (J : κ → Ideal C)
  (bI : (nhds (0 : A)).HasBasis (fun _ : ι => True) (fun i => (I i : Set A)))
  (bJ : (nhds (0 : C)).HasBasis (fun _ : κ => True) (fun j => (J j : Set C)))

/-- **A projection kernel is a weak ideal of definition** as soon as the two ideals cutting it
out are: it is open, and its elements are topologically nilpotent. -/
public theorem isWeakIdealOfDefinition_projectionKernel (i : ι) (j : κ)
    (hI : IsWeakIdealOfDefinition (I i)) (hJ : IsWeakIdealOfDefinition (J j)) :
    IsWeakIdealOfDefinition (projectionKernel (B := B) I J bI bJ i j) :=
  ⟨isOpen_projectionKernel (B := B) I J bI bJ i j, fun _ hx =>
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp
      (projectionKernel_le_topologicalNilradical I J bI bJ i j
        (fun _ hy => IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hI.2 _ hy))
        (fun _ hy => IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hJ.2 _ hy))
        hx)⟩

/-- **The projection kernels are cofinal among the open ideals** of the completed tensor
product, since they form a neighbourhood basis of zero.  Together with
`TopologicalRing.isWeakIdealOfDefinition_projectionKernel` this makes them cofinal among the
weak ideals of definition, which are open by definition. -/
@[ega "0 7.7.5" "partial"]
public theorem exists_projectionKernel_le
    {L : Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))}
    (hL : IsOpen (L : Set
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))) :
    ∃ (i : ι) (j : κ), projectionKernel (B := B) I J bI bJ i j ≤ L := by
  obtain ⟨p, -, hp⟩ := (hasBasis_projectionKernel (B := B) I J bI bJ).mem_iff.mp
    (hL.mem_nhds L.zero_mem)
  exact ⟨p.1, p.2, hp⟩

end WeakIdeals

end TopologicalRing

end
