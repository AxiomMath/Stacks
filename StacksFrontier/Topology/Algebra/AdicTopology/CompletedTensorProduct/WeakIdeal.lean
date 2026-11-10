module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# The quotient stages of a completed tensor product

Let `A` and `C` be linearly topologized algebras over a commutative ring `B`, with systems of
ideals `I` and `J` giving fundamental systems of neighbourhoods of zero. The completed tensor
product `A ⊗̂_B C` carries the projections `A ⊗̂_B C → A ⧸ I i ⊗_B C ⧸ J j` of
`TopologicalRing.projectionRingHom`, whose kernels are open
(`TopologicalRing.isOpen_projectionKernel`) and form a fundamental system of neighbourhoods of
zero (`TopologicalRing.hasBasis_projectionKernel`).

This file reads those projections as the *quotient stages* of `A ⊗̂_B C`: each projection is
surjective, so its kernel presents the ordinary tensor product of quotients as a quotient of
the completed tensor product; and when the two ideals are weak ideals of definition, so is the
kernel, and every weak ideal of definition of `A ⊗̂_B C` contains one of them. These are the
stage rings of the formal spectrum `Spf (A ⊗̂_B C)`, and the family of them is cofinal among
all of its stages.

## Main results

* `TopologicalRing.projectionRingHom_coe`: a projection of the completed tensor product sends
  the image of an element of `A ⊗_B C` to its residue class.
* `TopologicalRing.projectionRingHom_surjective`: a projection is surjective.
* `TopologicalRing.quotientProjectionKernelRingEquiv`: the induced ring isomorphism
  `(A ⊗̂_B C) ⧸ ker ≃+* A ⧸ I i ⊗_B C ⧸ J j`.
* `TopologicalRing.projectionKernel_isWeakIdealOfDefinition`: the kernel of a projection cut
  out by two weak ideals of definition is a weak ideal of definition.
* `TopologicalRing.exists_projectionKernel_le_of_isWeakIdealOfDefinition`: the projection
  kernels are cofinal among the weak ideals of definition of `A ⊗̂_B C`.
* `TopologicalRing.weakIdealProjectionKernel`,
  `TopologicalRing.weakIdealProjectionKernel_isWeakIdealOfDefinition`,
  `TopologicalRing.exists_weakIdealProjectionKernel_le` and
  `TopologicalRing.quotientWeakIdealProjectionKernelRingEquiv`: the same four facts in the
  canonical indexing, by a pair of weak ideals of definition of `A` and of `C`, which is the
  index of the quotient stages of a formal spectrum.

## Implementation notes

That a projection kernel consists of topologically nilpotent elements is the computation
performed inline in the proof of `TopologicalRing.completedTensorProduct_isWeaklyAdmissible`
(Stacks 0GB4): by `TopologicalRing.projectionKernel_eq_closure` the kernel is the closure of
the sum of the two extended ideals, and `TopologicalRing.closure_map_le_topologicalNilradical`
applies to each summand. It is isolated here for one weak ideal of definition at a time,
rather than only for the single pair that witnesses weak admissibility.

Cofinality is immediate from `TopologicalRing.hasBasis_projectionKernel`: an open ideal is a
neighbourhood of zero, so it contains a basis member.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AMW](https://stacks.math.columbia.edu/tag/0AMW)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
-/

@[expose] public section

namespace TopologicalRing

section

open Filter
open scoped TensorProduct Topology

/-- A weak ideal of definition consists of topologically nilpotent elements. -/
private theorem le_topologicalNilradical_of_isWeakIdealOfDefinition {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsLinearTopology R R]
    {I : Ideal R} (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    I ≤ topologicalNilradical R := fun _ hz =>
  IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hI.2 _ hz)

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
  [Algebra B A] [Algebra B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

variable {ι κ : Type*} (I : ι → Ideal A) (J : κ → Ideal C)
  (bI : (nhds (0 : A)).HasBasis (fun _ : ι => True) (fun i => (I i : Set A)))
  (bJ : (nhds (0 : C)).HasBasis (fun _ : κ => True) (fun j => (J j : Set C)))

include bI bJ

/-- A canonical projection of the completed tensor product sends the image of an element of
the ordinary tensor product to its residue class. -/
public theorem projectionRingHom_coe (i : ι) (j : κ) (z : A ⊗[B] C) :
    projectionRingHom (B := B) I J bI bJ i j
        (↑z : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I i))
        (Ideal.Quotient.mkₐ B (J j)) z :=
  (Classical.choose_spec
    (exists_completedTensorProductRingEquivQuotientLimit (B := B) I J bI bJ)).2.2 z i j

/-- A canonical projection of the completed tensor product is surjective: it already is on the
image of the ordinary tensor product, where it is the tensor product of the two quotient
maps. -/
public theorem projectionRingHom_surjective (i : ι) (j : κ) :
    Function.Surjective (projectionRingHom (B := B) I J bI bJ i j) := by
  intro y
  obtain ⟨z, hz⟩ := Algebra.TensorProduct.map_surjective (R := B) (S := B)
    (f := Ideal.Quotient.mkₐ B (I i)) (g := Ideal.Quotient.mkₐ B (J j))
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective y
  exact ⟨(↑z : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)),
    (projectionRingHom_coe (B := B) I J bI bJ i j z).trans hz⟩

/-- The quotient of the completed tensor product by a projection kernel is the corresponding
tensor product of quotients. -/
public noncomputable def quotientProjectionKernelRingEquiv (i : ι) (j : κ) :
    (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ⧸
        projectionKernel (B := B) I J bI bJ i j) ≃+* (A ⧸ I i) ⊗[B] (C ⧸ J j) :=
  RingHom.quotientKerEquivOfSurjective (projectionRingHom_surjective (B := B) I J bI bJ i j)

/-- A projection kernel consists of topologically nilpotent elements as soon as the two ideals
cutting it out do. -/
public theorem projectionKernel_le_topologicalNilradical (i : ι) (j : κ)
    (hI : I i ≤ topologicalNilradical A) (hJ : J j ≤ topologicalNilradical C) :
    projectionKernel (B := B) I J bI bJ i j ≤
      topologicalNilradical
        (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) := by
  let := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  let := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  set T := TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)
  let φA : A →+* T := RingHom.comp UniformSpace.Completion.coeRingHom
    ((Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] C).toRingHom)
  let φC : C →+* T := RingHom.comp UniformSpace.Completion.coeRingHom
    ((Algebra.TensorProduct.includeRight : C →ₐ[B] A ⊗[B] C).toRingHom)
  have hφA : Continuous φA := by
    change Continuous (fun a : A => ((a ⊗ₜ[B] (1 : C) : A ⊗[B] C) : T))
    exact (UniformSpace.Completion.continuous_coe (A ⊗[B] C)).comp
      (TopologicalRing.continuous_tmul_const (R := B) (M := A) (N := C) (1 : C))
  have hφC : Continuous φC := by
    change Continuous (fun c : C => (((1 : A) ⊗ₜ[B] c : A ⊗[B] C) : T))
    exact (UniformSpace.Completion.continuous_coe (A ⊗[B] C)).comp
      (TopologicalRing.continuous_const_tmul (R := B) (M := A) (N := C) (1 : A))
  intro x hx
  change x ∈ (SetLike.coe (projectionKernel (B := B) I J bI bJ i j) : Set T) at hx
  rw [TopologicalRing.projectionKernel_eq_closure (B := B) I J bI bJ i j] at hx
  change x ∈ closure ((I i).map φA + (J j).map φC : Ideal T) at hx
  exact closure_minimal (show ((I i).map φA + (J j).map φC : Ideal T) ≤
      topologicalNilradical T from sup_le
    (fun z hz => TopologicalRing.closure_map_le_topologicalNilradical φA hφA (I i) hI
      (subset_closure hz))
    (fun z hz => TopologicalRing.closure_map_le_topologicalNilradical φC hφC (J j) hJ
      (subset_closure hz)))
    (TopologicalRing.isClosed_topologicalNilradical (B := T)) hx

/-- **The projection kernel cut out by two weak ideals of definition is a weak ideal of
definition of the completed tensor product.** It is open by
`TopologicalRing.isOpen_projectionKernel`, and it consists of topologically nilpotent elements
because it is the closure of the sum of the two extended ideals. -/
@[stacks 0GB4 "the projection kernels as weak ideals of definition"]
public theorem projectionKernel_isWeakIdealOfDefinition (i : ι) (j : κ)
    (hI : TopologicalRing.IsWeakIdealOfDefinition (I i))
    (hJ : TopologicalRing.IsWeakIdealOfDefinition (J j)) :
    TopologicalRing.IsWeakIdealOfDefinition
      (projectionKernel (B := B) I J bI bJ i j) :=
  ⟨TopologicalRing.isOpen_projectionKernel (B := B) I J bI bJ i j, fun _ hx =>
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp
      (projectionKernel_le_topologicalNilradical (B := B) I J bI bJ i j
        (le_topologicalNilradical_of_isWeakIdealOfDefinition hI)
        (le_topologicalNilradical_of_isWeakIdealOfDefinition hJ)
        hx)⟩

/-- An open ideal of the completed tensor product contains a projection kernel: the projection
kernels are a fundamental system of neighbourhoods of zero. -/
public theorem exists_projectionKernel_le_of_isOpen
    {K : Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))}
    (hK : IsOpen (K : Set
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))) :
    ∃ p : ι × κ, projectionKernel (B := B) I J bI bJ p.1 p.2 ≤ K := by
  obtain ⟨p, -, hp⟩ :=
    (hasBasis_projectionKernel (B := B) I J bI bJ).mem_iff.mp (hK.mem_nhds K.zero_mem)
  exact ⟨p, hp⟩

/-- **The projection kernels are cofinal among the weak ideals of definition of the completed
tensor product**: every weak ideal of definition contains one of them, and those cut out by
weak ideals of definition are themselves weak ideals of definition by
`TopologicalRing.projectionKernel_isWeakIdealOfDefinition`. -/
public theorem exists_projectionKernel_le_of_isWeakIdealOfDefinition
    {K : Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))}
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) :
    ∃ p : ι × κ, projectionKernel (B := B) I J bI bJ p.1 p.2 ≤ K :=
  exists_projectionKernel_le_of_isOpen (B := B) I J bI bJ hK.1

end

section Canonical

open Filter
open scoped TensorProduct Topology

variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
  [Algebra B A] [Algebra B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- The weak ideals of definition of a weakly admissible linearly topologized ring form a
fundamental system of neighbourhoods of zero, in the indexed shape the projections of a
completed tensor product are stated for. The index is the subtype of weak ideals of definition
that indexes the quotient stages of a formal spectrum. -/
public theorem hasBasis_isWeakIdealOfDefinition_subtype
    (hA : TopologicalRing.IsWeaklyAdmissible A) :
    (nhds (0 : A)).HasBasis
      (fun _ : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } => True)
      (fun i => ((i.1 : Ideal A) : Set A)) :=
  (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).to_hasBasis
    (fun I hI => ⟨⟨I, hI⟩, trivial, subset_rfl⟩) (fun i _ => ⟨i.1, i.2, subset_rfl⟩)

variable (hA : TopologicalRing.IsWeaklyAdmissible A)
  (hC : TopologicalRing.IsWeaklyAdmissible C)

/-- The quotient stage of `A ⊗̂_B C` cut out by a pair of weak ideals of definition of `A` and
of `C`: the kernel of the projection to `A ⧸ I ⊗_B C ⧸ J`. These are weak ideals of definition
of `A ⊗̂_B C` and they are cofinal among all of them, so they index a cofinal subfamily of the
quotient stages of `Spf (A ⊗̂_B C)`. -/
public noncomputable abbrev weakIdealProjectionKernel
    (i : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (j : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J }) :
    Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) :=
  projectionKernel (B := B) (fun i => i.1) (fun j => j.1)
    (hasBasis_isWeakIdealOfDefinition_subtype hA)
    (hasBasis_isWeakIdealOfDefinition_subtype hC) i j

/-- Each canonical quotient stage of `A ⊗̂_B C` is a weak ideal of definition. -/
public theorem weakIdealProjectionKernel_isWeakIdealOfDefinition
    (i : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (j : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J }) :
    TopologicalRing.IsWeakIdealOfDefinition
      (weakIdealProjectionKernel (B := B) hA hC i j) :=
  projectionKernel_isWeakIdealOfDefinition (B := B) _ _ _ _ i j i.2 j.2

/-- **The canonical quotient stages are cofinal among the weak ideals of definition of
`A ⊗̂_B C`.** Together with
`TopologicalRing.weakIdealProjectionKernel_isWeakIdealOfDefinition` this says that the
stages of `Spf (A ⊗̂_B C)` indexed by pairs of weak ideals of definition of `A` and of `C` are
a cofinal subfamily of all of its stages. -/
public theorem exists_weakIdealProjectionKernel_le
    {K : Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))}
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) :
    ∃ (i : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (j : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J }),
      weakIdealProjectionKernel (B := B) hA hC i j ≤ K := by
  obtain ⟨p, hp⟩ :=
    exists_projectionKernel_le_of_isWeakIdealOfDefinition (B := B) _ _
      (hasBasis_isWeakIdealOfDefinition_subtype hA)
      (hasBasis_isWeakIdealOfDefinition_subtype hC) hK
  exact ⟨p.1, p.2, hp⟩

/-- **The stage ring of `Spf (A ⊗̂_B C)` at a pair of weak ideals of definition is the ordinary
tensor product of the two quotients.** This is the ring computation underlying clause (3) of
Stacks 0AN3: the quotient stages of the fibre product of two McQuillan affine formal algebraic
spaces are the spectra of the rings `A ⧸ I ⊗_B C ⧸ J`. -/
public noncomputable def quotientWeakIdealProjectionKernelRingEquiv
    (i : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (j : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J }) :
    (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ⧸
        weakIdealProjectionKernel (B := B) hA hC i j) ≃+*
      (A ⧸ (i.1 : Ideal A)) ⊗[B] (C ⧸ (j.1 : Ideal C)) :=
  quotientProjectionKernelRingEquiv (B := B) _ _
    (hasBasis_isWeakIdealOfDefinition_subtype hA)
    (hasBasis_isWeakIdealOfDefinition_subtype hC) i j

end Canonical

end TopologicalRing

end
