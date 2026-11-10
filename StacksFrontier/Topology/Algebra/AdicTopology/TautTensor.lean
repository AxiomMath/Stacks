module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct
public import StacksFrontier.Topology.Algebra.AdicTopology.Completion
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Tautness under completed tensor-product base change

A continuous taut homomorphism of linearly topologized rings stays taut after base change
along a continuous homomorphism, computed with the completed tensor product.

## References

* [Stacks Project, Tag 0GX5](https://stacks.math.columbia.edu/tag/0GX5)
-/

@[expose] public section

namespace RingHom

section

open Filter
open scoped TensorProduct

/-- An additive map out of a tensor product lands in an additive subgroup on the image of `g ⊗ h`
as soon as it does on pure tensors. -/
private theorem map_tensorProduct_mem {R M N P Q S : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup S]
    (f : P ⊗[R] Q →+ S) (L : AddSubgroup S) (g : M →ₗ[R] P) (h : N →ₗ[R] Q)
    (H : ∀ m n, f (g m ⊗ₜ[R] h n) ∈ L) (z : M ⊗[R] N) : f (TensorProduct.map g h z) ∈ L := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => simpa using H m n
  | add z z' hz hz' => simpa only [map_add] using L.add_mem hz hz'

private lemma completedTensorProduct_coe_tensorProductSubmodule_le
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (hIK : Ideal.map (algebraMap A C) I ≤ K)
    (hJ : J ≤ Ideal.closure (I.map (algebraMap A B))) :
    letI : TopologicalSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) :=
      TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
    letI : Algebra C (B ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
    ∀ x ∈ TopologicalRing.tensorProductSubmodule
        (J.restrictScalars A) (K.restrictScalars A),
      (UniformSpace.Completion.coeRingHom : (B ⊗[A] C) →+*
        TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) x ∈
        Ideal.closure (K.map (algebraMap C
          (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)))) := by
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  let : Algebra C (B ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
  let D := TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)
  let f : (B ⊗[A] C) →+* D := UniformSpace.Completion.coeRingHom
  let fB : B →+* D := f.comp Algebra.TensorProduct.includeLeftRingHom
  let fC : C →+* D := f.comp Algebra.TensorProduct.includeRight.toRingHom
  let φ : C →+* D := algebraMap C D
  let L : Ideal D := Ideal.closure (K.map φ)
  have hφ : φ = fC := by
    ext c
    rfl
  have hKL : K.map φ ≤ L := fun _ h => subset_closure h
  have hcomp : fB.comp (algebraMap A B) = φ.comp (algebraMap A C) := by
    rw [hφ]
    exact congrArg f.comp Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  have hmap : Ideal.map fB (I.map (algebraMap A B)) ≤ L := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
    exact (Ideal.map_mono hIK).trans hKL
  have hfB : Continuous fB := by
    dsimp [fB, f]
    change Continuous (fun b : B => (↑(b ⊗ₜ[A] (1 : C)) : D))
    exact (UniformSpace.Completion.continuous_coe (B ⊗[A] C)).comp
      (TopologicalRing.continuous_tmul_const (R := A) (M := B) (N := C) (1 : C))
  have hJmap : ∀ b ∈ J, fB b ∈ L := by
    intro b hb
    have hb' : b ∈ closure (I.map (algebraMap A B) : Set B) := by
      change b ∈ (Ideal.closure (I.map (algebraMap A B)) : Set B)
      rw [Ideal.coe_closure]
      exact hJ hb
    exact isClosed_closure.closure_subset
      (map_mem_closure hfB hb' fun x hx => hmap (Ideal.mem_map_of_mem fB hx))
  have hmul (b : B) (c : C) : f (b ⊗ₜ[A] c) = fB b * fC c := by
    change f _ = f (b ⊗ₜ[A] (1 : C)) * f ((1 : B) ⊗ₜ[A] c)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  intro x hx
  change x ∈ LinearMap.range (TensorProduct.map (J.restrictScalars A).subtype LinearMap.id) ⊔
    LinearMap.range (TensorProduct.map LinearMap.id (K.restrictScalars A).subtype) at hx
  obtain ⟨_, ⟨z₁, rfl⟩, _, ⟨z₂, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine L.add_mem (map_tensorProduct_mem f.toAddMonoidHom L.toAddSubgroup _ _ (fun b c => ?_) z₁)
    (map_tensorProduct_mem f.toAddMonoidHom L.toAddSubgroup _ _ (fun b c => ?_) z₂)
  · change f ((b : B) ⊗ₜ[A] c) ∈ L
    rw [hmul]
    exact L.mul_mem_right _ (hJmap b b.2)
  · change f (b ⊗ₜ[A] (c : C)) ∈ L
    rw [hmul, ← hφ]
    exact L.mul_mem_left _ (hKL (Ideal.mem_map_of_mem φ c.2))

/-- Completed tensor-product base change preserves a taut homomorphism. -/
@[stacks 0GX5]
public lemma isTaut_completedTensorProduct_baseChange
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (_hB : Continuous (algebraMap A B)) (hC : Continuous (algebraMap A C))
    (hTaut : RingHom.IsTaut (algebraMap A B)) :
    letI : Algebra C (B ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
    RingHom.IsTaut
      (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) := by
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  let : Algebra C (B ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
  let D := TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)
  let φ : C →+* D := algebraMap C D
  have hφ : Continuous φ := by
    change Continuous (fun c : C => (↑((1 : B) ⊗ₜ[A] c) : D))
    exact (UniformSpace.Completion.continuous_coe (B ⊗[A] C)).comp
      (TopologicalRing.continuous_const_tmul (R := A) (M := B) (N := C) (1 : B))
  have hOpen : ∀ K : Ideal C, IsOpen (K : Set C) →
      IsOpen (Ideal.closure (K.map φ) : Set D) := by
    intro K hK
    obtain ⟨I, hIopen, hIK⟩ :=
      TopologicalRing.exists_isOpen_ideal_map_le (algebraMap A C) hC K hK
    let J : Ideal B := Ideal.closure (I.map (algebraMap A B))
    let i : TopologicalRing.TensorProductSubmoduleIndex (R := A) (M := B) (N := C) :=
      (⟨J.restrictScalars A, hTaut.1 I hIopen⟩, ⟨K.restrictScalars A, hK⟩)
    have hbasic :
        (TopologicalRing.tensorProductSubmoduleBasis i : Set (B ⊗[A] C)) ∈
          nhds (0 : B ⊗[A] C) :=
      (TopologicalRing.hasBasis_tensorProductTopology (R := A) (M := B) (N := C)).mem_of_mem
        (i := i) trivial
    have hclnhds :
        closure (UniformSpace.Completion.coeRingHom ''
          (TopologicalRing.tensorProductSubmoduleBasis i : Set (B ⊗[A] C))) ∈ nhds (0 : D) :=
      UniformSpace.Completion.isDenseInducing_coe.closure_image_mem_nhds hbasic
    have himage :
        UniformSpace.Completion.coeRingHom ''
          (TopologicalRing.tensorProductSubmoduleBasis i : Set (B ⊗[A] C)) ⊆
        (Ideal.closure (K.map φ) : Set D) := by
      rintro y ⟨x, hx, rfl⟩
      exact completedTensorProduct_coe_tensorProductSubmodule_le I J K hIK le_rfl x hx
    exact (Ideal.closure (K.map φ)).toAddSubgroup.isOpen_of_mem_nhds
      (Filter.mem_of_superset hclnhds (closure_minimal himage isClosed_closure))
  refine ⟨hOpen, IsLinearTopology.hasBasis_open_ideal.to_hasBasis (fun H hH => ?_)
    fun K hK => ⟨Ideal.closure (K.map φ), hOpen K hK, Set.Subset.rfl⟩⟩
  have hpreC : φ ⁻¹' (H : Set D) ∈ nhds (0 : C) :=
    hφ.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hH.mem_nhds H.zero_mem)
  obtain ⟨K, hKopen, hKpre⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hpreC
  have hKmap : Ideal.map φ K ≤ H := Ideal.map_le_iff_le_comap.mpr fun c hc => hKpre hc
  refine ⟨K, hKopen, ?_⟩
  change closure (Ideal.map φ K : Set D) ⊆ (H : Set D)
  exact closure_minimal (fun _ hy => hKmap hy) (H.toAddSubgroup.isClosed_of_isOpen hH)

end

end RingHom

end
