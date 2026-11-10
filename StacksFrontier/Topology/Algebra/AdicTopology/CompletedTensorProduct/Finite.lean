module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# The completed tensor product of a finite algebra is the ordinary one

Let `A → B` and `A → C` be continuous maps of adic topological rings, adic for an ideal of
definition `I` of `A` and its extensions to `B` and to `C`, with `B` Noetherian and complete.
If `C` is finite as an `A`-module, then `B ⊗[A] C` carries the `I`-adic topology, is already
complete and Hausdorff for it, and so the canonical map to `B ⊗̂[A] C` is a bijection.

Both halves of the topological statement come down to one ideal computation: the ideal
`I · B · (B ⊗[A] C) + I · C · (B ⊗[A] C)` which `TopologicalRing.tensorProduct_basis_is_adic`
exhibits as an ideal of definition of the tensor-product topology is just
`I · (B ⊗[A] C)`, because the two factors induce the same `A`-action.  Completeness is then the
algebraic statement that a finite module over a complete Noetherian ring is complete
(Tag 00MA), applied over `B`: the tensor product is a finite `B`-module, and `I · (B ⊗[A] C)`
is the extension to it of the ideal of definition `I · B` of `B`.

## Main results

* `TopologicalRing.tensorProduct_idealOfDefinition_eq_map`: the ideal of definition of the
  tensor-product topology produced by `TopologicalRing.tensorProduct_basis_is_adic` is the
  extension of `I`.
* `TopologicalRing.isAdic_tensorProduct_map_algebraMap`: the tensor-product topology on
  `B ⊗[A] C` is the `I · (B ⊗[A] C)`-adic topology.
* `TopologicalRing.isAdicComplete_tensorProduct_of_finite`: `B ⊗[A] C` is
  `I · (B ⊗[A] C)`-adically complete when `C` is a finite `A`-module.
* `TopologicalRing.bijective_coe_completedTensorProduct_of_finite`: **`B ⊗[A] C = B ⊗̂[A] C`**
  for `C` finite over `A`.  This is a consequence of Tag 00MA, not a proof of it; 00MA itself is
  Mathlib's and is recorded in `StacksFrontier.RingTheory.AdicCompletion.Flat`.

## Implementation notes

The ideal of definition of the tensor-product topology is written as the sum of the extensions
of the two ideals of definition because that is the shape
`TopologicalRing.tensorProduct_basis_is_adic` produces; the first result here rewrites it as a
single extension, which is what both `IsAdicComplete.map_algebraMap_iff` and the ambient
`Ideal.map` API expect.

Bijectivity of the canonical map is deduced from completeness and separatedness by a general
fact about uniform completions: the range of the canonical map is dense, and is closed because
it is a complete subspace, hence is everything.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 00MA](https://stacks.math.columbia.edu/tag/00MA), cited, not proved
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

namespace TopologicalRing

open scoped TensorProduct

universe u

/-- **In a complete separated uniform space the canonical map to the completion is a
bijection.** -/
public theorem bijective_coe_completion {α : Type u} [UniformSpace α] [CompleteSpace α]
    [T0Space α] : Function.Bijective ((↑) : α → UniformSpace.Completion α) := by
  refine ⟨UniformSpace.Completion.coe_injective α, fun x => ?_⟩
  have hclosed : IsClosed (Set.range ((↑) : α → UniformSpace.Completion α)) :=
    ((UniformSpace.Completion.isUniformEmbedding_coe α).isComplete_range).isClosed
  have hdense := UniformSpace.Completion.denseRange_coe (α := α)
  rw [DenseRange, Dense] at hdense
  have := hdense x
  rwa [hclosed.closure_eq] at this

/-- **A complete separated uniform space is homeomorphic to its completion**, by the canonical
map. -/
public noncomputable def homeomorphCompletion {α : Type u} [UniformSpace α] [CompleteSpace α]
    [T0Space α] : α ≃ₜ UniformSpace.Completion α :=
  Equiv.toHomeomorphOfIsInducing (Equiv.ofBijective _ (bijective_coe_completion (α := α)))
    (UniformSpace.Completion.isUniformEmbedding_coe α).isInducing

/-- The homeomorphism `homeomorphCompletion` sends `x` to its image in the completion. -/
@[simp]
public theorem homeomorphCompletion_apply {α : Type u} [UniformSpace α] [CompleteSpace α]
    [T0Space α] (x : α) : homeomorphCompletion x = (x : UniformSpace.Completion α) := rfl

section

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- **The ideal of definition of the tensor-product topology is the extension of the base
ideal.**  The sum of the extensions of `I · B` and of `I · C` to `B ⊗[A] C` is the extension of
`I` itself: both summands are `I · (B ⊗[A] C)`, because the two inclusions restrict to the same
structure map on `A`. -/
public theorem tensorProduct_idealOfDefinition_eq_map (I : Ideal A) :
    Ideal.map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom
          (I.map (algebraMap A B)) +
        Ideal.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
          (I.map (algebraMap A C)) =
      I.map (algebraMap A (B ⊗[A] C)) := by
  have key : ∀ {D : Type u} [CommRing D] [Algebra A D] (f : D →ₐ[A] B ⊗[A] C),
      (I.map (algebraMap A D)).map f.toRingHom = I.map (algebraMap A (B ⊗[A] C)) := fun f => by
    rw [Ideal.map_map]
    exact congrArg (I.map) (RingHom.ext f.commutes)
  rw [key, key, Ideal.add_eq_sup, sup_idem]

/-- **`B ⊗[A] C` is complete when `C` is a finite `A`-module.**  The tensor product is a finite
module over the Noetherian complete ring `B`, hence complete for the extension of the ideal of
definition of `B`, which is the extension of `I`. -/
@[ega "0 7.7.8" "special case"]
public theorem isAdicComplete_tensorProduct_of_finite (I : Ideal A) [IsNoetherianRing B]
    [IsAdicComplete (I.map (algebraMap A B)) B] [Module.Finite A C] :
    IsAdicComplete (I.map (algebraMap A (B ⊗[A] C))) (B ⊗[A] C) := by
  have : Module.Finite B (B ⊗[A] C) := Module.Finite.base_change A B C
  have hB : IsAdicComplete (I.map (algebraMap A B)) (B ⊗[A] C) :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing (I.map (algebraMap A B))
      (B ⊗[A] C)
  have hmap : (I.map (algebraMap A B)).map (algebraMap B (B ⊗[A] C)) =
      I.map (algebraMap A (B ⊗[A] C)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B (B ⊗[A] C)]
  exact hmap ▸ (IsAdicComplete.map_algebraMap_iff (I.map (algebraMap A B)) (B ⊗[A] C)).mpr hB

variable [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- **The tensor-product topology is the adic topology of the extended base ideal.** -/
public theorem isAdic_tensorProduct_map_algebraMap (I : Ideal A)
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A C))) :
    letI : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
    _root_.IsAdic (I.map (algebraMap A (B ⊗[A] C))) := by
  have h := tensorProduct_basis_is_adic (B := A) (A := B) (C := C)
    (I.map (algebraMap A B)) (isIdealOfDefinition_of_isAdic hJ)
    (I.map (algebraMap A B)) (isIdealOfDefinition_of_isAdic hJ) hJ
    (I.map (algebraMap A C)) (isIdealOfDefinition_of_isAdic hK)
    (I.map (algebraMap A C)) (isIdealOfDefinition_of_isAdic hK) hK
  rwa [tensorProduct_idealOfDefinition_eq_map I] at h

/-- `B ⊗[A] C` is complete and separated for the tensor-product topology when `C` is finite. -/
private theorem completeSpace_and_t2Space_of_finite (I : Ideal A)
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A C)))
    [IsNoetherianRing B] [IsAdicComplete (I.map (algebraMap A B)) B] [Module.Finite A C] :
    letI : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
    CompleteSpace (B ⊗[A] C) ∧ T2Space (B ⊗[A] C) := by
  let : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
  have : IsUniformAddGroup (B ⊗[A] C) :=
    tensorProduct_isUniformAddGroup (R := A) (M := B) (N := C)
  exact (_root_.IsAdic.isAdicComplete_iff (isAdic_tensorProduct_map_algebraMap I hJ hK)).mp
    (isAdicComplete_tensorProduct_of_finite I)

/-- **The completed tensor product of a finite algebra is the ordinary one.**  If `C` is finite
as an `A`-module then the canonical map `B ⊗[A] C → B ⊗̂[A] C` is a bijection: the
tensor-product topology is the `I`-adic one, for which the tensor product is already complete
and separated.

This is the second paragraph of the proof of Tag 0GGR: "if `C` is finite as an `A`-module, then
`B ⊗_A C = B ⊗̂_A C`, as a finite module over a complete Noetherian ring is complete".  It is a
consequence of Tag 00MA and not a proof of it: the three parts of 00MA are Mathlib's, recorded
in `StacksFrontier.RingTheory.AdicCompletion.Flat`, and the corollary used here — a finite module
over a complete Noetherian ring is complete — is
`AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing`. -/
@[ega "0 7.7.8" "special case"]
public theorem bijective_coe_completedTensorProduct_of_finite (I : Ideal A)
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A C)))
    [IsNoetherianRing B] [IsAdicComplete (I.map (algebraMap A B)) B] [Module.Finite A C] :
    letI : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
    Function.Bijective
      ((↑) : B ⊗[A] C → CompletedTensorProduct (R := A) (M := B) (N := C)) := by
  let : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
  obtain ⟨hcomplete, hT2⟩ := completeSpace_and_t2Space_of_finite I hJ hK
  let : T2Space (B ⊗[A] C) := hT2
  exact bijective_coe_completion

/-- **`B ⊗[A] C` is complete and separated for the tensor-product topology** when `C` is a
finite `A`-module.  Together with `TopologicalRing.homeomorphCompletion` and
`TopologicalRing.bijective_coe_completion` this upgrades
`TopologicalRing.bijective_coe_completedTensorProduct_of_finite` to an isomorphism of
topological rings `B ⊗[A] C ≃ B ⊗̂[A] C`, along which any property of the canonical map from
either factor may be transported. -/
public theorem completeSpace_and_t2Space_tensorProduct_of_finite (I : Ideal A)
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A C)))
    [IsNoetherianRing B] [IsAdicComplete (I.map (algebraMap A B)) B] [Module.Finite A C] :
    letI : TopologicalSpace (B ⊗[A] C) := tensorProductTopology (R := A) (M := B) (N := C)
    letI : UniformSpace (B ⊗[A] C) := tensorProductUniformSpace (R := A) (M := B) (N := C)
    CompleteSpace (B ⊗[A] C) ∧ T2Space (B ⊗[A] C) := by
  exact completeSpace_and_t2Space_of_finite I hJ hK

end

end TopologicalRing

end
