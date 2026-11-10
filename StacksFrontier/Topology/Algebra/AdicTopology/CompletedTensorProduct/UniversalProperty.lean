module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The universal property of the completed tensor product

Let `R` be a commutative ring and let `A` and `C` be linearly topologized topological
`R`-algebras. The completed tensor product `A ⊗̂_R C` of Stacks 0AMU receives continuous ring
maps from `A` and from `C` which agree on `R`, and it is universal for this: a pair of
continuous ring maps `A → T`, `C → T` into a complete separated linearly topologized ring which
agree on `R` extends uniquely to a continuous ring map `A ⊗̂_R C → T`.

## Main definitions

* `TopologicalRing.completedTensorProductInl` and `TopologicalRing.completedTensorProductInr`:
  the two canonical maps into `A ⊗̂_R C`.
* `TopologicalRing.completedTensorProductLift`: the continuous ring map induced by a compatible
  pair.

## Main results

* `TopologicalRing.completedTensorProductLift_comp_inl`,
  `TopologicalRing.completedTensorProductLift_comp_inr` and
  `TopologicalRing.continuous_completedTensorProductLift`: existence.
* `TopologicalRing.completedTensorProduct_ringHom_ext`: uniqueness.

## Implementation notes

The lift is the extension to the completion of `Algebra.TensorProduct.lift`, for the `R`-algebra
structure the target receives from either map. It is continuous on `A ⊗_R C` for the tensor
product topology because a pure tensor `a ⊗ c` with `a` in the preimage of an open ideal `K` of
the target lands in `K`, and similarly in the second variable.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public noncomputable section

open Filter
open scoped TensorProduct Topology

namespace TopologicalRing

variable {R A C : Type*} [CommRing R]
  [CommRing A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [Algebra R C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- The canonical map `A → A ⊗̂_R C`, `a ↦ a ⊗ 1`. -/
@[ega "0 7.7.6"]
def completedTensorProductInl : A →+* CompletedTensorProduct (R := R) (M := A) (N := C) :=
  letI : TopologicalSpace (A ⊗[R] C) := tensorProductTopology (R := R) (M := A) (N := C)
  letI : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  letI : IsTopologicalRing (A ⊗[R] C) := tensorProduct_isTopologicalRing (R := R) (A := A)
    (B := C)
  UniformSpace.Completion.coeRingHom.comp Algebra.TensorProduct.includeLeftRingHom

/-- The canonical map `C → A ⊗̂_R C`, `c ↦ 1 ⊗ c`. -/
@[ega "0 7.7.6"]
def completedTensorProductInr : C →+* CompletedTensorProduct (R := R) (M := A) (N := C) :=
  letI : TopologicalSpace (A ⊗[R] C) := tensorProductTopology (R := R) (M := A) (N := C)
  letI : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  letI : IsTopologicalRing (A ⊗[R] C) := tensorProduct_isTopologicalRing (R := R) (A := A)
    (B := C)
  UniformSpace.Completion.coeRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom

/-- The canonical map `A → A ⊗̂_R C` sends `a` to the image of `a ⊗ 1`. -/
@[ega "0 7.7.6" "partial"]
theorem completedTensorProductInl_apply (a : A) :
    completedTensorProductInl (R := R) (C := C) a =
      ((a ⊗ₜ[R] (1 : C) : A ⊗[R] C) : CompletedTensorProduct (R := R) (M := A) (N := C)) :=
  rfl

/-- The canonical map `C → A ⊗̂_R C` sends `c` to the image of `1 ⊗ c`. -/
theorem completedTensorProductInr_apply (c : C) :
    completedTensorProductInr (R := R) (A := A) c =
      (((1 : A) ⊗ₜ[R] c : A ⊗[R] C) : CompletedTensorProduct (R := R) (M := A) (N := C)) :=
  rfl

/-- With the algebra structure of `A ⊗̂_R C` over its second factor, the canonical map from the
second factor is the structure map. -/
theorem completedTensorProductInr_eq_algebraMap :
    letI : Algebra C (A ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
    completedTensorProductInr (R := R) (A := A) (C := C) =
      algebraMap C (CompletedTensorProduct (R := R) (M := A) (N := C)) :=
  rfl

/-- The canonical map `A → A ⊗̂_R C` is continuous. -/
@[ega "0 7.7.6" "continuity of ρ"]
theorem continuous_completedTensorProductInl :
    Continuous (completedTensorProductInl (R := R) (A := A) (C := C)) := by
  let _ : TopologicalSpace (A ⊗[R] C) := tensorProductTopology (R := R) (M := A) (N := C)
  let _ : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  exact (UniformSpace.Completion.continuous_coe _).comp
    (continuous_tmul_const (R := R) (M := A) (N := C) (1 : C))

/-- The canonical map `C → A ⊗̂_R C` is continuous. -/
@[ega "0 7.7.6" "continuity of σ"]
theorem continuous_completedTensorProductInr :
    Continuous (completedTensorProductInr (R := R) (A := A) (C := C)) := by
  let _ : TopologicalSpace (A ⊗[R] C) := tensorProductTopology (R := R) (M := A) (N := C)
  let _ : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  exact (UniformSpace.Completion.continuous_coe _).comp
    (continuous_const_tmul (R := R) (M := A) (N := C) (1 : A))

/-- The two canonical maps agree on `R`. -/
theorem completedTensorProductInl_comp_algebraMap :
    (completedTensorProductInl (R := R) (A := A) (C := C)).comp (algebraMap R A) =
      (completedTensorProductInr (R := R) (A := A) (C := C)).comp (algebraMap R C) := by
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, completedTensorProductInl_apply,
    completedTensorProductInr_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

section Tensor

variable {T : Type*} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [IsLinearTopology T T]

/-- The ring map `A ⊗_R C → T` attached to a pair of ring maps agreeing on `R`. -/
@[ega "0 7.7.6"]
def tensorProductLiftOfCompat (α : A →+* T) (β : C →+* T)
    (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) : A ⊗[R] C →+* T :=
  letI : Algebra R T := (α.comp (algebraMap R A)).toAlgebra
  (Algebra.TensorProduct.lift (R := R) (S := R)
    ({ α with commutes' := fun _ ↦ rfl } : A →ₐ[R] T)
    ({ β with commutes' := fun r ↦ (RingHom.congr_fun h r).symm } : C →ₐ[R] T)
    (fun _ _ ↦ Commute.all _ _)).toRingHom

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [TopologicalSpace C]
  [IsTopologicalRing C] [IsLinearTopology C C] [TopologicalSpace T] [IsTopologicalRing T]
  [IsLinearTopology T T] in
/-- The ring map `A ⊗_R C → T` attached to `α` and `β` sends `a ⊗ c` to `α a * β c`. -/
@[ega "0 7.7.6" "partial", ega "I 3.2.3" "τ(b⊗c)=ρ(b)σ(c)"]
theorem tensorProductLiftOfCompat_tmul (α : A →+* T) (β : C →+* T)
    (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) (a : A) (c : C) :
    tensorProductLiftOfCompat α β h (a ⊗ₜ[R] c) = α a * β c := by
  let : Algebra R T := (α.comp (algebraMap R A)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ a c

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsTopologicalRing C] [IsLinearTopology C C] in
/-- If `α` and `β` are continuous, the ring map `A ⊗_R C → T` attached to them is continuous for
the tensor product topology. -/
@[ega "0 7.7.6" "more general"]
theorem continuous_tensorProductLiftOfCompat (α : A →+* T) (β : C →+* T) (hα : Continuous α)
    (hβ : Continuous β) (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) :
    @Continuous (A ⊗[R] C) T (tensorProductTopology (R := R) (M := A) (N := C)) _
      (tensorProductLiftOfCompat α β h) := by
  let _ := tensorProductTopology (R := R) (M := A) (N := C)
  let _ : IsTopologicalAddGroup (A ⊗[R] C) :=
    (tensorProductAddGroupFilterBasis (R := R) (M := A) (N := C)).isTopologicalAddGroup
  apply continuous_of_continuousAt_zero (tensorProductLiftOfCompat α β h)
  change Tendsto (tensorProductLiftOfCompat α β h) (𝓝 0) (𝓝 (tensorProductLiftOfCompat α β h 0))
  rw [map_zero]
  refine ((hasBasis_tensorProductTopology (R := R) (M := A) (N := C)).tendsto_iff
    IsLinearTopology.hasBasis_open_ideal).mpr ?_
  intro K hK
  let I : Ideal A := K.comap α
  let J : Ideal C := K.comap β
  refine ⟨(⟨I.restrictScalars R, hK.preimage hα⟩, ⟨J.restrictScalars R, hK.preimage hβ⟩),
    trivial, ?_⟩
  let L := tensorProductLiftOfCompat α β h
  let N : Submodule R (A ⊗[R] C) := (K.comap L).restrictScalars R
  have hle : tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R) ≤ N := by
    refine sup_le ?_ ?_ <;> rw [TensorProduct.range_map_eq_span_tmul, Submodule.span_le] <;>
      rintro _ ⟨a, c, rfl⟩ <;> change L (_ ⊗ₜ[R] _) ∈ K <;> rw [tensorProductLiftOfCompat_tmul]
    · exact K.mul_mem_right _ a.2
    · exact K.mul_mem_left _ c.2
  exact fun x hx ↦ hle hx

end Tensor

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T] [IsTopologicalRing T]
  [IsLinearTopology T T] [CompleteSpace T] [T0Space T]

/-- **The universal property of the completed tensor product.** A pair of continuous ring maps
`A → T` and `C → T` into a complete separated linearly topologized ring which agree on `R`
induces a ring map `A ⊗̂_R C → T`. -/
@[ega "0 7.7.6"]
def completedTensorProductLift (α : A →+* T) (β : C →+* T) (hα : Continuous α)
    (hβ : Continuous β) (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) :
    CompletedTensorProduct (R := R) (M := A) (N := C) →+* T :=
  letI : TopologicalSpace (A ⊗[R] C) := tensorProductTopology (R := R) (M := A) (N := C)
  letI : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  letI : IsTopologicalRing (A ⊗[R] C) := tensorProduct_isTopologicalRing (R := R) (A := A)
    (B := C)
  UniformSpace.Completion.extensionHom (tensorProductLiftOfCompat α β h)
    (continuous_tensorProductLiftOfCompat α β hα hβ h)

/-- On the image of `A ⊗_R C`, the lift `A ⊗̂_R C → T` agrees with the ring map
`tensorProductLiftOfCompat`. -/
@[ega "0 7.7.6" "partial"]
theorem completedTensorProductLift_coe (α : A →+* T) (β : C →+* T) (hα : Continuous α)
    (hβ : Continuous β) (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) (x : A ⊗[R] C) :
    letI : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
    completedTensorProductLift α β hα hβ h
        (x : CompletedTensorProduct (R := R) (M := A) (N := C)) =
      tensorProductLiftOfCompat α β h x := by
  let _ : TopologicalSpace (A ⊗[R] C) := tensorProductTopology (R := R) (M := A) (N := C)
  let _ : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  let _ : IsTopologicalRing (A ⊗[R] C) := tensorProduct_isTopologicalRing (R := R) (A := A)
    (B := C)
  exact UniformSpace.Completion.extensionHom_coe _ _ x

/-- The lift `A ⊗̂_R C → T` is continuous. -/
@[ega "0 7.7.6" "continuity of w"]
theorem continuous_completedTensorProductLift (α : A →+* T) (β : C →+* T) (hα : Continuous α)
    (hβ : Continuous β) (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) :
    Continuous (completedTensorProductLift α β hα hβ h) := by
  let _ : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  exact UniformSpace.Completion.continuous_extension

/-- The lift `A ⊗̂_R C → T` restricts to `α` along the canonical map from `A`. -/
@[ega "0 7.7.6" "factorization u = w ∘ ρ"]
theorem completedTensorProductLift_comp_inl (α : A →+* T) (β : C →+* T) (hα : Continuous α)
    (hβ : Continuous β) (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) :
    (completedTensorProductLift α β hα hβ h).comp completedTensorProductInl = α := by
  ext a
  rw [RingHom.comp_apply, completedTensorProductInl_apply, completedTensorProductLift_coe,
    tensorProductLiftOfCompat_tmul, map_one, mul_one]

/-- The lift `A ⊗̂_R C → T` restricts to `β` along the canonical map from `C`. -/
@[ega "0 7.7.6" "factorization v = w ∘ σ"]
theorem completedTensorProductLift_comp_inr (α : A →+* T) (β : C →+* T) (hα : Continuous α)
    (hβ : Continuous β) (h : α.comp (algebraMap R A) = β.comp (algebraMap R C)) :
    (completedTensorProductLift α β hα hβ h).comp completedTensorProductInr = β := by
  ext c
  rw [RingHom.comp_apply, completedTensorProductInr_apply, completedTensorProductLift_coe,
    tensorProductLiftOfCompat_tmul, map_one, one_mul]

omit [IsTopologicalRing T] [IsLinearTopology T T] [IsUniformAddGroup T] [CompleteSpace T]
  [T0Space T] in
/-- **Uniqueness in the universal property of the completed tensor product.** Two continuous ring
maps out of `A ⊗̂_R C` into a separated ring which agree on the images of `A` and of `C` are
equal. -/
@[ega "0 7.7.6" "more general"]
theorem completedTensorProduct_ringHom_ext [T2Space T]
    {φ ψ : CompletedTensorProduct (R := R) (M := A) (N := C) →+* T} (hφ : Continuous φ)
    (hψ : Continuous ψ) (hl : φ.comp completedTensorProductInl = ψ.comp completedTensorProductInl)
    (hr : φ.comp completedTensorProductInr = ψ.comp completedTensorProductInr) : φ = ψ := by
  let _ : UniformSpace (A ⊗[R] C) := tensorProductUniformSpace (R := R) (M := A) (N := C)
  refine RingHom.coe_inj (UniformSpace.Completion.ext hφ hψ fun x ↦ ?_)
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    have e : (((a ⊗ₜ[R] c : A ⊗[R] C)) : CompletedTensorProduct (R := R) (M := A) (N := C)) =
        completedTensorProductInl a * completedTensorProductInr c := by
      rw [completedTensorProductInl_apply, completedTensorProductInr_apply,
        ← UniformSpace.Completion.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, ← RingHom.comp_apply φ, ← RingHom.comp_apply ψ, hl,
      ← RingHom.comp_apply φ, ← RingHom.comp_apply ψ, hr]
  | add x y hx hy => rw [UniformSpace.Completion.coe_add, map_add, map_add, hx, hy]

end TopologicalRing

end
