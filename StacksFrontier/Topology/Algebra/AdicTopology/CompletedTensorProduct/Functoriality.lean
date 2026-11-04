module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.UniformRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct

/-!
# Functoriality of the completed tensor product

The tensor product topology of Tag 0AMU is functorial: a pair of continuous linear maps
`f : M → M'` and `g : N → N'` induces a continuous map `M ⊗[R] N → M' ⊗[R] N'`, because the
basic open submodule attached to a pair `(P, Q)` of open submodules of the targets pulls back
to a submodule containing the basic open submodule attached to `(f⁻¹ P, g⁻¹ Q)`.  Completing,
a pair of continuous algebra maps induces a ring homomorphism of completed tensor products.

Specialising `f` to the identity gives functoriality in the second variable, which is what the
identification `B ⊗̂[A] (R ⧸ K) ≃ (B ⊗̂[A] R) ⧸ K · (B ⊗̂[A] R)` is built from.

## Main definitions

* `TopologicalRing.completedTensorProductMap`: the ring homomorphism
  `A ⊗̂[R] B → A' ⊗̂[R] B'` induced by a pair of continuous algebra maps.
* `TopologicalRing.completedTensorProductMapRight`: its specialisation to the second variable,
  `B ⊗̂[R] C → B ⊗̂[R] C'`.

## Main results

* `TopologicalRing.tensorProductSubmodule_map_le`: the image of the basic open submodule at
  `(f⁻¹ P, g⁻¹ Q)` under `TensorProduct.map f g` lies in the basic open submodule at `(P, Q)`.
* `TopologicalRing.continuous_tensorProduct_map`: `TensorProduct.map f g` is continuous for the
  tensor product topologies.
* `TopologicalRing.completedTensorProductMap_coe`: the induced map on completions agrees with
  `TensorProduct.map f g` on the image of the tensor product.

## Implementation notes

The tensor product topology is not a global instance, so it and its uniformity are supplied by
hand at every statement, as elsewhere in this directory; the continuity statements are written
with `@Continuous` and both topologies spelled out.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

namespace TopologicalRing

section

open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- **The basic open submodules of the tensor product topology are functorial.**  The image
under `TensorProduct.map f g` of the basic submodule attached to the pair of preimages
`(f⁻¹ P, g⁻¹ Q)` is contained in the basic submodule attached to `(P, Q)`. -/
public theorem tensorProductSubmodule_map_le
    {M N M' N' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (P : Submodule R M') (Q : Submodule R N') :
    (tensorProductSubmodule (P.comap f) (Q.comap g)).map (TensorProduct.map f g) ≤
      tensorProductSubmodule P Q := by
  have hleft : TensorProduct.map f g ∘ₗ TensorProduct.map (P.comap f).subtype LinearMap.id =
      TensorProduct.map P.subtype (LinearMap.id : N' →ₗ[R] N') ∘ₗ
        TensorProduct.map ((f ∘ₗ (P.comap f).subtype).codRestrict P (fun x => x.2)) g := by
    ext x y
    rfl
  have hright : TensorProduct.map f g ∘ₗ TensorProduct.map LinearMap.id (Q.comap g).subtype =
      TensorProduct.map (LinearMap.id : M' →ₗ[R] M') Q.subtype ∘ₗ
        TensorProduct.map f ((g ∘ₗ (Q.comap g).subtype).codRestrict Q (fun x => x.2)) := by
    ext x y
    rfl
  unfold tensorProductSubmodule
  rw [Submodule.map_sup]
  refine sup_le ?_ ?_
  · rw [← LinearMap.range_comp, hleft]
    exact le_sup_of_le_left (LinearMap.range_comp_le_range _ _)
  · rw [← LinearMap.range_comp, hright]
    exact le_sup_of_le_right (LinearMap.range_comp_le_range _ _)

/-- **`TensorProduct.map` is continuous for the tensor product topologies** when both of its
arguments are continuous. -/
public theorem continuous_tensorProduct_map
    {M N M' N' : Type*}
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
    [AddCommGroup N'] [Module R N'] [TopologicalSpace N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (hf : Continuous f) (hg : Continuous g) :
    @Continuous (M ⊗[R] N) (M' ⊗[R] N')
      (tensorProductTopology (R := R) (M := M) (N := N))
      (tensorProductTopology (R := R) (M := M') (N := N'))
      (TensorProduct.map f g) := by
  let := tensorProductTopology (R := R) (M := M) (N := N)
  let := tensorProductTopology (R := R) (M := M') (N := N')
  apply continuous_of_continuousAt_zero (TensorProduct.map f g)
  change Filter.Tendsto (TensorProduct.map f g) (nhds 0) (nhds 0)
  refine ((hasBasis_tensorProductTopology (R := R) (M := M) (N := N)).tendsto_iff
    (hasBasis_tensorProductTopology (R := R) (M := M') (N := N'))).mpr ?_
  intro i _
  refine ⟨(⟨i.1.1.comap f, ?_⟩, ⟨i.2.1.comap g, ?_⟩), trivial, fun x hx ↦ ?_⟩
  · simpa [Submodule.comap_coe] using i.1.2.preimage hf
  · simpa [Submodule.comap_coe] using i.2.2.preimage hg
  · exact tensorProductSubmodule_map_le f g i.1.1 i.2.1
      (Submodule.mem_map_of_mem (show x ∈ tensorProductSubmodule _ _ from hx))

end

section Algebras

open scoped TensorProduct

variable {R A B A' B' : Type*} [CommRing R]
  [CommRing A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [Algebra R B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing A'] [Algebra R A'] [TopologicalSpace A'] [IsTopologicalRing A']
  [IsLinearTopology A' A']
  [CommRing B'] [Algebra R B'] [TopologicalSpace B'] [IsTopologicalRing B']
  [IsLinearTopology B' B']

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsTopologicalRing B] [IsLinearTopology B B]
  [IsTopologicalRing A'] [IsLinearTopology A' A'] [IsTopologicalRing B'] [IsLinearTopology B' B'] in
/-- **`Algebra.TensorProduct.map` is continuous for the tensor product topologies** when both
of its arguments are continuous. -/
public theorem continuous_algebraTensorProduct_map
    (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') (hφ : Continuous φ) (hψ : Continuous ψ) :
    @Continuous (A ⊗[R] B) (A' ⊗[R] B')
      (tensorProductTopology (R := R) (M := A) (N := B))
      (tensorProductTopology (R := R) (M := A') (N := B'))
      (Algebra.TensorProduct.map φ ψ) :=
  continuous_tensorProduct_map φ.toLinearMap ψ.toLinearMap hφ hψ

/-- **The completed tensor product is functorial in both variables.**  A pair of continuous
`R`-algebra maps `φ : A → A'` and `ψ : B → B'` induces a ring homomorphism
`A ⊗̂[R] B → A' ⊗̂[R] B'`, obtained by completing `Algebra.TensorProduct.map φ ψ`. -/
@[ega "0 7.7.3" "special case"]
public noncomputable def completedTensorProductMap
    (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') (hφ : Continuous φ) (hψ : Continuous ψ) :
    CompletedTensorProduct (R := R) (M := A) (N := B) →+*
      CompletedTensorProduct (R := R) (M := A') (N := B') :=
  letI : TopologicalSpace (A ⊗[R] B) := tensorProductTopology (R := R) (M := A) (N := B)
  letI : TopologicalSpace (A' ⊗[R] B') := tensorProductTopology (R := R) (M := A') (N := B')
  letI : UniformSpace (A ⊗[R] B) := tensorProductUniformSpace (R := R) (M := A) (N := B)
  letI : UniformSpace (A' ⊗[R] B') := tensorProductUniformSpace (R := R) (M := A') (N := B')
  letI : IsTopologicalRing (A ⊗[R] B) := tensorProduct_isTopologicalRing (R := R) (A := A)
    (B := B)
  letI : IsTopologicalRing (A' ⊗[R] B') := tensorProduct_isTopologicalRing (R := R) (A := A')
    (B := B')
  UniformSpace.Completion.mapRingHom (Algebra.TensorProduct.map φ ψ).toRingHom
    (continuous_algebraTensorProduct_map φ ψ hφ hψ)

/-- The induced map on completed tensor products agrees with `Algebra.TensorProduct.map` on the
image of the tensor product. -/
@[simp]
public theorem completedTensorProductMap_coe
    (φ : A →ₐ[R] A') (ψ : B →ₐ[R] B') (hφ : Continuous φ) (hψ : Continuous ψ)
    (t : A ⊗[R] B) :
    letI : TopologicalSpace (A ⊗[R] B) := tensorProductTopology (R := R) (M := A) (N := B)
    letI : TopologicalSpace (A' ⊗[R] B') := tensorProductTopology (R := R) (M := A') (N := B')
    letI : UniformSpace (A ⊗[R] B) := tensorProductUniformSpace (R := R) (M := A) (N := B)
    letI : UniformSpace (A' ⊗[R] B') := tensorProductUniformSpace (R := R) (M := A') (N := B')
    completedTensorProductMap φ ψ hφ hψ (t : CompletedTensorProduct (R := R) (M := A) (N := B))
      = ((Algebra.TensorProduct.map φ ψ t :
          A' ⊗[R] B') : CompletedTensorProduct (R := R) (M := A') (N := B')) := by
  let : TopologicalSpace (A ⊗[R] B) := tensorProductTopology (R := R) (M := A) (N := B)
  let : TopologicalSpace (A' ⊗[R] B') := tensorProductTopology (R := R) (M := A') (N := B')
  let : UniformSpace (A ⊗[R] B) := tensorProductUniformSpace (R := R) (M := A) (N := B)
  let : UniformSpace (A' ⊗[R] B') := tensorProductUniformSpace (R := R) (M := A') (N := B')
  let : IsTopologicalRing (A ⊗[R] B) := tensorProduct_isTopologicalRing (R := R) (A := A)
    (B := B)
  let : IsTopologicalRing (A' ⊗[R] B') := tensorProduct_isTopologicalRing (R := R) (A := A')
    (B := B')
  exact UniformSpace.Completion.mapRingHom_coe
    (continuous_algebraTensorProduct_map φ ψ hφ hψ) t

/-- **Functoriality of the completed tensor product in the second variable.**  A continuous
`R`-algebra map `ψ : B → B'` induces a ring homomorphism `A ⊗̂[R] B → A ⊗̂[R] B'`. -/
@[ega "0 7.7.3" "special case"]
public noncomputable def completedTensorProductMapRight
    (ψ : B →ₐ[R] B') (hψ : Continuous ψ) :
    CompletedTensorProduct (R := R) (M := A) (N := B) →+*
      CompletedTensorProduct (R := R) (M := A) (N := B') :=
  completedTensorProductMap (AlgHom.id R A) ψ continuous_id hψ

/-- The second-variable induced map sends the image of `a ⊗ₜ b` to the image of `a ⊗ₜ ψ b`. -/
@[simp]
public theorem completedTensorProductMapRight_coe_tmul
    (ψ : B →ₐ[R] B') (hψ : Continuous ψ) (a : A) (b : B) :
    letI : TopologicalSpace (A ⊗[R] B) := tensorProductTopology (R := R) (M := A) (N := B)
    letI : TopologicalSpace (A ⊗[R] B') := tensorProductTopology (R := R) (M := A) (N := B')
    letI : UniformSpace (A ⊗[R] B) := tensorProductUniformSpace (R := R) (M := A) (N := B)
    letI : UniformSpace (A ⊗[R] B') := tensorProductUniformSpace (R := R) (M := A) (N := B')
    completedTensorProductMapRight (A := A) ψ hψ
        ((a ⊗ₜ[R] b : A ⊗[R] B) : CompletedTensorProduct (R := R) (M := A) (N := B)) =
      ((a ⊗ₜ[R] ψ b : A ⊗[R] B') :
        CompletedTensorProduct (R := R) (M := A) (N := B')) := by
  let : TopologicalSpace (A ⊗[R] B) := tensorProductTopology (R := R) (M := A) (N := B)
  let : TopologicalSpace (A ⊗[R] B') := tensorProductTopology (R := R) (M := A) (N := B')
  let : UniformSpace (A ⊗[R] B) := tensorProductUniformSpace (R := R) (M := A) (N := B)
  let : UniformSpace (A ⊗[R] B') := tensorProductUniformSpace (R := R) (M := A) (N := B')
  rw [completedTensorProductMapRight,
    completedTensorProductMap_coe (AlgHom.id R A) ψ continuous_id hψ (a ⊗ₜ[R] b)]
  norm_cast

end Algebras

end TopologicalRing

end
