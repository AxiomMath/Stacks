module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Functoriality

/-!
# Right exactness of the tensor product topology in the second variable

Let `g : N → N'` be a surjective open continuous map of linearly topologized modules — the
quotient map by a submodule, for instance.  Then `id ⊗ g : M ⊗[R] N → M ⊗[R] N'` is a
surjective *open* map for the tensor product topologies of Tag 0AMU: the image of the basic
open submodule attached to `(P, Q)` is exactly the basic open submodule attached to
`(P, g Q)`.

Consequently `M ⊗[R] N'` carries the quotient topology of `M ⊗[R] N`, which is what turns the
algebraic right-exactness of the tensor product into a statement about completions.

## Main results

* `TopologicalRing.tensorProductSubmodule_map_lTensor`: the image of `tensorProductSubmodule
  P Q` under `id ⊗ g` is `tensorProductSubmodule P (Q.map g)`, for `g` surjective.
* `TopologicalRing.surjective_tensorProduct_lTensor`: `id ⊗ g` is surjective.
* `TopologicalRing.isOpenMap_tensorProduct_lTensor`: `id ⊗ g` is an open map.

## Implementation notes

Surjectivity of `id ⊗ g` is Mathlib's `LinearMap.lTensor_surjective`; it is restated here only
to have it in the shape `TensorProduct.map LinearMap.id g` that the topological statements use.

The tensor product topology is not a global instance, so it is supplied by hand at every
statement, as elsewhere in this directory.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public section

namespace TopologicalRing

section

open Set
open scoped TensorProduct Topology

variable {R M N N' : Type*} [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

/-- `id ⊗ g` is surjective when `g` is.  This is `LinearMap.lTensor_surjective` in the shape
`TensorProduct.map LinearMap.id g`. -/
@[sga "3 VIIB 0.3.2" "Corollary, special case"]
public theorem surjective_tensorProduct_lTensor (g : N →ₗ[R] N')
    (hg : Function.Surjective g) :
    Function.Surjective (TensorProduct.map (LinearMap.id : M →ₗ[R] M) g) :=
  LinearMap.lTensor_surjective M hg

/-- The image of `range φ` under `ψ` is `range φ'` when `ψ ∘ φ = φ' ∘ χ` with `χ` surjective. -/
private theorem map_range_eq_range_of_comp_eq {A B C D : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    {ψ : C →ₗ[R] D} {φ : A →ₗ[R] C} {φ' : B →ₗ[R] D} {χ : A →ₗ[R] B}
    (hχ : Function.Surjective χ) (h : ψ ∘ₗ φ = φ' ∘ₗ χ) :
    (LinearMap.range φ).map ψ = LinearMap.range φ' := by
  rw [← LinearMap.range_comp, h, LinearMap.range_comp, LinearMap.range_eq_top.mpr hχ,
    Submodule.map_top]

/-- **The basic open submodules of the tensor product topology are carried onto one another by a
surjection in the second variable.**  The image of the basic submodule attached to `(P, Q)`
under `id ⊗ g` is the basic submodule attached to `(P, g Q)`. -/
public theorem tensorProductSubmodule_map_lTensor (g : N →ₗ[R] N')
    (hg : Function.Surjective g) (P : Submodule R M) (Q : Submodule R N) :
    (tensorProductSubmodule P Q).map (TensorProduct.map LinearMap.id g) =
      tensorProductSubmodule P (Q.map g) := by
  have hQ : Function.Surjective ((g ∘ₗ Q.subtype).codRestrict (Q.map g)
      (fun x => Submodule.mem_map_of_mem x.2)) := by
    rintro ⟨_, q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩
  unfold tensorProductSubmodule
  rw [Submodule.map_sup]
  congr 1
  · exact map_range_eq_range_of_comp_eq (surjective_tensorProduct_lTensor (M := P) g hg)
      (by ext; rfl)
  · exact map_range_eq_range_of_comp_eq (surjective_tensorProduct_lTensor (M := M) _ hQ)
      (by ext; rfl)

variable [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']

/-- A basic open submodule of the tensor product topology is an open set. -/
private theorem isOpen_tensorProductSubmoduleBasis
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N')) :
    @IsOpen (M ⊗[R] N') (tensorProductTopology (R := R) (M := M) (N := N'))
      (tensorProductSubmoduleBasis i : Set (M ⊗[R] N')) := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N')
  exact (tensorProductSubmoduleBasis i).toAddSubgroup.isOpen_of_mem_nhds
    ((hasBasis_tensorProductTopology (R := R) (M := M) (N := N')).mem_of_mem (i := i) trivial)

/-- The image of an open submodule under `id ⊗ g` is open, for `g` a surjective open map. -/
private theorem isOpen_map_of_isOpen_submodule (g : N →ₗ[R] N')
    (hg : Function.Surjective g) (hgopen : IsOpenMap g)
    (L : Submodule R (M ⊗[R] N))
    (hL : @IsOpen (M ⊗[R] N) (tensorProductTopology (R := R) (M := M) (N := N))
      (L : Set (M ⊗[R] N))) :
    @IsOpen (M ⊗[R] N') (tensorProductTopology (R := R) (M := M) (N := N'))
      ((L.map (TensorProduct.map LinearMap.id g)) : Set (M ⊗[R] N')) := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  let _ := tensorProductTopology (R := R) (M := M) (N := N')
  obtain ⟨i, -, hi⟩ := (hasBasis_tensorProductTopology (R := R) (M := M) (N := N)).mem_iff.mp
    (hL.mem_nhds L.zero_mem)
  let j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N') :=
    (i.1, ⟨i.2.1.map g, by simpa [Submodule.map_coe] using hgopen _ i.2.2⟩)
  have hle : tensorProductSubmoduleBasis j ≤ L.map (TensorProduct.map LinearMap.id g) := by
    change tensorProductSubmodule i.1.1 (i.2.1.map g) ≤ _
    rw [← tensorProductSubmodule_map_lTensor g hg]
    exact Submodule.map_mono (show tensorProductSubmoduleBasis i ≤ L from fun y hy => hi hy)
  exact AddSubgroup.isOpen_mono
    (H₁ := (tensorProductSubmoduleBasis j).toAddSubgroup)
    (H₂ := (L.map (TensorProduct.map LinearMap.id g)).toAddSubgroup)
    (fun x hx => hle hx) (isOpen_tensorProductSubmoduleBasis (M := M) j)

/-- **`id ⊗ g` is an open map** for the tensor product topologies, when `g` is a surjective open
continuous map.  Together with surjectivity this says that `M ⊗[R] N'` carries the quotient
topology of `M ⊗[R] N`. -/
public theorem isOpenMap_tensorProduct_lTensor (g : N →ₗ[R] N')
    (hg : Function.Surjective g) (hgopen : IsOpenMap g) :
    @IsOpenMap (M ⊗[R] N) (M ⊗[R] N')
      (tensorProductTopology (R := R) (M := M) (N := N))
      (tensorProductTopology (R := R) (M := M) (N := N'))
      (TensorProduct.map LinearMap.id g) := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  let _ := tensorProductTopology (R := R) (M := M) (N := N')
  intro V hV
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hxV, rfl⟩
  obtain ⟨L, hL, hLV⟩ :=
    ((IsLinearTopology.hasBasis_open_submodule R).nhds_of_zero' x).mem_iff.mp (hV.mem_nhds hxV)
  refine Filter.mem_of_superset
    ((isOpenMap_add_left (TensorProduct.map (LinearMap.id : M →ₗ[R] M) g x)) _
      (isOpen_map_of_isOpen_submodule (M := M) g hg hgopen L hL)
      |>.mem_nhds ⟨0, (L.map (TensorProduct.map LinearMap.id g)).zero_mem, by simp⟩) ?_
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨x + w, hLV ⟨w, hw, rfl⟩, by simp⟩

end

end TopologicalRing

end
