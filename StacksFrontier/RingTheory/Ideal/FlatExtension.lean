module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The base change of an ideal along a flat ring map is its extension

Let `φ : R → S` be a homomorphism of commutative rings, written as an `Algebra R S` instance,
and let `u : M → R` be an `R`-linear map. Multiplying out gives an `S`-linear map
`S ⊗_R M → S`, `s ⊗ m ↦ s · φ(u m)`, whose image is the extension `J S = Ideal.map φ J` of the
image ideal `J` of `u`, for any `φ`. When `S` is flat over `R` and `u` is injective the map is
moreover injective; for `u` the inclusion of an ideal `I` this identifies the base change of `I`
with its extension,

`S ⊗_R I ≅ I S`.

## Main definitions

* `Stacks.FlatIdeal.toRing`: the `S`-linear map `S ⊗_R M → S` attached to `u : M →ₗ[R] R`.
* `Stacks.FlatIdeal.extensionEquiv`: the isomorphism `S ⊗_R I ≅ I S` for `S` flat over `R`.

## Main results

* `Stacks.FlatIdeal.toRing_tmul` and `Stacks.FlatIdeal.range_toRing`: the map is
  `s ⊗ m ↦ s φ(u m)` and its image is the extension of the image ideal of `u`; neither needs
  flatness.
* `Stacks.FlatIdeal.injective_toRing`: **flatness is what makes the map injective.** Tensoring
  an injective `u` with the flat module `S` preserves injectivity, and the right unitor
  `S ⊗_R R ≅ S` is an isomorphism.

## Implementation notes

The map is stated for an arbitrary `u : M →ₗ[R] R` rather than only for the inclusion of an
ideal, because the module it is applied to is a module of sections of a sheaf, identified with a
power of an ideal only through an isomorphism; taking `u` as data avoids transporting the tensor
product along that isomorphism.

## References

* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.FlatIdeal

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- The canonical `S`-linear map `S ⊗_R M → S` attached to an `R`-linear map `u : M → R`,
namely `s ⊗ m ↦ s · φ(u m)`: `u` tensored with `S`, followed by the right unitor
`S ⊗_R R ≅ S`. -/
noncomputable def toRing (u : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ LinearMap.baseChange S u

/-- The canonical map multiplies out: `s ⊗ m ↦ s · φ(u m)`. -/
@[simp] theorem toRing_tmul (u : M →ₗ[R] R) (s : S) (m : M) :
    toRing (S := S) u (s ⊗ₜ[R] m) = s * algebraMap R S (u m) := by
  simp [toRing, TensorProduct.AlgebraTensorModule.rid, Algebra.smul_def, mul_comm]

/-- The value of the canonical map lies in the extension of the image ideal of `u`. -/
theorem toRing_mem (u : M →ₗ[R] R) (x : S ⊗[R] M) :
    toRing (S := S) u x ∈ Ideal.map (algebraMap R S) (LinearMap.range u) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [toRing_tmul]
      exact Ideal.mul_mem_left _ _
        (Ideal.mem_map_of_mem _ (LinearMap.mem_range_self u m))
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy

/-- **The image of the canonical map is the extension of the image ideal of `u`**, for any
ring map. -/
theorem range_toRing (u : M →ₗ[R] R) :
    LinearMap.range (toRing (S := S) u) =
      Ideal.map (algebraMap R S) (LinearMap.range u) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨y, rfl⟩ := hx
    exact toRing_mem u y
  · rw [Ideal.map, Ideal.span_le]
    rintro x ⟨r, ⟨m, rfl⟩, rfl⟩
    refine ⟨(1 : S) ⊗ₜ[R] m, ?_⟩
    rw [toRing_tmul, one_mul]

/-- **Flatness is what makes the canonical map injective.** Tensoring an injective `u` with the
flat module `S` preserves injectivity, and the right unitor is an isomorphism. -/
theorem injective_toRing [Module.Flat R S] (u : M →ₗ[R] R)
    (hu : Function.Injective u) : Function.Injective (toRing (S := S) u) := by
  have h1 : Function.Injective (LinearMap.baseChange S (M := M) (N := R) u) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) u hu
    rwa [← LinearMap.baseChange_eq_ltensor] at h
  exact (TensorProduct.AlgebraTensorModule.rid R S S).injective.comp h1

/-- **The base change of an ideal along a flat ring map is its extension**, `S ⊗_R I ≅ I S`:
the case `u = (I ↪ R)` of `Stacks.FlatIdeal.injective_toRing` and `range_toRing`. -/
noncomputable def extensionEquiv [Module.Flat R S] (I : Ideal R) :
    (S ⊗[R] (I : Submodule R R)) ≃ₗ[S] (Ideal.map (algebraMap R S) I) :=
  (LinearEquiv.ofInjective (toRing (S := S) (I : Submodule R R).subtype)
      (injective_toRing _ Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [range_toRing, Submodule.range_subtype]))

/-- The isomorphism `extensionEquiv I`, followed by the inclusion `I S ⊆ S`, is the canonical
map `toRing` attached to the inclusion `I ↪ R`. -/
@[simp] theorem extensionEquiv_apply [Module.Flat R S] (I : Ideal R)
    (x : S ⊗[R] (I : Submodule R R)) :
    ((extensionEquiv (S := S) I x : Ideal.map (algebraMap R S) I) : S) =
      toRing (I : Submodule R R).subtype x := rfl

end Stacks.FlatIdeal

end
