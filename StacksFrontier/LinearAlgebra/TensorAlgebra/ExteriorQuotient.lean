module

public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# The exterior power of a module as a quotient of its tensor power

Let `R` be a commutative ring and `M` an `R`-module. The canonical homomorphism of algebras
`TensorAlgebra R M ⟶ ExteriorAlgebra R M` extending the degree-one generator restricts in each
degree to a surjection

`Tᵏ(M) = TensorAlgebra.gradedPiece R k M ⟶ ⋀ᵏ(M) = ⋀[R]^k M`,

and this file constructs it, proves it surjective, and shows that it commutes with base change
along a ring homomorphism.

## Main definitions

* `ExteriorAlgebra.algHom`: the canonical homomorphism of algebras
  `TensorAlgebra R M →ₐ[R] ExteriorAlgebra R M`. The symmetric analogue is Mathlib's
  `SymmetricAlgebra.algHom`, which exists because the symmetric algebra is *defined* as a
  quotient of the tensor algebra; the exterior algebra is a quotient of the tensor algebra by a
  `RingQuot` of a relation on it (it is `CliffordAlgebra 0`), but the quotient map itself is not
  in Mathlib, so it is built here from `TensorAlgebra.lift`.
* `TensorAlgebra.extQuot k`: **the surjection `Tᵏ(M) ⟶ ⋀ᵏ(M)`**, the degree-`k` part of
  `ExteriorAlgebra.algHom`.

## Main results

* `TensorAlgebra.map_gradedPiece_eq_exteriorPower`: `ExteriorAlgebra.algHom` carries the
  degree-`k` piece of the tensor algebra *onto* the `k`-th exterior power, both being the `k`-th
  power of the range of the respective degree-one generator.
* `TensorAlgebra.surjective_extQuot`: `Tᵏ(M) ⟶ ⋀ᵏ(M)` is surjective.
* `ExteriorAlgebra.algHom_mapₛₗ` and `ExteriorAlgebra.powMapₛₗ_extQuot`: **base change commutes
  with the canonical map to the exterior algebra**, and with its degree-`k` part.

## Implementation notes

**Why no kernel computation.** The symmetric sibling of this file,
`StacksFrontier.LinearAlgebra.TensorAlgebra.SymmetricQuotient`, computes the *kernel* of
`Tᵏ(M) ⟶ Symᵏ(M)`: it is the sum of the ranges of the `k - 1` endomorphisms of `Tᵏ(M)`
antisymmetrising two adjacent slots. There is no such statement on the exterior side, and the
obstruction is not incidental: the kernel of `Tᵏ(M) ⟶ ⋀ᵏ(M)` is cut out by the *squares*
`ι x · ι x`, and `x ↦ x ⊗ x` is quadratic, so in characteristic two the kernel is strictly
larger than the sum of the ranges of the symmetrisers `𝟙 + τ_p` and is not the image of any
morphism built from `M` by linear algebra.

**Why `algHom` is a `def` and not an `abbrev`.** `SymmetricAlgebra.algHom` is an `abbrev` for the
quotient map of the defining `RingCon`, so that the symmetric algebra's own `rfl` lemmas see
through it. Here `algHom` is `TensorAlgebra.lift` applied to the exterior generator, and the
equation that determines it is `ExteriorAlgebra.algHom_ι`, which is `TensorAlgebra.lift_ι_apply`
and not `rfl`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public noncomputable section

namespace ExteriorAlgebra

/-! ### The canonical map from the tensor algebra -/

section AlgHom

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **The canonical homomorphism of algebras from the tensor algebra to the exterior algebra**,
extending the degree-one generator of the exterior algebra. -/
def algHom : TensorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  TensorAlgebra.lift R (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)

/-- `ExteriorAlgebra.algHom` sends the generator `TensorAlgebra.ι R m` to
`ExteriorAlgebra.ι R m`. -/
@[simp]
theorem algHom_ι (m : M) : algHom R M (TensorAlgebra.ι R m) = ExteriorAlgebra.ι R m :=
  TensorAlgebra.lift_ι_apply _ _

/-- `ExteriorAlgebra.algHom` composed with `TensorAlgebra.ι R` is `ExteriorAlgebra.ι R`. -/
theorem algHom_comp_ι :
    (algHom R M).toLinearMap ∘ₗ (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) =
      (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) :=
  LinearMap.ext (algHom_ι R M)

end AlgHom

end ExteriorAlgebra

/-! ### The quotient map in a fixed degree -/

namespace TensorAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The canonical map to the exterior algebra carries the degree-`k` piece of the tensor algebra
onto the `k`-th exterior power: both are the `k`-th power of the range of the degree-one
generator, and the map carries one range onto the other. -/
theorem map_gradedPiece_eq_exteriorPower (k : ℕ) :
    Submodule.map (ExteriorAlgebra.algHom R M).toLinearMap (gradedPiece R k M) = ⋀[R]^k M := by
  have h1 : Submodule.map (ExteriorAlgebra.algHom R M).toLinearMap
      (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M)) =
      LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) := by
    rw [← ExteriorAlgebra.algHom_comp_ι R M, LinearMap.range_comp]
  rw [gradedPiece, Submodule.map_pow, h1, ExteriorAlgebra.exteriorPower]

/-- `ExteriorAlgebra.algHom` sends an element of the degree-`k` piece of the tensor algebra into
the `k`-th exterior power. -/
theorem algHom_mem_exteriorPower {k : ℕ} {x : TensorAlgebra R M} (hx : x ∈ gradedPiece R k M) :
    ExteriorAlgebra.algHom R M x ∈ ⋀[R]^k M := by
  rw [← map_gradedPiece_eq_exteriorPower k]
  exact Submodule.mem_map_of_mem hx

/-- **The canonical surjection `Tᵏ(M) ⟶ ⋀ᵏ(M)`**, the degree-`k` part of
`ExteriorAlgebra.algHom`. -/
def extQuot (k : ℕ) : gradedPiece R k M →ₗ[R] ⋀[R]^k M :=
  (ExteriorAlgebra.algHom R M).toLinearMap.restrict
    (fun _ hx => algHom_mem_exteriorPower hx)

/-- The image of `t` under `extQuot k`, viewed in the exterior algebra, is
`ExteriorAlgebra.algHom R M t`. -/
@[simp]
theorem coe_extQuot (k : ℕ) (t : gradedPiece R k M) :
    (extQuot k t : ExteriorAlgebra R M) = ExteriorAlgebra.algHom R M t := rfl

/-- The map `extQuot k : Tᵏ(M) ⟶ ⋀ᵏ(M)` is surjective. -/
theorem surjective_extQuot (k : ℕ) :
    Function.Surjective (extQuot (R := R) (M := M) k) := by
  rintro ⟨z, hz⟩
  rw [← map_gradedPiece_eq_exteriorPower k] at hz
  obtain ⟨x, hx, hxz⟩ := hz
  exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩

end TensorAlgebra

/-! ### Base change -/

namespace ExteriorAlgebra

section BaseChange

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]

/-- **Base change commutes with the canonical map from the tensor algebra to the exterior
algebra.** -/
theorem algHom_mapₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) (x : TensorAlgebra R M) :
    algHom S N (TensorAlgebra.mapₛₗ φ u x) = mapₛₗ φ u (algHom R M x) := by
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
      rw [TensorAlgebra.mapₛₗ_algebraMap, AlgHom.commutes, AlgHom.commutes, mapₛₗ_algebraMap]
  | ι m => rw [TensorAlgebra.mapₛₗ_ι, algHom_ι, algHom_ι, mapₛₗ_ι]
  | mul a b ha hb => simp only [map_mul]; rw [ha, hb]
  | add a b ha hb => simp only [map_add]; rw [ha, hb]

/-- **The degree-`k` part of the canonical map to the exterior algebra commutes with base
change.** -/
theorem powMapₛₗ_extQuot (k : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N)
    (t : TensorAlgebra.gradedPiece R k M) :
    powMapₛₗ k φ u (TensorAlgebra.extQuot k t) =
      TensorAlgebra.extQuot k (TensorAlgebra.powMapₛₗ k φ u t) :=
  Subtype.ext (by
    rw [powMapₛₗ_coe, TensorAlgebra.coe_extQuot, TensorAlgebra.coe_extQuot,
      TensorAlgebra.powMapₛₗ_coe, algHom_mapₛₗ])

end BaseChange

end ExteriorAlgebra

end
