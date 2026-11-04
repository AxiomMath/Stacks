module

public import StacksFrontier.RingTheory.DeRham.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseExteriorSymmetricAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk

/-!
# Exterior powers commute with base change

Let `R` be a commutative ring, `A` a commutative `R`-algebra and `M` an `R`-module. This file
proves

`A ⊗_R ⋀ⁿ_R(M) ≅ ⋀ⁿ_A(A ⊗_R M)`,

the exterior counterpart of `SymmetricAlgebra.symmetricPowerBaseChange`, together with the
equation pinning it down on wedges of generators and its naturality in the algebra `A`.

## Main definitions

* `ExteriorAlgebra.exteriorPowerBaseChangeAlt`: the `R`-alternating map
  `v ↦ (1 ⊗ v 0) ∧ ⋯ ∧ (1 ⊗ v (n-1))` with values in `⋀ⁿ_A(A ⊗_R M)`.
* `ExteriorAlgebra.exteriorPowerBaseChangeMap`: the induced `R`-linear map
  `⋀ⁿ_R(M) → ⋀ⁿ_A(A ⊗_R M)`.
* `ExteriorAlgebra.exteriorPowerBaseChange`: **the degreewise comparison
  `A ⊗_R ⋀ⁿ_R(M) ≃ₗ[A] ⋀ⁿ_A(A ⊗_R M)`.**

## Main results

* `ExteriorAlgebra.isBaseChange_exteriorPowerBaseChangeMap`: the induced map exhibits
  `⋀ⁿ_A(A ⊗_R M)` as the base change of `⋀ⁿ_R(M)`, which is what makes the comparison an
  isomorphism.
* `ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti`: the comparison carries
  `a ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to `a · ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ))`. Since those wedges span
  (`exteriorPower.ιMulti_span`), this pins the comparison down.
* `ExteriorAlgebra.exteriorPowerBaseChange_naturality`: for a ring map `φ : A →+* B` over `R`
  and a `φ`-semilinear map `u : A ⊗_R M → B ⊗_R M` fixing the elements `1 ⊗ m`, the comparisons
  for `A` and for `B` agree, read inside the exterior algebras.

## Implementation notes

Unlike the symmetric case, the degreewise statement is not obtained by restricting an
algebra-level comparison to a graded summand, but from the universal property directly:
`DeRhamBaseChange.isBaseChange_exteriorPower` says that a degree-`n` map compatible with
`exteriorPower.ιMulti` and with a base change in degree one is itself a base change, because an
alternating `R`-multilinear map on `M` extends uniquely to an alternating `A`-multilinear map on
`A ⊗_R M`. The degree-one input is `TensorProduct.isBaseChange`.

Hence no flatness and no characteristic hypothesis appears: the square-zero relation
is never manipulated, only the alternating-map universal property is used.

**The ℤ-graded reading.** `ExteriorAlgebra.intPiece R M (n : ℤ)` is `⋀[R]^n M` definitionally
for `n ≥ 0` (`ExteriorAlgebra.intPiece_natCast`); `ExteriorAlgebra.intPieceBaseChange` states the
comparison in that spelling, in which the modules on the two sides are syntactically equal.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open scoped TensorProduct

namespace ExteriorAlgebra

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (M : Type*) [AddCommGroup M] [Module R M]

/-- The `R`-alternating map `v ↦ (1 ⊗ v 0) ∧ ⋯ ∧ (1 ⊗ v (n-1))` with values in the `n`-th
exterior power of the base change. -/
noncomputable def exteriorPowerBaseChangeAlt (n : ℕ) :
    M [⋀^Fin n]→ₗ[R] ↥(⋀[A]^n (A ⊗[R] M)) where
  toMultilinearMap :=
    ((exteriorPower.ιMulti A n).toMultilinearMap.restrictScalars R).compLinearMap
      fun _ => TensorProduct.mk R A M 1
  map_eq_zero_of_eq' _v _i _j hv hij :=
    (exteriorPower.ιMulti A n).map_eq_zero_of_eq _
      (congrArg (fun m => (1 : A) ⊗ₜ[R] m) hv) hij

/-- The `R`-linear map `⋀ⁿ_R(M) → ⋀ⁿ_A(A ⊗_R M)` induced by the alternating map. -/
noncomputable def exteriorPowerBaseChangeMap (n : ℕ) :
    ↥(⋀[R]^n M) →ₗ[R] ↥(⋀[A]^n (A ⊗[R] M)) :=
  exteriorPower.alternatingMapLinearEquiv (exteriorPowerBaseChangeAlt R A M n)

/-- The induced map sends `m₁ ∧ ⋯ ∧ mₙ` to `(1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ)`. -/
@[simp]
theorem exteriorPowerBaseChangeMap_ιMulti (n : ℕ) (v : Fin n → M) :
    exteriorPowerBaseChangeMap R A M n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti A n fun i => (1 : A) ⊗ₜ[R] v i :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- **The `n`-th exterior power of the base change is the base change of the `n`-th exterior
power.** -/
theorem isBaseChange_exteriorPowerBaseChangeMap (n : ℕ) :
    IsBaseChange A (exteriorPowerBaseChangeMap R A M n) :=
  DeRhamBaseChange.isBaseChange_exteriorPower
    (TensorProduct.isBaseChange (R := R) (M := M) (S := A)) _
    (exteriorPowerBaseChangeMap_ιMulti R A M n)

/-- **The exterior powers commute with base change.** For a commutative `R`-algebra `A` and an
`R`-module `M`, the base change of the `n`-th exterior power of `M` is the `n`-th exterior power
of the base change of `M`. -/
noncomputable def exteriorPowerBaseChange (n : ℕ) :
    A ⊗[R] ↥(⋀[R]^n M) ≃ₗ[A] ↥(⋀[A]^n (A ⊗[R] M)) :=
  (isBaseChange_exteriorPowerBaseChangeMap R A M n).equiv

/-- The degreewise comparison carries `a ⊗ x` to `a` times the image of `x` under
`ExteriorAlgebra.exteriorPowerBaseChangeMap`. -/
theorem exteriorPowerBaseChange_tmul (n : ℕ) (a : A) (x : ↥(⋀[R]^n M)) :
    exteriorPowerBaseChange R A M n (a ⊗ₜ[R] x) =
      a • exteriorPowerBaseChangeMap R A M n x :=
  (isBaseChange_exteriorPowerBaseChangeMap R A M n).equiv_tmul a x

/-- The comparison carries `a ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to `a • ((1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₙ))`. -/
theorem exteriorPowerBaseChange_tmul_ιMulti (n : ℕ) (a : A) (v : Fin n → M) :
    exteriorPowerBaseChange R A M n (a ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      a • exteriorPower.ιMulti A n fun i => (1 : A) ⊗ₜ[R] v i := by
  rw [exteriorPowerBaseChange_tmul, exteriorPowerBaseChangeMap_ιMulti]


/-! ### Naturality in the algebra -/

section Naturality

variable {B : Type*} [CommRing B] [Algebra R B]

/-- **The comparison map is natural in the algebra.** A ring map `φ : A →+* B` over `R`, together
with a `φ`-semilinear map `u` on the base changes of `M` fixing the elements `1 ⊗ m`, carries the
comparison for `A` to the comparison for `B`. -/
theorem powMapₛₗ_exteriorPowerBaseChangeMap (φ : A →+* B)
    (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (u : A ⊗[R] M →ₛₗ[φ] B ⊗[R] M) (hu : ∀ m : M, u ((1 : A) ⊗ₜ[R] m) = (1 : B) ⊗ₜ[R] m)
    (n : ℕ) (x : ↥(⋀[R]^n M)) :
    powMapₛₗ n φ u (exteriorPowerBaseChangeMap R A M n x) =
      exteriorPowerBaseChangeMap R B M n x := by
  let G : ↥(⋀[R]^n M) →ₗ[R] ↥(⋀[B]^n (B ⊗[R] M)) :=
    { toFun := fun y => powMapₛₗ n φ u (exteriorPowerBaseChangeMap R A M n y)
      map_add' := fun y z => by simp only [map_add]
      map_smul' := fun r y => by
        show powMapₛₗ n φ u (exteriorPowerBaseChangeMap R A M n (r • y)) =
          r • powMapₛₗ n φ u (exteriorPowerBaseChangeMap R A M n y)
        have h1 : exteriorPowerBaseChangeMap R A M n (r • y) =
            (algebraMap R A r) • exteriorPowerBaseChangeMap R A M n y := by
          rw [map_smul, algebraMap_smul]
        rw [h1, map_smulₛₗ, hφ, algebraMap_smul] }
  have hG : G = exteriorPowerBaseChangeMap R B M n := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    show powMapₛₗ n φ u (exteriorPowerBaseChangeMap R A M n (exteriorPower.ιMulti R n v)) =
      exteriorPowerBaseChangeMap R B M n (exteriorPower.ιMulti R n v)
    rw [exteriorPowerBaseChangeMap_ιMulti, exteriorPowerBaseChangeMap_ιMulti,
      powMapₛₗ_ιMulti (R := A) (M := A ⊗[R] M) n φ u]
    exact congrArg (exteriorPower.ιMulti B n) (funext fun i => hu (v i))
  exact congrArg (fun k : ↥(⋀[R]^n M) →ₗ[R] ↥(⋀[B]^n (B ⊗[R] M)) => k x) hG

/-- **Naturality of the degreewise base-change comparison**, read inside the exterior algebra of
the base change. -/
theorem exteriorPowerBaseChange_naturality (φ : A →+* B)
    (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (u : A ⊗[R] M →ₛₗ[φ] B ⊗[R] M) (hu : ∀ m : M, u ((1 : A) ⊗ₜ[R] m) = (1 : B) ⊗ₜ[R] m)
    (n : ℕ) (a : A) (x : ↥(⋀[R]^n M)) :
    mapₛₗ φ u (exteriorPowerBaseChange R A M n (a ⊗ₜ[R] x) :
        ExteriorAlgebra A (A ⊗[R] M)) =
      (exteriorPowerBaseChange R B M n (φ a ⊗ₜ[R] x) : ExteriorAlgebra B (B ⊗[R] M)) := by
  rw [exteriorPowerBaseChange_tmul, exteriorPowerBaseChange_tmul, Submodule.coe_smul,
    Submodule.coe_smul, mapₛₗ_smul]
  exact congrArg (fun y : ExteriorAlgebra B (B ⊗[R] M) => φ a • y)
    (congrArg Subtype.val (powMapₛₗ_exteriorPowerBaseChangeMap R A M φ hφ u hu n x))

end Naturality

/-! ### The ℤ-graded spelling -/

/-- The comparison `A ⊗_R ⋀ⁿ_R(M) ≃ₗ[A] ⋀ⁿ_A(A ⊗_R M)` in the `ℤ`-graded spelling
`ExteriorAlgebra.intPiece`. -/
noncomputable def intPieceBaseChange (n : ℕ) :
    A ⊗[R] ↥(intPiece R M (n : ℤ)) ≃ₗ[A] ↥(intPiece A (A ⊗[R] M) (n : ℤ)) :=
  exteriorPowerBaseChange R A M n

/-- The `ℤ`-graded comparison carries `a ⊗ x` to `a` times the image of `x` under
`ExteriorAlgebra.exteriorPowerBaseChangeMap`, as elements of the exterior algebra. -/
theorem intPieceBaseChange_tmul (n : ℕ) (a : A) (x : ↥(intPiece R M (n : ℤ))) :
    (intPieceBaseChange R A M n (a ⊗ₜ[R] x) : ExteriorAlgebra A (A ⊗[R] M)) =
      (a • exteriorPowerBaseChangeMap R A M n x : ↥(⋀[A]^n (A ⊗[R] M))) :=
  congrArg Subtype.val (exteriorPowerBaseChange_tmul R A M n a x)

/-- **Naturality in the `ℤ`-graded spelling.** Same statement as
`ExteriorAlgebra.exteriorPowerBaseChange_naturality`, with the comparison written as
`ExteriorAlgebra.intPieceBaseChange`. -/
theorem intPieceBaseChange_naturality {B : Type*} [CommRing B] [Algebra R B] (φ : A →+* B)
    (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (u : A ⊗[R] M →ₛₗ[φ] B ⊗[R] M) (hu : ∀ m : M, u ((1 : A) ⊗ₜ[R] m) = (1 : B) ⊗ₜ[R] m)
    (n : ℕ) (a : A) (x : ↥(intPiece R M (n : ℤ))) :
    mapₛₗ φ u (intPieceBaseChange R A M n (a ⊗ₜ[R] x) : ExteriorAlgebra A (A ⊗[R] M)) =
      (intPieceBaseChange R B M n (φ a ⊗ₜ[R] x) : ExteriorAlgebra B (B ⊗[R] M)) :=
  exteriorPowerBaseChange_naturality R A M φ hφ u hu n a x

end ExteriorAlgebra

end
