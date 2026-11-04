module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded decomposition of the symmetric algebra

Let `R` be a commutative ring and `M` an `R`-module. `SymPow.symmetricPower n R M` is the
`n`-th symmetric power of `M`, realized as the submodule `(LinearMap.range (SymmetricAlgebra.ι
R M)) ^ n` of the symmetric algebra `SymmetricAlgebra R M`. These submodules make
`SymmetricAlgebra R M` an `ℕ`-graded `R`-algebra, so that the canonical map

`⨁ n, Symⁿ_R(M) → Sym_R(M)`

is an isomorphism. This is the analogue for the symmetric algebra of
`TensorAlgebra.gradedAlgebra` and `ExteriorAlgebra.gradedAlgebra`.

## Main definitions

* `SymmetricAlgebra.GradedAlgebra.ι`: `SymmetricAlgebra.ι` viewed as a map into the degree-one
  summand of `⨁ n, Symⁿ_R(M)`.
* `SymmetricAlgebra.GradedAlgebra.liftι`: the `R`-algebra map `Sym_R(M) → ⨁ n, Symⁿ_R(M)`
  extending it; this is the inverse of the canonical "recomposition" map.
* `SymmetricAlgebra.directSumSymmetricPowerEquiv`: the resulting `R`-linear equivalence
  `(⨁ n, Symⁿ_R(M)) ≃ₗ[R] Sym_R(M)`.
* `SymmetricAlgebra.symmetricPowerZeroEquiv`: the degree-zero identification
  `R ≃ₗ[R] Sym⁰_R(M)`.

## Main results

* `SymmetricAlgebra.gradedAlgebra`: `GradedAlgebra fun n : ℕ => Symⁿ_R(M)`. This is the
  decomposition of the symmetric algebra into its homogeneous pieces, and it is what makes
  `directSumSymmetricPowerEquiv` available.
* `SymmetricAlgebra.prod_ι_mem`: a product of `n` degree-one generators lies in `Symⁿ`.
* `SymmetricAlgebra.symmetricPower_eq_span_prod_ι`: those products *span* `Symⁿ`. Together with
  `prod_ι_mem` this is what makes a specification of a map on products of generators — the form
  Stacks 01CG and 01CH state their comparisons in — determine the map.
* `SymmetricAlgebra.symmetricPower_mul_symmetricPower_le`: multiplication is graded.

## Implementation notes

The proof follows `ExteriorAlgebra.gradedAlgebra`. The lift of `SymmetricAlgebra.ι` to
`⨁ n, Symⁿ_R(M)` needs no side condition, because that direct sum is commutative, being an
internal grading of the commutative ring `Sym_R(M)`; in the exterior case one has to verify that
squares vanish.

The symmetric power used is `SymPow.symmetricPower`, i.e. the degree-`n` *submodule* of
`SymmetricAlgebra R M` rather than a separately constructed quotient of a tensor power, since
`DirectSum.Decomposition` describes an internal grading by a family of submodules.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

namespace SymmetricAlgebra

open scoped DirectSum

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The symmetric powers `Symⁿ_R(M)` form a graded monoid in `SymmetricAlgebra R M`. -/
instance : SetLike.GradedMonoid fun n : ℕ => SymPow.symmetricPower n R M :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

/-- A version of `SymmetricAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `SymmetricAlgebra.gradedAlgebra`. -/
protected def GradedAlgebra.ι : M →ₗ[R] ⨁ n : ℕ, SymPow.symmetricPower n R M :=
  DirectSum.lof R ℕ (fun n => SymPow.symmetricPower n R M) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun m => by
      simpa only [pow_one] using LinearMap.mem_range_self _ m

/-- `SymmetricAlgebra.GradedAlgebra.ι` sends `m` to `SymmetricAlgebra.ι R M m` in degree one. -/
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun n : ℕ => SymPow.symmetricPower n R M) 1
        ⟨SymmetricAlgebra.ι R M m, by
          simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

/-- `SymmetricAlgebra.GradedAlgebra.ι` lifted to the symmetric algebra. This is primarily an
auxiliary construction used to provide `SymmetricAlgebra.gradedAlgebra`. -/
def GradedAlgebra.liftι :
    SymmetricAlgebra R M →ₐ[R] ⨁ n : ℕ, SymPow.symmetricPower n R M :=
  SymmetricAlgebra.lift (GradedAlgebra.ι R M)

/-- `SymmetricAlgebra.GradedAlgebra.liftι` sends an element of `Symⁿ_R(M)` to itself in the
degree-`n` summand. -/
theorem GradedAlgebra.liftι_eq (n : ℕ) (x : SymPow.symmetricPower n R M) :
    GradedAlgebra.liftι R M x =
      DirectSum.of (fun n => SymPow.symmetricPower n R M) n x := by
  obtain ⟨x, hx⟩ := x
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [map_mul, ih, GradedAlgebra.liftι, SymmetricAlgebra.lift_ι_apply,
        GradedAlgebra.ι_apply R M, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/-- The symmetric algebra is graded by the powers of the submodule
`LinearMap.range (SymmetricAlgebra.ι R M)`, that is, by the symmetric powers of `M`. -/
@[ega "II 1.7.1"]
instance gradedAlgebra : GradedAlgebra (fun n : ℕ => SymPow.symmetricPower n R M) :=
  GradedAlgebra.ofAlgHom _
    (-- while not necessary, the `by apply` makes this elaborate faster
    by apply GradedAlgebra.liftι R M)
    (by
      ext m
      change (DirectSum.coeAlgHom (fun n : ℕ => SymPow.symmetricPower n R M))
          (GradedAlgebra.liftι R M (SymmetricAlgebra.ι R M m)) = SymmetricAlgebra.ι R M m
      rw [GradedAlgebra.liftι, SymmetricAlgebra.lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.coeAlgHom_of])
    (by apply GradedAlgebra.liftι_eq R M)

/-- The decomposition of the symmetric algebra into its symmetric powers. -/
instance : DirectSum.Decomposition (fun n : ℕ => SymPow.symmetricPower n R M) :=
  (gradedAlgebra R M).toDecomposition

/-- The decomposition of the symmetric algebra into its symmetric powers, as an `R`-linear
equivalence `(⨁ n, Symⁿ_R(M)) ≃ₗ[R] Sym_R(M)`. -/
@[ega "II 1.7.1" "direct-sum decomposition"]
noncomputable def directSumSymmetricPowerEquiv :
    (⨁ n : ℕ, SymPow.symmetricPower n R M) ≃ₗ[R] SymmetricAlgebra R M :=
  (DirectSum.decomposeLinearEquiv (fun n : ℕ => SymPow.symmetricPower n R M)).symm

/-- `SymmetricAlgebra.directSumSymmetricPowerEquiv` sends an element of the degree-`n` summand
to itself. -/
@[simp]
theorem directSumSymmetricPowerEquiv_lof (n : ℕ) (x : SymPow.symmetricPower n R M) :
    directSumSymmetricPowerEquiv R M
        (DirectSum.lof R ℕ (fun n => SymPow.symmetricPower n R M) n x) = x :=
  DirectSum.decomposeLinearEquiv_symm_lof
    (fun n : ℕ => SymPow.symmetricPower n R M) n x

/-- Multiplication on the symmetric algebra is graded. -/
@[ega "II 1.7.1" "partial", sga "3 VIIB 1.2.4" "partial"]
theorem symmetricPower_mul_symmetricPower_le (m n : ℕ) :
    SymPow.symmetricPower m R M * SymPow.symmetricPower n R M ≤
      SymPow.symmetricPower (m + n) R M := by
  rw [SymPow.symmetricPower, SymPow.symmetricPower, SymPow.symmetricPower, pow_add]

variable {M} in
/-- A product of `n` degree-one generators lies in the `n`-th symmetric power. -/
theorem prod_ι_mem {n : ℕ} (s : Fin n → M) :
    ∏ i : Fin n, SymmetricAlgebra.ι R M (s i) ∈ SymPow.symmetricPower n R M := by
  have h := SetLike.prod_mem_graded (F := Finset.univ)
    (fun n : ℕ => SymPow.symmetricPower n R M)
    (fun _ : Fin n => 1) (fun i : Fin n => SymmetricAlgebra.ι R M (s i))
    fun i _ => by simpa only [pow_one] using LinearMap.mem_range_self _ (s i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

/-- The `n`-th symmetric power is spanned by the products of `n` degree-one generators. With
`SymmetricAlgebra.prod_ι_mem` this says that such products are exactly a spanning set of
`Symⁿ`, so an `R`-linear map out of `Symⁿ` is determined by its values on them. -/
theorem symmetricPower_eq_span_prod_ι (n : ℕ) :
    SymPow.symmetricPower n R M =
      Submodule.span R
        (Set.range fun s : Fin n → M => ∏ i : Fin n, SymmetricAlgebra.ι R M (s i)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [SymPow.symmetricPower, Submodule.pow_eq_span_pow_set, Submodule.span_le]
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Set.mem_pow_iff_prod.mp hx
    choose s hs using fun i => LinearMap.mem_range.mp (hf i)
    exact Submodule.subset_span ⟨s, by simp only [hs]⟩
  · rintro _ ⟨s, rfl⟩
    exact prod_ι_mem R s

/-- The degree-zero symmetric power is the image of the structure map, so it is a copy of the
base ring. -/
noncomputable def symmetricPowerZeroEquiv : R ≃ₗ[R] SymPow.symmetricPower 0 R M :=
  (LinearEquiv.ofInjective (Algebra.linearMap R (SymmetricAlgebra R M))
      fun x y h => (SymmetricAlgebra.algebraMap_inj (M := M) x y).mp h).trans
    (LinearEquiv.ofEq _ _ (by
      simp only [SymPow.symmetricPower, pow_zero]
      exact (Submodule.one_eq_range (R := R) (A := SymmetricAlgebra R M)).symm))

/-- `SymmetricAlgebra.symmetricPowerZeroEquiv` sends `r` to `algebraMap R _ r`. -/
@[simp]
theorem symmetricPowerZeroEquiv_apply (r : R) :
    (symmetricPowerZeroEquiv R M r : SymmetricAlgebra R M) = algebraMap R _ r :=
  rfl

end SymmetricAlgebra
