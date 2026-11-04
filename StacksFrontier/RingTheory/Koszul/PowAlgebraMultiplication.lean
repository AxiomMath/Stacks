module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleOfTensor
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.OppositeHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorAlgebraGrading
public import StacksFrontier.RingTheory.Koszul.CohomologicalDifferentialGradedAlgebra

/-!
# The multiplication maps of the Koszul inverse system

Let `f₁, …, f_r` be elements of a commutative ring `R` and let `K_n = R⟨ξ₁, …, ξ_r⟩` be the
differential graded Koszul algebra with `d ξᵢ = fᵢ ^ n`. For `1 ≤ t ≤ m` the transition
homomorphism `K_m → K_t` and the identity of `K_t` have Koszul-anticommuting images, because the
exterior algebra is graded commutative; they therefore assemble into the *multiplication*
homomorphism
$$\mu_m : K_m \otimes_R K_t \longrightarrow K_t, \qquad
  a \otimes b \longmapsto \tau_{m,t}(a)\, b,$$
which applies the transition map to the left factor and multiplies.

Restricting the left regular module of `K_t` along the transition homomorphism gives the left
differential graded `K_m`-module `{}_mK_t`, that is, `K_t` with `K_m` acting through `τ_{m,t}`;
following the convention that a left `A`-module is a right module over the graded opposite
`Aᵒᵖᵖ`, it is an object of the derived category `D(K_mᵒᵖᵖ, d)`.

## Main definitions

* `Koszul.powMul`: the multiplication homomorphism `K_m ⊗_R K_t → K_t`.
* `Koszul.powRestrictedModule`: the left differential graded `K_m`-module `{}_mK_t`.
* `Koszul.powRestrictedObject`: `{}_mK_t` as an object of `D(K_mᵒᵖᵖ, d)`.

## Main results

* `Koszul.cohomological_mul_comm`: the exterior algebra is graded commutative for the
  cohomological grading, in which the `k`-th exterior power sits in degree `-k`.
* `Koszul.anticommutesAlong_cohomological`: any two homomorphisms into a cohomologically graded
  Koszul algebra have Koszul-anticommuting images.
* `Koszul.powMul_tmul`: the multiplication homomorphism sends `a ⊗ b` to `τ_{m,t}(a) b`.
* `Koszul.powMul_comp_includeLeft` and `Koszul.powMul_comp_includeRight`: it restricts to the
  transition homomorphism on the left factor and to the identity on the right factor.

## Implementation notes

Graded commutativity in the cohomological grading is deduced from
`ExteriorAlgebra.mul_comm_exteriorPower`, which is stated for the exterior grading with a sign in
`R`: in degrees `-p` and `-q` the Koszul sign `(-1)^((-q)(-p))` is `(-1)^(qp)`, so the regrading
does not change it.

## References

* [Stacks Project, Tag 0GZ3](https://stacks.math.columbia.edu/tag/0GZ3)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public section

namespace Koszul

universe u v

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra

section GradedCommutativity

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]

/-- The exterior algebra is graded commutative in the cohomological grading: elements of degrees
`i` and `j` commute up to the sign `(-1)^(i·j)`. -/
theorem cohomological_mul_comm {i j : ℤ} {x y : ExteriorAlgebra R E}
    (hx : x ∈ cohomologicalExteriorGrade R E i)
    (hy : y ∈ cohomologicalExteriorGrade R E j) :
    x * y = (-1 : ℤˣ) ^ (j * i) • (y * x) := by
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
      rw [cohomologicalExteriorGrade_neg_natCast] at hx hy
      rw [show -(q : ℤ) * -(p : ℤ) = ((q * p : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
        ExteriorAlgebra.zunits_neg_one_pow_smul, Nat.mul_comm q p]
      exact ExteriorAlgebra.mul_comm_exteriorPower hx hy
    · rw [eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R E (by omega) hy]
      simp
  · rw [eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R E (by omega) hx]
    simp

variable {R E}

/-- Two homomorphisms of differential graded algebras into the Koszul algebra of a functional
have Koszul-anticommuting images, because that algebra is graded commutative. -/
theorem anticommutesAlong_cohomological {C D : DifferentialGradedAlgebra.{u, max u v} R}
    {φ : Module.Dual R E} (f : C.Hom (cohomologicalDifferentialGradedAlgebra R E φ))
    (g : D.Hom (cohomologicalDifferentialGradedAlgebra R E φ)) :
    AnticommutesAlong C D (cohomologicalDifferentialGradedAlgebra R E φ) f g :=
  fun i j a b =>
    cohomological_mul_comm R E (f.map_grading i a a.2) (g.map_grading j b b.2)

end GradedCommutativity

section Multiplication

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The multiplication homomorphism `μ_m : K_m ⊗_R K_t → K_t` for `1 ≤ t ≤ m`: apply the
transition homomorphism to the left factor, then multiply in `K_t`. -/
noncomputable def powMul (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (tensorProduct (powAlgebra f m) (powAlgebra f t)).Hom (powAlgebra f t) :=
  tensorLift (anticommutesAlong_cohomological (powTransition f ht htm) (idHom (powAlgebra f t)))

/-- The multiplication homomorphism sends `a ⊗ b` to `τ_{m,t}(a) b`. -/
theorem powMul_tmul (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m)
    (a : (powAlgebra f m).A) (b : (powAlgebra f t).A) :
    (powMul f ht htm).toAlgebraHom
        (a ᵍ⊗ₜ[R] b : (powAlgebra f m).grading ᵍ⊗[R] (powAlgebra f t).grading) =
      (powTransition f ht htm).toAlgebraHom a * b := rfl

/-- The multiplication homomorphism restricts to the transition homomorphism on the left
factor. -/
theorem powMul_comp_includeLeft (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (powMul f ht htm).toAlgebraHom.comp
        (GradedTensorProduct.includeLeft (powAlgebra f m).grading (powAlgebra f t).grading) =
      (powTransition f ht htm).toAlgebraHom :=
  tensorLiftAlgebraHom_comp_includeLeft
    (anticommutesAlong_cohomological (powTransition f ht htm) (idHom (powAlgebra f t)))

/-- The multiplication homomorphism restricts to the identity on the right factor. -/
theorem powMul_comp_includeRight (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (powMul f ht htm).toAlgebraHom.comp
        (GradedTensorProduct.includeRight (powAlgebra f m).grading (powAlgebra f t).grading) =
      AlgHom.id R (powAlgebra f t).A :=
  tensorLiftAlgebraHom_comp_includeRight
    (anticommutesAlong_cohomological (powTransition f ht htm) (idHom (powAlgebra f t)))

end Multiplication

section RestrictedModule

open CategoryTheory DifferentialGradedModule DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The transition homomorphism `K_m → K_t`, read on the graded opposite algebras. -/
noncomputable def oppPowTransition (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (oppAlgebra (powAlgebra f m)).Hom (oppAlgebra (powAlgebra f t)) :=
  oppositeHom (DifferentialGradedAlgebra.opposite R (powAlgebra f m))
    (DifferentialGradedAlgebra.opposite R (powAlgebra f t)) (powTransition f ht htm)

/-- The left differential graded `K_m`-module `{}_mK_t`: the algebra `K_t`, with `K_m` acting
through the transition homomorphism `K_m → K_t`. Left modules are recorded as right modules over
the graded opposite algebra. -/
noncomputable def powRestrictedModule (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    DifferentialGradedModule (oppAlgebra (powAlgebra f m)) :=
  restrictScalars (oppPowTransition f ht htm) (regularModule (oppAlgebra (powAlgebra f t)))

/-- The underlying module of `{}_mK_t` is the graded opposite of `K_t`. -/
theorem powRestrictedModule_M (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (powRestrictedModule f ht htm).M = (oppAlgebra (powAlgebra f t)).A := rfl

/-- The grading of `{}_mK_t` is the grading of the graded opposite of `K_t`. -/
theorem powRestrictedModule_grading (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (powRestrictedModule f ht htm).grading = (oppAlgebra (powAlgebra f t)).grading := rfl

/-- The differential of `{}_mK_t` is the differential of the graded opposite of `K_t`. -/
theorem powRestrictedModule_d (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (powRestrictedModule f ht htm).d = (oppAlgebra (powAlgebra f t)).d := rfl

/-- The underlying `R`-module of `{}_mK_t` is `K_t`, through the identification of the graded
opposite algebra of `K_t` with `K_t`. -/
noncomputable def powRestrictedModuleEquiv (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    (powRestrictedModule f ht htm).M ≃ₗ[R] ExteriorAlgebra R (Fin r → R) :=
  (DifferentialGradedAlgebra.opposite R (powAlgebra f t)).equiv

/-- A homogeneous element of `{}_mK_t` of degree `n` corresponds to an element of degree `n`
of `K_t`. -/
theorem mem_powRestrictedModule_grading_iff (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m)
    (n : ℤ) (x : (powRestrictedModule f ht htm).M) :
    x ∈ (powRestrictedModule f ht htm).grading n ↔
      powRestrictedModuleEquiv f ht htm x ∈ (powAlgebra f t).grading n :=
  (DifferentialGradedAlgebra.opposite R (powAlgebra f t)).mem_grading_iff n x

/-- The module `{}_mK_t` as an object of the derived category `D(K_mᵒᵖᵖ, d)` of left
differential graded `K_m`-modules. -/
noncomputable def powRestrictedObject (f : Fin r → R) {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    derivedCategory' (oppAlgebra (powAlgebra f m)) :=
  (toHomotopyCategory (oppAlgebra (powAlgebra f m)) ⋙
      (quasiIsomorphisms' (oppAlgebra (powAlgebra f m))).Q).obj (powRestrictedModule f ht htm)

end RestrictedModule

end Koszul
