module

public import StacksFrontier.Algebra.DGA.CohomologicalRegrading
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulDga
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential
public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# The divided power algebra `R⟨x, z, u⟩`

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The algebra
`B_{N,t} = R⟨x, z, u⟩` is the divided power algebra on two odd generators `x` and `z` of
homological degree one and one even generator `u` of homological degree two, with differential
determined by
$$\mathrm{d}(x) = f^t, \qquad \mathrm{d}(z) = f^N, \qquad \mathrm{d}(u) = z - f^{N-t} x.$$
The last value is a cycle, since `d(z) - f^{N-t} d(x) = f^N - f^{N-t} f^t = 0`, so the
prescription really defines a differential. Read cohomologically, with the homological degree
`k` in degree `-k`, this is an object of the bundled `DifferentialGradedAlgebra` of Chapter 22,
and it is the algebra comparing the Koszul algebra `K_t` with the tensor product
`K_n ⊗_R K_t`.

## Main definitions

* `Koszul.comparisonSeq`: the pair `(f^t, f^N)` of values of the differential on `x` and `z`.
* `Koszul.comparisonExterior`: the exterior algebra `R⟨x, z⟩` on the two odd generators.
* `Koszul.comparisonCycle`: the degree-one cycle `z - f^{N-t} x` killed by `u`.
* `Koszul.comparisonAlgebra`: the algebra `B_{N,t} = R⟨x, z, u⟩` as an object of
  `DifferentialGradedAlgebra`.
* `Koszul.comparisonX`, `Koszul.comparisonZ`, `Koszul.comparisonU`: the three generators of
  `B_{N,t}`.

## Main results

* `Koszul.comparisonAlgebra_d_x`, `Koszul.comparisonAlgebra_d_z` and
  `Koszul.comparisonAlgebra_d_u`: the differential of `B_{N,t}` takes the values `f^t`, `f^N`
  and `z - f^{N-t} x` on the three generators.
* `Koszul.comparisonX_mem_grading`, `Koszul.comparisonZ_mem_grading` and
  `Koszul.comparisonU_mem_grading`: the generators `x` and `z` have cohomological degree `-1`
  and `u` has cohomological degree `-2`.

## Implementation notes

The odd part `R⟨x, z⟩` is the exterior algebra on `R²` with Koszul contraction by the functional
`x ↦ f^t`, `z ↦ f^N` as differential; the even generator is then adjoined by the divided power
polynomial construction of Tag 09PM, whose differential is `evenPolynomialDifferential`. Both
are graded by `ℕ` with a differential lowering degrees, so the bundled object is obtained from
them by the cohomological regrading `regradedDifferentialGradedAlgebra`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
-/

@[expose] public section

namespace Koszul

universe u

open scoped ExteriorAlgebra

open DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

/-- The values `f ^ t` and `f ^ N` taken by the differential of `B_{N,t}` on the two odd generators
`x` and `z`. -/
def comparisonSeq (f : R) (N t : ℕ) : Fin 2 → R
  | 0 => f ^ t
  | 1 => f ^ N

/-- The differential takes the value `f ^ t` on `x`. -/
@[simp] theorem comparisonSeq_zero (f : R) (N t : ℕ) : comparisonSeq f N t 0 = f ^ t := rfl

/-- The differential takes the value `f ^ N` on `z`. -/
@[simp] theorem comparisonSeq_one (f : R) (N t : ℕ) : comparisonSeq f N t 1 = f ^ N := rfl

/-- The odd part `R⟨x, z⟩` of `B_{N,t}`: the exterior algebra on `R²`, graded by exterior powers,
with the generators `x` and `z` in degree one. -/
abbrev comparisonExterior (R : Type u) [CommRing R] : Type u := ExteriorAlgebra R (Fin 2 → R)

/-- The odd generator `x` of `B_{N,t}`, of homological degree one, with `d x = f ^ t`. -/
noncomputable def comparisonX (R : Type u) [CommRing R] : comparisonExterior R :=
  ExteriorAlgebra.ι R (Pi.single 0 1)

/-- The odd generator `z` of `B_{N,t}`, of homological degree one, with `d z = f ^ N`. -/
noncomputable def comparisonZ (R : Type u) [CommRing R] : comparisonExterior R :=
  ExteriorAlgebra.ι R (Pi.single 1 1)

/-- The differential of `R⟨x, z⟩`: Koszul contraction by the functional `x ↦ f ^ t`,
`z ↦ f ^ N`. -/
noncomputable def comparisonExteriorDifferential (f : R) (N t : ℕ) :
    comparisonExterior R →ₗ[R] comparisonExterior R :=
  contraction (seqDual (comparisonSeq f N t))

/-- The Koszul contraction `comparisonExteriorDifferential f N t` makes the exterior algebra
`R⟨x, z⟩`, graded by exterior powers, a differential graded algebra. -/
instance isDifferentialGradedAlgebra_comparisonExteriorDifferential (f : R) (N t : ℕ) :
    IsDifferentialGradedAlgebra (exteriorGrade R (Fin 2 → R))
      (comparisonExteriorDifferential f N t) :=
  isDifferentialGradedAlgebra_contraction _

/-- The differential of `R⟨x, z⟩` sends `x` to `f ^ t`. -/
theorem comparisonExteriorDifferential_x (f : R) (N t : ℕ) :
    comparisonExteriorDifferential f N t (comparisonX R) =
      algebraMap R (comparisonExterior R) (f ^ t) := by
  simp [comparisonExteriorDifferential, comparisonX]

/-- The differential of `R⟨x, z⟩` sends `z` to `f ^ N`. -/
theorem comparisonExteriorDifferential_z (f : R) (N t : ℕ) :
    comparisonExteriorDifferential f N t (comparisonZ R) =
      algebraMap R (comparisonExterior R) (f ^ N) := by
  simp [comparisonExteriorDifferential, comparisonZ]

/-- The generator `x` lies in exterior degree one. -/
theorem comparisonX_mem (R : Type u) [CommRing R] :
    comparisonX R ∈ exteriorGrade R (Fin 2 → R) 1 :=
  ι_mem_one _

/-- The generator `z` lies in exterior degree one. -/
theorem comparisonZ_mem (R : Type u) [CommRing R] :
    comparisonZ R ∈ exteriorGrade R (Fin 2 → R) 1 :=
  ι_mem_one _

/-- The degree-one cycle `z - f^{N-t} x` of `R⟨x, z⟩`, which the even generator `u` kills. -/
noncomputable def comparisonCycle (f : R) (N t : ℕ) : comparisonExterior R :=
  comparisonZ R - f ^ (N - t) • comparisonX R

/-- The cycle `z - f^{N-t} x` lies in exterior degree one. -/
theorem comparisonCycle_mem (f : R) (N t : ℕ) :
    comparisonCycle f N t ∈ exteriorGrade R (Fin 2 → R) (2 - 1) := by
  simpa [comparisonCycle] using
    Submodule.sub_mem _ (comparisonZ_mem R) (Submodule.smul_mem _ _ (comparisonX_mem R))

/-- The prescribed value of `d u` really is a cycle: `d(z) - f^{N-t} d(x)` is
`f^N - f^{N-t} f^t = 0`. -/
theorem comparisonExteriorDifferential_comparisonCycle (f : R) {N t : ℕ} (h : t ≤ N) :
    comparisonExteriorDifferential f N t (comparisonCycle f N t) = 0 := by
  rw [comparisonCycle, map_sub, map_smul, comparisonExteriorDifferential_x,
    comparisonExteriorDifferential_z, Algebra.smul_def, ← map_mul, ← pow_add,
    show N - t + t = N from by omega, sub_self]

/-- The differential of `R⟨x, z, u⟩`, as a differential on the divided power polynomial algebra
in the even generator `u` of degree two over `R⟨x, z⟩`. -/
noncomputable def comparisonDifferential (f : R) (N t : ℕ) :
    EvenVariableAlgebra (comparisonExterior R) →ₗ[R] EvenVariableAlgebra (comparisonExterior R) :=
  evenPolynomialDifferential (exteriorGrade R (Fin 2 → R)) (comparisonExteriorDifferential f N t)
    (comparisonCycle f N t)

/-- For `t ≤ N`, `comparisonDifferential f N t` makes the divided power polynomial algebra over
`R⟨x, z⟩` in the generator `u` of degree two a differential graded algebra. -/
theorem isDifferentialGradedAlgebra_comparisonDifferential (f : R) {N t : ℕ} (h : t ≤ N) :
    IsDifferentialGradedAlgebra
      (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2)
      (comparisonDifferential f N t) :=
  have : Fact (Even 2) := ⟨even_two⟩
  evenPolynomialDifferential_isDGA (exteriorGrade R (Fin 2 → R))
    (comparisonExteriorDifferential f N t) 2 (by norm_num) (comparisonCycle f N t)
    (comparisonCycle_mem f N t) (comparisonExteriorDifferential_comparisonCycle f h)

/-- The algebra `B_{N,t} = R⟨x, z, u⟩` for `N ≥ t`: the divided power algebra on two odd
generators `x`, `z` of degree one and one even generator `u` of degree two, with `d x = f^t`,
`d z = f^N` and `d u = z - f^{N-t} x`, read cohomologically with the homological degree `k` in
degree `-k`. -/
noncomputable def comparisonAlgebra (f : R) {N t : ℕ} (h : t ≤ N) :
    DifferentialGradedAlgebra.{u, u} R :=
  letI : Fact (Even 2) := ⟨even_two⟩
  haveI := isDifferentialGradedAlgebra_comparisonDifferential f h
  regradedDifferentialGradedAlgebra (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2)
    (comparisonDifferential f N t)

/-- The underlying algebra of `B_{N,t}` is the divided power polynomial algebra over `R⟨x, z⟩`. -/
theorem comparisonAlgebra_A (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).A = EvenVariableAlgebra (comparisonExterior R) := rfl

/-- The grading of `B_{N,t}` is the cohomological regrading of its homological grading. -/
theorem comparisonAlgebra_grading (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).grading =
      cohomologicalGrade (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) := rfl

/-- The differential of `B_{N,t}` is `comparisonDifferential f N t`. -/
theorem comparisonAlgebra_d (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).d = comparisonDifferential f N t := rfl

/-- The inclusion of the odd part `R⟨x, z⟩` into `B_{N,t}`. -/
noncomputable def comparisonInclusion (R : Type u) [CommRing R] :
    comparisonExterior R →ₐ[R] EvenVariableAlgebra (comparisonExterior R) :=
  EvenVariableAlgebra.coeffAlgHom

/-- The even generator `u` of `B_{N,t}`, of homological degree two, with `d u = z - f^{N-t} x`. -/
noncomputable def comparisonU (R : Type u) [CommRing R] :
    EvenVariableAlgebra (comparisonExterior R) :=
  EvenVariableAlgebra.monomial 1 1

/-- The differential of `B_{N,t}` restricts on `R⟨x, z⟩` to the differential of `R⟨x, z⟩`. -/
theorem comparisonDifferential_inclusion (f : R) (N t : ℕ) (a : comparisonExterior R) :
    comparisonDifferential f N t (comparisonInclusion R a) =
      comparisonInclusion R (comparisonExteriorDifferential f N t a) := by
  have h := evenPolynomialDifferential_monomial (exteriorGrade R (Fin 2 → R))
    (comparisonExteriorDifferential f N t) (comparisonCycle f N t) 0 a
  simpa [comparisonDifferential, comparisonInclusion, EvenVariableAlgebra.coeffAlgHom,
    EvenVariableAlgebra.coeffEmbedding] using h

/-- The differential of `B_{N,t}` sends the even generator `u` to the cycle `z - f^{N-t} x`. -/
theorem comparisonDifferential_u (f : R) (N t : ℕ) :
    comparisonDifferential f N t (comparisonU R) =
      comparisonInclusion R (comparisonCycle f N t) := by
  have h := evenPolynomialDifferential_monomial (exteriorGrade R (Fin 2 → R))
    (comparisonExteriorDifferential f N t) (comparisonCycle f N t) 1 1
  have hone : comparisonExteriorDifferential f N t 1 = 0 := by
    simp [comparisonExteriorDifferential]
  have hsign : signRingHom (exteriorGrade R (Fin 2 → R)) 1 (1 : comparisonExterior R) = 1 := by
    rw [signRingHom_of_mem (exteriorGrade R (Fin 2 → R)) 1 0
      (SetLike.one_mem_graded (exteriorGrade R (Fin 2 → R)))]
    simp
  rw [comparisonU, comparisonDifferential, h, hone, hsign, one_mul]
  simp [comparisonInclusion, EvenVariableAlgebra.coeffAlgHom, EvenVariableAlgebra.coeffEmbedding]

/-- If the differential of `R⟨x, z⟩` sends `a` to the constant `c`, so does that of `B_{N,t}`
on the image of `a`. -/
private theorem comparisonAlgebra_d_inclusion_of_eq (f : R) {N t : ℕ} (h : t ≤ N)
    {a : comparisonExterior R} {c : R}
    (ha : comparisonExteriorDifferential f N t a = algebraMap R (comparisonExterior R) c) :
    (comparisonAlgebra f h).d (comparisonInclusion R a) =
      algebraMap R (EvenVariableAlgebra (comparisonExterior R)) c := by
  change comparisonDifferential f N t (comparisonInclusion R a) = _
  rw [comparisonDifferential_inclusion, ha]
  exact (comparisonInclusion R).commutes _

/-- The differential of `B_{N,t}` sends the odd generator `x` to `f ^ t`. -/
theorem comparisonAlgebra_d_x (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).d (comparisonInclusion R (comparisonX R)) =
      algebraMap R (EvenVariableAlgebra (comparisonExterior R)) (f ^ t) :=
  comparisonAlgebra_d_inclusion_of_eq f h (comparisonExteriorDifferential_x f N t)

/-- The differential of `B_{N,t}` sends the odd generator `z` to `f ^ N`. -/
theorem comparisonAlgebra_d_z (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).d (comparisonInclusion R (comparisonZ R)) =
      algebraMap R (EvenVariableAlgebra (comparisonExterior R)) (f ^ N) :=
  comparisonAlgebra_d_inclusion_of_eq f h (comparisonExteriorDifferential_z f N t)

/-- The differential of `B_{N,t}` sends the even generator `u` to `z - f^{N-t} x`. -/
theorem comparisonAlgebra_d_u (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).d (comparisonU R) =
      comparisonInclusion R (comparisonZ R) -
        f ^ (N - t) • comparisonInclusion R (comparisonX R) := by
  change comparisonDifferential f N t (comparisonU R) = _
  rw [comparisonDifferential_u, comparisonCycle, map_sub, map_smul]

/-- The image in `B_{N,t}` of an element of exterior degree one has cohomological degree `-1`. -/
private theorem comparisonInclusion_mem_grading (f : R) {N t : ℕ} (h : t ≤ N)
    {a : comparisonExterior R} (ha : a ∈ exteriorGrade R (Fin 2 → R) 1) :
    comparisonInclusion R a ∈ (comparisonAlgebra f h).grading (-1) := by
  rw [comparisonAlgebra_grading, show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    cohomologicalGrade_neg_natCast]
  exact (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff _ 2 1 _).2 ha

/-- The odd generator `x` has cohomological degree `-1`. -/
theorem comparisonX_mem_grading (f : R) {N t : ℕ} (h : t ≤ N) :
    comparisonInclusion R (comparisonX R) ∈ (comparisonAlgebra f h).grading (-1) :=
  comparisonInclusion_mem_grading f h (comparisonX_mem R)

/-- The odd generator `z` has cohomological degree `-1`. -/
theorem comparisonZ_mem_grading (f : R) {N t : ℕ} (h : t ≤ N) :
    comparisonInclusion R (comparisonZ R) ∈ (comparisonAlgebra f h).grading (-1) :=
  comparisonInclusion_mem_grading f h (comparisonZ_mem R)

/-- The even generator `u` has cohomological degree `-2`. -/
theorem comparisonU_mem_grading (f : R) {N t : ℕ} (h : t ≤ N) :
    comparisonU R ∈ (comparisonAlgebra f h).grading (-2) := by
  rw [comparisonAlgebra_grading, show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
    cohomologicalGrade_neg_natCast]
  have h2 := EvenVariableAlgebra.monomial_mem_grade (exteriorGrade R (Fin 2 → R)) 2 1 0
    (SetLike.one_mem_graded (exteriorGrade R (Fin 2 → R)))
  rw [show 0 + 1 * 2 = 2 from by norm_num] at h2
  exact h2

end Koszul
