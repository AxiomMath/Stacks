module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulTransition
public import StacksFrontier.RingTheory.Koszul.CohomologicalDifferentialGradedAlgebra
public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebra

/-!
# The map from `R⟨x, z, u⟩` to the Koszul algebra of one element

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The algebra
`B_{N,t} = R⟨x, z, u⟩` of `Koszul.comparisonAlgebra` maps to the one-variable Koszul algebra
`K_t = R⟨x⟩` of `f ^ t` by
$$x \longmapsto x, \qquad z \longmapsto f^{N-t} x, \qquad u \longmapsto 0 .$$
This is a homomorphism of differential graded algebras: on the odd part it is induced by the
linear map `R² → R` with matrix `(1, f^{N-t})`, which pulls the Koszul functional `x ↦ f^t`
back to the functional `x ↦ f^t`, `z ↦ f^N` defining the differential of `R⟨x, z⟩`; and the even
generator may be sent to zero because the element `z - f^{N-t} x` it kills already maps to zero.

## Main definitions

* `Koszul.comparisonProj`: the linear map `R² → R` with matrix `(1, f^{N-t})`.
* `Koszul.comparisonExteriorMap`: the induced map `R⟨x, z⟩ → R⟨x⟩` of exterior algebras.
* `Koszul.comparisonToKoszul`: the homomorphism `B_{N,t} → K_t` of differential graded algebras.

## Main results

* `Koszul.seqDual_comp_comparisonProj`: the functional `x ↦ f^t` on `R` pulls back to the
  functional of `R⟨x, z⟩`.
* `Koszul.comparisonExteriorMap_comparisonCycle`: the cycle `z - f^{N-t} x` maps to zero.
* `Koszul.comparisonAlgHom_comp_differential`: the map commutes with the two differentials.
* `Koszul.comparisonToKoszul_x`, `Koszul.comparisonToKoszul_z` and
  `Koszul.comparisonToKoszul_u`: the values of the homomorphism on the three generators.

## Implementation notes

The homomorphism out of the even-variable divided power extension is the one supplied by the
universal property of Tag 09PI, applied with the adjoined variable sent to `0`; all positive
divided powers of `0` then vanish, so only the coefficient of `u⁽⁰⁾` survives. Compatibility with
the differentials is checked on the divided power monomials `a u⁽ⁿ⁾`, where it reduces to the
compatibility on the odd part for `n = 0`, to the vanishing of the image of `z - f^{N-t} x` for
`n = 1`, and to the vanishing of the positive divided powers of `0` for `n ≥ 2`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
-/

@[expose] public section

namespace Koszul

universe u

open scoped ExteriorAlgebra

open DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

/-- The linear map `R² → R` with matrix `(1, f^{N-t})`: it sends the generator `x` to `x` and
the generator `z` to `f^{N-t} x`. -/
def comparisonProj (f : R) (N t : ℕ) : (Fin 2 → R) →ₗ[R] (Fin 1 → R) where
  toFun v := fun _ => v 0 + f ^ (N - t) * v 1
  map_add' v w := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The coordinate formula for `comparisonProj`: it sends `v` to `v 0 + f^{N-t} v 1`. -/
@[simp] theorem comparisonProj_apply (f : R) (N t : ℕ) (v : Fin 2 → R) (i : Fin 1) :
    comparisonProj f N t v i = v 0 + f ^ (N - t) * v 1 := rfl

/-- The functional `x ↦ f^t` on `R` pulls back along `comparisonProj` to the functional
`x ↦ f^t`, `z ↦ f^N` whose contraction is the differential of `R⟨x, z⟩`. -/
theorem seqDual_comp_comparisonProj (f : R) {N t : ℕ} (h : t ≤ N) :
    (seqDual fun _ : Fin 1 => f ^ t) ∘ₗ comparisonProj f N t =
      seqDual (comparisonSeq f N t) := by
  have hf : f ^ (N - t) * f ^ t = f ^ N := by
    rw [← pow_add, show N - t + t = N from by omega]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, seqDual_apply, seqDual_apply, Fin.sum_univ_one, Fin.sum_univ_two,
    comparisonProj_apply, comparisonSeq_zero, comparisonSeq_one, ← hf]
  ring

/-- The map `R⟨x, z⟩ → R⟨x⟩` of exterior algebras induced by `comparisonProj`. -/
noncomputable def comparisonExteriorMap (f : R) (N t : ℕ) :
    comparisonExterior R →ₐ[R] ExteriorAlgebra R (Fin 1 → R) :=
  ExteriorAlgebra.map (comparisonProj f N t)

/-- The map `R⟨x, z⟩ → R⟨x⟩` sends `x` to the generator of `R⟨x⟩`. -/
theorem comparisonExteriorMap_x (f : R) (N t : ℕ) :
    comparisonExteriorMap f N t (comparisonX R) =
      ExteriorAlgebra.ι R (fun _ => 1) := by
  rw [comparisonExteriorMap, comparisonX, ExteriorAlgebra.map_apply_ι]
  congr 1
  funext i
  simp

/-- The map `R⟨x, z⟩ → R⟨x⟩` sends `z` to `f^{N-t}` times the generator of `R⟨x⟩`. -/
theorem comparisonExteriorMap_z (f : R) (N t : ℕ) :
    comparisonExteriorMap f N t (comparisonZ R) =
      f ^ (N - t) • ExteriorAlgebra.ι R (fun _ => 1) := by
  rw [comparisonExteriorMap, comparisonZ, ExteriorAlgebra.map_apply_ι, ← map_smul]
  congr 1
  funext i
  simp

/-- The map `R⟨x, z⟩ → R⟨x⟩` sends the cycle `z - f^{N-t} x` to zero. -/
theorem comparisonExteriorMap_comparisonCycle (f : R) (N t : ℕ) :
    comparisonExteriorMap f N t (comparisonCycle f N t) = 0 := by
  rw [comparisonCycle, map_sub, map_smul, comparisonExteriorMap_x, comparisonExteriorMap_z,
    sub_self]

/-- The map of exterior algebras commutes with the two Koszul differentials. -/
theorem comparisonExteriorMap_comp_differential (f : R) {N t : ℕ} (h : t ≤ N)
    (a : comparisonExterior R) :
    comparisonExteriorMap f N t (comparisonExteriorDifferential f N t a) =
      contraction (seqDual fun _ : Fin 1 => f ^ t) (comparisonExteriorMap f N t a) := by
  rw [comparisonExteriorDifferential, comparisonExteriorMap, ← seqDual_comp_comparisonProj f h]
  exact (contractLeft_exteriorAlgebraMap (comparisonProj f N t)
    (seqDual fun _ : Fin 1 => f ^ t) a).symm

/-- The map `R⟨x, z⟩ → R⟨x⟩` sends the `m`th exterior power into the `m`th exterior power. -/
theorem comparisonExteriorMap_mem (f : R) (N t m : ℕ) {a : comparisonExterior R}
    (ha : a ∈ exteriorGrade R (Fin 2 → R) m) :
    comparisonExteriorMap f N t a ∈ exteriorGrade R (Fin 1 → R) m :=
  ExteriorAlgebra.map_mem_exteriorPower (comparisonProj f N t) ha

/-- The ring homomorphism `B_{N,t} → K_t` sending `u` to zero: on `a u⁽ⁿ⁾` it is the image of `a`
times the `n`th divided power of `0`. -/
noncomputable def comparisonLift (f : R) (N t : ℕ) :
    EvenVariableAlgebra (comparisonExterior R) →+* ExteriorAlgebra R (Fin 1 → R) :=
  evenLift (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 1 → R)) 2 (by norm_num) even_two
    (comparisonExteriorMap f N t).toRingHom
    (fun m _ ha => comparisonExteriorMap_mem f N t m ha)
    (exteriorDividedPowerStructure R 1) 0 (Submodule.zero_mem _)

/-- The image of `a u⁽ⁿ⁾` is the image of `a` times the `n`th divided power of `0`. -/
theorem comparisonLift_monomial (f : R) (N t n : ℕ) (a : comparisonExterior R) :
    comparisonLift f N t (EvenVariableAlgebra.monomial n a) =
      comparisonExteriorMap f N t a * (exteriorDividedPowerStructure R 1).dpow n 0 :=
  evenLift_monomial (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 1 → R)) 2 (by norm_num)
    even_two _ _ _ 0 (Submodule.zero_mem _) n a

/-- The image of `a u⁽⁰⁾` is the image of `a` in `R⟨x⟩`. -/
theorem comparisonLift_monomial_zero (f : R) (N t : ℕ) (a : comparisonExterior R) :
    comparisonLift f N t (EvenVariableAlgebra.monomial 0 a) = comparisonExteriorMap f N t a := by
  rw [comparisonLift_monomial,
    (exteriorDividedPowerStructure R 1).dpow_zero (Submodule.zero_mem _), mul_one]

/-- The image of `a u⁽ⁿ⁺¹⁾` is zero. -/
theorem comparisonLift_monomial_succ (f : R) (N t n : ℕ) (a : comparisonExterior R) :
    comparisonLift f N t (EvenVariableAlgebra.monomial (n + 1) a) = 0 := by
  rw [comparisonLift_monomial,
    (exteriorDividedPowerStructure R 1).dpow_zero_eq_zero (Nat.succ_ne_zero n), mul_zero]

/-- Every divided power monomial with the cycle `z - f^{N-t} x` as a factor maps to zero. -/
theorem comparisonLift_monomial_comparisonCycle (f : R) (N t n : ℕ)
    (b : comparisonExterior R) :
    comparisonLift f N t
        (EvenVariableAlgebra.monomial n (b * comparisonCycle f N t)) = 0 := by
  match n with
  | 0 =>
    rw [comparisonLift_monomial_zero, map_mul, comparisonExteriorMap_comparisonCycle, mul_zero]
  | (k + 1) => rw [comparisonLift_monomial_succ]

/-- On the coefficient algebra `R⟨x, z⟩`, the map `B_{N,t} → K_t` is `comparisonExteriorMap`. -/
theorem comparisonLift_coeffEmbedding (f : R) (N t : ℕ) (a : comparisonExterior R) :
    comparisonLift f N t (EvenVariableAlgebra.coeffEmbedding a) =
      comparisonExteriorMap f N t a := by
  rw [EvenVariableAlgebra.coeffEmbedding_apply, comparisonLift_monomial_zero]

/-- The map `B_{N,t} → K_t` sends the elements of degree `m` into the `m`th exterior power. -/
theorem comparisonLift_mem (f : R) (N t m : ℕ) {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2 m) :
    comparisonLift f N t x ∈ exteriorGrade R (Fin 1 → R) m :=
  evenLift_mem_grade (exteriorGrade R (Fin 2 → R)) (exteriorGrade R (Fin 1 → R)) 2 (by norm_num)
    even_two _ _ _ 0 (Submodule.zero_mem _) m x hx

/-- The map `B_{N,t} → K_t` preserves the cohomological grading. -/
theorem comparisonLift_mem_grading (f : R) (N t : ℕ) (n : ℤ)
    {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ cohomologicalGrade (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n) :
    comparisonLift f N t x ∈ cohomologicalExteriorGrade R (Fin 1 → R) n := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalGrade_neg_natCast] at hx
    rw [cohomologicalExteriorGrade_neg_natCast]
    exact comparisonLift_mem f N t k hx
  · have h0 : x = 0 := eq_zero_of_mem_cohomologicalGrade_of_pos _ (by omega) hx
    rw [h0, map_zero]
    exact Submodule.zero_mem _

/-- The ring homomorphism `B_{N,t} → K_t` is a homomorphism of `R`-algebras. -/
noncomputable def comparisonAlgHom (f : R) (N t : ℕ) :
    EvenVariableAlgebra (comparisonExterior R) →ₐ[R] ExteriorAlgebra R (Fin 1 → R) :=
  { comparisonLift f N t with
    commutes' := fun r => by
      have h : algebraMap R (EvenVariableAlgebra (comparisonExterior R)) r =
          EvenVariableAlgebra.coeffEmbedding (algebraMap R (comparisonExterior R) r) := rfl
      change comparisonLift f N t (algebraMap R _ r) = _
      rw [h, comparisonLift_coeffEmbedding]
      exact (comparisonExteriorMap f N t).commutes r }

/-- The underlying ring homomorphism of `comparisonAlgHom` is `comparisonLift`. -/
theorem comparisonAlgHom_apply (f : R) (N t : ℕ)
    (x : EvenVariableAlgebra (comparisonExterior R)) :
    comparisonAlgHom f N t x = comparisonLift f N t x := rfl

/-- The map `B_{N,t} → K_t` commutes with the differentials. -/
theorem comparisonAlgHom_comp_differential (f : R) {N t : ℕ} (h : t ≤ N)
    (x : EvenVariableAlgebra (comparisonExterior R)) :
    comparisonAlgHom f N t (comparisonDifferential f N t x) =
      contraction (seqDual fun _ : Fin 1 => f ^ t) (comparisonAlgHom f N t x) := by
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add n a y hy =>
    rw [map_add, map_add, map_add, map_add, hy]
    congr 1
    rw [comparisonDifferential, evenPolynomialDifferential_monomial]
    split_ifs with hc
    · subst hc
      rw [add_zero, comparisonAlgHom_apply, comparisonAlgHom_apply,
        comparisonLift_monomial_zero, comparisonLift_monomial_zero]
      exact comparisonExteriorMap_comp_differential f h a
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
      rw [comparisonAlgHom_apply, comparisonAlgHom_apply, map_add,
        comparisonLift_monomial_succ, comparisonLift_monomial_comparisonCycle,
        comparisonLift_monomial_succ, map_zero, add_zero]

/-- The homomorphism `B_{N,t} → K_t` of differential graded algebras sending `x` to `x`, `z` to
`f^{N-t} x` and `u` to `0`. -/
noncomputable def comparisonToKoszul (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonAlgebra f h).Hom (powAlgebra (fun _ : Fin 1 => f) t) where
  toAlgebraHom := comparisonAlgHom f N t
  map_grading := by
    intro n a ha
    rw [comparisonAlgebra_grading] at ha
    exact comparisonLift_mem_grading f N t n ha
  map_d := fun a => comparisonAlgHom_comp_differential f h a

/-- The homomorphism `B_{N,t} → K_t` restricts to `comparisonExteriorMap` on `R⟨x, z⟩`. -/
private theorem comparisonToKoszul_inclusion (f : R) {N t : ℕ} (h : t ≤ N)
    (a : comparisonExterior R) :
    (comparisonToKoszul f h).toAlgebraHom (comparisonInclusion R a) =
      comparisonExteriorMap f N t a :=
  comparisonLift_coeffEmbedding f N t a

/-- The homomorphism `B_{N,t} → K_t` sends `x` to the generator of `K_t`. -/
theorem comparisonToKoszul_x (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonToKoszul f h).toAlgebraHom (comparisonInclusion R (comparisonX R)) =
      ExteriorAlgebra.ι R (fun _ => 1) :=
  (comparisonToKoszul_inclusion f h _).trans (comparisonExteriorMap_x f N t)

/-- The homomorphism `B_{N,t} → K_t` sends `z` to `f^{N-t}` times the generator of `K_t`. -/
theorem comparisonToKoszul_z (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonToKoszul f h).toAlgebraHom (comparisonInclusion R (comparisonZ R)) =
      f ^ (N - t) • ExteriorAlgebra.ι R (fun _ => 1) := by
  rw [comparisonToKoszul_inclusion, comparisonExteriorMap_z]
  rfl

/-- The homomorphism `B_{N,t} → K_t` sends the even generator `u` to zero. -/
theorem comparisonToKoszul_u (f : R) {N t : ℕ} (h : t ≤ N) :
    (comparisonToKoszul f h).toAlgebraHom (comparisonU R) = 0 := by
  change comparisonLift f N t (EvenVariableAlgebra.monomial 1 1) = 0
  exact comparisonLift_monomial_succ f N t 0 1

/-- The linear map `R → R²` onto the first coordinate, which sends the generator of `K_t` to
the odd generator `x` of `B_{N,t}`. -/
def comparisonXInclusion (R : Type u) [CommRing R] : (Fin 1 → R) →ₗ[R] (Fin 2 → R) :=
  (LinearMap.single R (fun _ : Fin 2 => R) 0).comp (LinearMap.proj 0)

/-- `comparisonXInclusion` sends `v` to `Pi.single 0 (v 0)`. -/
@[simp] theorem comparisonXInclusion_apply (v : Fin 1 → R) :
    comparisonXInclusion R v = Pi.single 0 (v 0) := rfl

/-- The functional `x ↦ f^t`, `z ↦ f^N` of `R⟨x, z⟩` pulls back along `comparisonXInclusion` to
the functional `x ↦ f^t` whose contraction is the differential of `K_t`. -/
theorem seqDual_comp_comparisonXInclusion (f : R) (N t : ℕ) :
    seqDual (comparisonSeq f N t) ∘ₗ comparisonXInclusion R =
      seqDual fun _ : Fin 1 => f ^ t := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, comparisonXInclusion_apply, seqDual_apply_single, comparisonSeq_zero,
    seqDual_apply, Fin.sum_univ_one]

end Koszul
