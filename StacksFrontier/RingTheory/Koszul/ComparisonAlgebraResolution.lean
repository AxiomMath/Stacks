module

public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraMap
public import StacksFrontier.RingTheory.Koszul.Semilinear

/-!
# `R⟨x, z, u⟩` resolves the Koszul algebra of one element

Let `f` be an element of a commutative ring `R` and let `N ≥ t ≥ 1`. The comparison homomorphism
`B_{N,t} = R⟨x, z, u⟩ → K_t = R⟨x⟩` of `Koszul.comparisonToKoszul` is a quasi-isomorphism: it has
an `R`-linear section, and the composite of the section with it is homotopic to the identity of
`B_{N,t}`.

Both the section and the homotopy are explicit. In the basis `x`, `z' = z - f^{N-t} x` of the odd
part the differential satisfies `d(x) = f^t`, `d(z') = 0` and `d(u) = z'`, so `B_{N,t}` is the
Koszul algebra `R⟨x⟩` tensored with the acyclic algebra `R⟨z', u⟩`. The section is the inclusion
`R⟨x⟩ → B_{N,t}`, and the homotopy sends `a u⁽ⁿ⁾` to `-(z'⌟a) u⁽ⁿ⁺¹⁾`, where `z'⌟` is contraction
with the functional dual to `z'`.

## Main definitions

* `Koszul.comparisonCycleVector` and `Koszul.comparisonDualZ`: the vector `z - f^{N-t} x` of `R²`
  and the functional dual to it in the basis `x`, `z - f^{N-t} x`.
* `Koszul.comparisonContraction`: contraction of `R⟨x, z⟩` with that functional.
* `Koszul.comparisonProjector`: the projection of `R⟨x, z⟩` onto `R⟨x⟩` killing `z - f^{N-t} x`.
* `Koszul.comparisonSectionMap`: the section `K_t → B_{N,t}` of the comparison homomorphism.
* `Koszul.comparisonHomotopy`: the homotopy operator of `B_{N,t}`.

## Main results

* `Koszul.sub_comparisonProjector`: every element of `R⟨x, z⟩` is its projection to `R⟨x⟩` plus
  `z - f^{N-t} x` times its contraction.
* `Koszul.comparisonAlgHom_comparisonSectionMap`: the section is a right inverse of the
  comparison homomorphism.
* `Koszul.comparisonHomotopy_eq`: the homotopy identity
  `η ∘ ε - 1 = d ∘ H + H ∘ d` on `B_{N,t}`.
* `Koszul.exists_cycle_comparisonToKoszul` and `Koszul.exists_primitive_of_comparisonToKoszul`:
  the comparison homomorphism is surjective on cohomology and injective on it, so it is a
  quasi-isomorphism.

## Implementation notes

The computation is carried out on the divided power monomials `a u⁽ⁿ⁾` with `a` homogeneous for
the exterior grading, and extended to all of `B_{N,t}` by linearity; homogeneity of `a` is needed
because the differential of `B_{N,t}` involves the grading sign of `a`.

Only three facts about the odd part are used, each a consequence of the contraction calculus of
`CliffordAlgebra.contractLeft`: contraction with two functionals anticommutes, so the contraction
anticommutes with the Koszul differential; contraction with the functional dual to
`z - f^{N-t} x` takes the value one on that element; and the grading sign moves a homogeneous
element past `z - f^{N-t} x`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
-/

@[expose] public section

namespace Koszul

universe u v

open scoped ExteriorAlgebra

open DividedPowers.TateResolution

section Contraction

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

end Contraction

section Vectors

variable {R : Type u} [CommRing R]

/-- The vector `z - f^{N-t} x` of `R²`, whose wedge generator is the cycle killed by `u`. -/
def comparisonCycleVector (f : R) (N t : ℕ) : Fin 2 → R :=
  Pi.single 1 1 - f ^ (N - t) • Pi.single 0 1

/-- The cycle `z - f^{N-t} x` of `R⟨x, z⟩` is the image of `comparisonCycleVector` under `ι`. -/
theorem comparisonCycle_eq_ι (f : R) (N t : ℕ) :
    comparisonCycle f N t = ExteriorAlgebra.ι R (comparisonCycleVector f N t) := by
  rw [comparisonCycleVector, map_sub, map_smul]
  rfl

/-- The functional on `R²` dual to `z - f^{N-t} x` in the basis `x`, `z - f^{N-t} x`. -/
noncomputable def comparisonDualZ (R : Type u) [CommRing R] : Module.Dual R (Fin 2 → R) :=
  seqDual (Pi.single 1 1)

/-- The functional `comparisonDualZ` takes a vector to its second coordinate. -/
theorem comparisonDualZ_apply (v : Fin 2 → R) : comparisonDualZ R v = v 1 := by
  rw [comparisonDualZ, seqDual_apply, Fin.sum_univ_two]
  simp

/-- The functional `comparisonDualZ` takes the value one on `z - f^{N-t} x`. -/
@[simp] theorem comparisonDualZ_comparisonCycleVector (f : R) (N t : ℕ) :
    comparisonDualZ R (comparisonCycleVector f N t) = 1 := by
  rw [comparisonDualZ_apply, comparisonCycleVector]
  simp

/-- The projection `R² → R` is a left inverse of the inclusion `R → R²` of `x`. -/
theorem comparisonProj_comp_comparisonXInclusion (f : R) (N t : ℕ) :
    (comparisonProj f N t).comp (comparisonXInclusion R) = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun i => ?_
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rw [LinearMap.comp_apply, comparisonProj_apply, comparisonXInclusion_apply]
  simp

/-- The idempotent of `R²` projecting onto `x` and killing `z - f^{N-t} x`. -/
def comparisonProjVector (f : R) (N t : ℕ) : (Fin 2 → R) →ₗ[R] (Fin 2 → R) :=
  (comparisonXInclusion R).comp (comparisonProj f N t)

/-- Every vector of `R²` is its projection onto `x` plus its `comparisonDualZ`-coordinate times
`z - f^{N-t} x`. -/
theorem comparisonProjVector_add_smul (f : R) (N t : ℕ) (v : Fin 2 → R) :
    comparisonProjVector f N t v + comparisonDualZ R v • comparisonCycleVector f N t = v := by
  refine funext fun i => ?_
  rw [comparisonDualZ_apply, comparisonProjVector, LinearMap.comp_apply,
    comparisonXInclusion_apply, comparisonCycleVector]
  fin_cases i
  · simp
    ring
  · simp

end Vectors

section Projector

variable {R : Type u} [CommRing R]

/-- Contraction of `R⟨x, z⟩` with the functional dual to `z - f^{N-t} x`. -/
noncomputable def comparisonContraction (R : Type u) [CommRing R] :
    comparisonExterior R →ₗ[R] comparisonExterior R :=
  contraction (comparisonDualZ R)

/-- The projection of `R⟨x, z⟩` onto `R⟨x⟩`, killing `z - f^{N-t} x`. It is the composite of the
comparison map `R⟨x, z⟩ → R⟨x⟩` with its section. -/
noncomputable def comparisonProjector (f : R) (N t : ℕ) :
    comparisonExterior R →ₐ[R] comparisonExterior R :=
  ExteriorAlgebra.map (comparisonProjVector f N t)

/-- The projector is the comparison map `R⟨x, z⟩ → R⟨x⟩` followed by the inclusion
`R⟨x⟩ → R⟨x, z⟩`. -/
theorem comparisonProjector_eq (f : R) (N t : ℕ) (a : comparisonExterior R) :
    comparisonProjector f N t a =
      ExteriorAlgebra.map (comparisonXInclusion R) (comparisonExteriorMap f N t a) := by
  rw [comparisonProjector, comparisonProjVector, ← ExteriorAlgebra.map_comp_map,
    comparisonExteriorMap]
  rfl

/-- Every element of `R⟨x, z⟩` is its projection to `R⟨x⟩` plus `z - f^{N-t} x` times its
contraction. -/
theorem sub_comparisonProjector (f : R) (N t : ℕ) (a : comparisonExterior R) :
    a - comparisonProjector f N t a =
      comparisonCycle f N t * comparisonContraction R a := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [comparisonProjector, AlgHom.commutes, sub_self, comparisonContraction,
        CliffordAlgebra.contractLeft_algebraMap, mul_zero]
  | add x y hx hy =>
      have hA : comparisonProjector f N t (x + y) =
          comparisonProjector f N t x + comparisonProjector f N t y := by simp
      have hB : comparisonContraction R (x + y) =
          comparisonContraction R x + comparisonContraction R y := by simp
      rw [hA, hB, mul_add, ← hx, ← hy]
      abel
  | ι_mul x m hx =>
      have hm : ExteriorAlgebra.ι R m =
          ExteriorAlgebra.ι R (comparisonProjVector f N t m) +
            comparisonDualZ R m • comparisonCycle f N t := by
        rw [comparisonCycle_eq_ι, ← map_smul, ← map_add, comparisonProjVector_add_smul]
      have hsq : comparisonCycle f N t * comparisonCycle f N t = 0 := by
        rw [comparisonCycle_eq_ι]
        exact ExteriorAlgebra.ι_sq_zero _
      have hswap : comparisonCycle f N t * ExteriorAlgebra.ι R (comparisonProjVector f N t m) =
          -(ExteriorAlgebra.ι R (comparisonProjVector f N t m) * comparisonCycle f N t) := by
        rw [comparisonCycle_eq_ι, eq_neg_iff_add_eq_zero, add_comm]
        exact ExteriorAlgebra.ι_add_mul_swap _ _
      have hcontract : comparisonContraction R (ExteriorAlgebra.ι R m * x) =
          comparisonDualZ R m • x - ExteriorAlgebra.ι R m * comparisonContraction R x :=
        CliffordAlgebra.contractLeft_ι_mul _ _ _
      have h1 : comparisonCycle f N t * (comparisonDualZ R m • (comparisonCycle f N t *
          comparisonContraction R x)) = 0 := by
        rw [mul_smul_comm, ← mul_assoc, hsq, zero_mul, smul_zero]
      have h2 : comparisonCycle f N t * (ExteriorAlgebra.ι R (comparisonProjVector f N t m) *
          comparisonContraction R x) =
          -(ExteriorAlgebra.ι R (comparisonProjVector f N t m) * x) +
            ExteriorAlgebra.ι R (comparisonProjVector f N t m) *
              comparisonProjector f N t x := by
        rw [← mul_assoc, hswap, neg_mul, mul_assoc, ← hx, mul_sub]
        abel
      have hP : comparisonProjector f N t (ExteriorAlgebra.ι R m * x) =
          ExteriorAlgebra.ι R (comparisonProjVector f N t m) *
            comparisonProjector f N t x := by
        rw [comparisonProjector, map_mul, ExteriorAlgebra.map_apply_ι]
      rw [hP, hcontract, mul_sub, mul_smul_comm, hm, add_mul, smul_mul_assoc, add_mul,
        smul_mul_assoc, mul_add, h1, h2]
      abel

end Projector

section Homotopy

variable {R : Type u} [CommRing R]

/-- The coefficients of a divided power polynomial in `u`, as an `R`-linear map. -/
def comparisonCoeff (R : Type u) [CommRing R] :
    EvenVariableAlgebra (comparisonExterior R) →ₗ[R] (ℕ →₀ comparisonExterior R) where
  toFun x := x.coeff
  map_add' := EvenVariableAlgebra.coeff_add
  map_smul' := EvenVariableAlgebra.coeff_smul

/-- The homotopy operator of `B_{N,t}`: contract with the functional dual to `z - f^{N-t} x`,
change sign, and raise the divided power index of `u` by one. -/
noncomputable def comparisonHomotopy (R : Type u) [CommRing R] :
    EvenVariableAlgebra (comparisonExterior R) →ₗ[R]
      EvenVariableAlgebra (comparisonExterior R) :=
  (Finsupp.lsum R fun n =>
    (EvenVariableAlgebra.monomialLinearMap (R := R) (n + 1)).comp
      (-comparisonContraction R)).comp (comparisonCoeff R)

/-- The homotopy operator sends `a u⁽ⁿ⁾` to `-(z'⌟a) u⁽ⁿ⁺¹⁾`. -/
@[simp] theorem comparisonHomotopy_monomial (n : ℕ) (a : comparisonExterior R) :
    comparisonHomotopy R (EvenVariableAlgebra.monomial n a) =
      EvenVariableAlgebra.monomial (n + 1) (-comparisonContraction R a) := by
  rw [comparisonHomotopy, LinearMap.comp_apply]
  rw [show comparisonCoeff R (EvenVariableAlgebra.monomial n a) = Finsupp.single n a from rfl]
  rw [Finsupp.lsum_single]
  rfl

/-- The section `K_t → B_{N,t}` of the comparison homomorphism: the generator of `K_t` goes to
`x`, in divided power degree zero. -/
noncomputable def comparisonSectionMap (R : Type u) [CommRing R] :
    ExteriorAlgebra R (Fin 1 → R) →ₗ[R] EvenVariableAlgebra (comparisonExterior R) :=
  (EvenVariableAlgebra.monomialLinearMap (R := R) 0).comp
    (ExteriorAlgebra.map (comparisonXInclusion R)).toLinearMap

/-- The section sends `y` to its image in `R⟨x, z⟩`, in divided power degree zero. -/
theorem comparisonSectionMap_apply (y : ExteriorAlgebra R (Fin 1 → R)) :
    comparisonSectionMap R y =
      EvenVariableAlgebra.monomial 0 (ExteriorAlgebra.map (comparisonXInclusion R) y) := rfl

/-- The section is a right inverse of the comparison homomorphism `B_{N,t} → K_t`. -/
theorem comparisonAlgHom_comparisonSectionMap (f : R) (N t : ℕ)
    (y : ExteriorAlgebra R (Fin 1 → R)) :
    comparisonAlgHom f N t (comparisonSectionMap R y) = y := by
  rw [comparisonSectionMap_apply, comparisonAlgHom_apply, comparisonLift_monomial_zero,
    comparisonExteriorMap, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    comparisonProj_comp_comparisonXInclusion, ExteriorAlgebra.map_id, AlgHom.id_apply]

/-- On divided power degree zero the section composed with the comparison homomorphism is the
projector. -/
theorem comparisonSectionMap_comparisonAlgHom_monomial_zero (f : R) (N t : ℕ)
    (a : comparisonExterior R) :
    comparisonSectionMap R (comparisonAlgHom f N t (EvenVariableAlgebra.monomial 0 a)) =
      EvenVariableAlgebra.monomial 0 (comparisonProjector f N t a) := by
  rw [comparisonAlgHom_apply, comparisonLift_monomial_zero, comparisonSectionMap_apply,
    comparisonProjector_eq]

/-- In positive divided power degree the comparison homomorphism vanishes. -/
theorem comparisonSectionMap_comparisonAlgHom_monomial_succ (f : R) (N t k : ℕ)
    (a : comparisonExterior R) :
    comparisonSectionMap R (comparisonAlgHom f N t (EvenVariableAlgebra.monomial (k + 1) a)) =
      0 := by
  rw [comparisonAlgHom_apply, comparisonLift_monomial_succ, map_zero]

end Homotopy

section SignCalculus

variable {R : Type u} [CommRing R]

/-- The cycle `z - f^{N-t} x` has exterior degree one. -/
theorem comparisonCycle_mem_one (f : R) (N t : ℕ) :
    comparisonCycle f N t ∈ exteriorGrade R (Fin 2 → R) 1 := by
  simpa using comparisonCycle_mem f N t

/-- The grading sign moves a homogeneous element past the cycle `z - f^{N-t} x`. -/
theorem signRingHom_mul_comparisonCycle (f : R) (N t m : ℕ) {b : comparisonExterior R}
    (hb : b ∈ exteriorGrade R (Fin 2 → R) m) :
    signRingHom (exteriorGrade R (Fin 2 → R)) 1 b * comparisonCycle f N t =
      comparisonCycle f N t * b := by
  rw [signRingHom_of_mem (exteriorGrade R (Fin 2 → R)) 1 m hb, smul_mul_assoc,
    ExteriorAlgebra.mul_comm_exteriorPower hb (comparisonCycle_mem_one f N t), smul_smul,
    ← pow_add]
  rw [show 1 * m + m * 1 = 2 * m by ring, pow_mul]
  simp

/-- The contraction of a homogeneous element of `R⟨x, z⟩` is homogeneous. -/
theorem exists_mem_exteriorGrade_comparisonContraction {k : ℕ} {a : comparisonExterior R}
    (ha : a ∈ exteriorGrade R (Fin 2 → R) k) :
    ∃ m, comparisonContraction R a ∈ exteriorGrade R (Fin 2 → R) m := by
  match k with
  | 0 =>
      refine ⟨0, ?_⟩
      rw [comparisonContraction, contraction_eq_zero_of_mem_zero _ ha]
      exact Submodule.zero_mem _
  | (j + 1) => exact ⟨j, contraction_mem _ j ha⟩

/-- Contraction with the functional dual to `z - f^{N-t} x` anticommutes with the Koszul
differential of `R⟨x, z⟩`. -/
theorem comparisonContraction_comparisonExteriorDifferential (f : R) (N t : ℕ)
    (a : comparisonExterior R) :
    comparisonContraction R (comparisonExteriorDifferential f N t a) +
        comparisonExteriorDifferential f N t (comparisonContraction R a) = 0 := by
  rw [comparisonContraction, comparisonExteriorDifferential,
    CliffordAlgebra.contractLeft_comm (d := comparisonDualZ R)]
  abel

/-- Contracting the product of the cycle `z - f^{N-t} x` with an element returns its
projection. -/
theorem comparisonContraction_comparisonCycle_mul (f : R) (N t : ℕ)
    (a : comparisonExterior R) :
    comparisonContraction R (comparisonCycle f N t * a) = comparisonProjector f N t a := by
  rw [comparisonCycle_eq_ι, comparisonContraction,
    CliffordAlgebra.contractLeft_ι_mul (comparisonDualZ R) (comparisonCycleVector f N t) a,
    comparisonDualZ_comparisonCycleVector, one_smul, ← comparisonCycle_eq_ι,
    show comparisonCycle f N t * contraction (comparisonDualZ R) a =
      comparisonCycle f N t * comparisonContraction R a from rfl,
    ← sub_comparisonProjector f N t a]
  abel

end SignCalculus

section HomotopyIdentity

variable {R : Type u} [CommRing R]

/-- The divided power monomial with coefficient zero vanishes. -/
theorem evenMonomial_zero (n : ℕ) :
    EvenVariableAlgebra.monomial n (0 : comparisonExterior R) = 0 := by
  rw [← EvenVariableAlgebra.monomialLinearMap_apply (R := R) n 0, map_zero]

/-- The divided power monomial `(-a) u⁽ⁿ⁾` is `-(a u⁽ⁿ⁾)`. -/
theorem evenMonomial_neg (n : ℕ) (a : comparisonExterior R) :
    EvenVariableAlgebra.monomial n (-a) = -EvenVariableAlgebra.monomial n a := by
  rw [← EvenVariableAlgebra.monomialLinearMap_apply (R := R) n (-a),
    ← EvenVariableAlgebra.monomialLinearMap_apply (R := R) n a, map_neg]

/-- The divided power monomial `(a - b) u⁽ⁿ⁾` is `a u⁽ⁿ⁾ - b u⁽ⁿ⁾`. -/
theorem evenMonomial_sub (n : ℕ) (a b : comparisonExterior R) :
    EvenVariableAlgebra.monomial n (a - b) =
      EvenVariableAlgebra.monomial n a - EvenVariableAlgebra.monomial n b := by
  rw [← EvenVariableAlgebra.monomialLinearMap_apply (R := R) n (a - b),
    ← EvenVariableAlgebra.monomialLinearMap_apply (R := R) n a,
    ← EvenVariableAlgebra.monomialLinearMap_apply (R := R) n b, map_sub]

/-- The differential of `B_{N,t}` on `a u⁽ⁿ⁾` is `d(a) u⁽ⁿ⁾`, plus, for `n > 0`, the grading
sign of `a` times `z - f^{N-t} x`, in divided power degree `n - 1`. -/
theorem comparisonDifferential_monomial (f : R) (N t n : ℕ) (a : comparisonExterior R) :
    comparisonDifferential f N t (EvenVariableAlgebra.monomial n a) =
      EvenVariableAlgebra.monomial n (comparisonExteriorDifferential f N t a) +
        if n = 0 then 0
        else EvenVariableAlgebra.monomial (n - 1)
          (signRingHom (exteriorGrade R (Fin 2 → R)) 1 a * comparisonCycle f N t) :=
  evenPolynomialDifferential_monomial _ _ _ n a

/-- The differential of `B_{N,t}` on `a u⁽⁰⁾` is `d(a) u⁽⁰⁾`. -/
theorem comparisonDifferential_monomial_zero (f : R) (N t : ℕ) (a : comparisonExterior R) :
    comparisonDifferential f N t (EvenVariableAlgebra.monomial 0 a) =
      EvenVariableAlgebra.monomial 0 (comparisonExteriorDifferential f N t a) := by
  rw [comparisonDifferential_monomial]
  simp

/-- The differential of `B_{N,t}` on `a u⁽ᵏ⁺¹⁾` is `d(a) u⁽ᵏ⁺¹⁾` plus the grading sign of `a`
times `z - f^{N-t} x`, in divided power degree `k`. -/
theorem comparisonDifferential_monomial_succ (f : R) (N t k : ℕ) (a : comparisonExterior R) :
    comparisonDifferential f N t (EvenVariableAlgebra.monomial (k + 1) a) =
      EvenVariableAlgebra.monomial (k + 1) (comparisonExteriorDifferential f N t a) +
        EvenVariableAlgebra.monomial k
          (signRingHom (exteriorGrade R (Fin 2 → R)) 1 a * comparisonCycle f N t) := by
  rw [comparisonDifferential_monomial]
  simp

/-- The leading coefficient produced by the homotopy identity: the grading sign of the
contraction, times the cycle, is the projection minus the element. -/
theorem signRingHom_neg_comparisonContraction_mul (f : R) (N t k : ℕ)
    {a : comparisonExterior R} (ha : a ∈ exteriorGrade R (Fin 2 → R) k) :
    signRingHom (exteriorGrade R (Fin 2 → R)) 1 (-comparisonContraction R a) *
        comparisonCycle f N t =
      comparisonProjector f N t a - a := by
  obtain ⟨m, hm⟩ := exists_mem_exteriorGrade_comparisonContraction ha
  rw [map_neg, neg_mul, signRingHom_mul_comparisonCycle f N t m hm,
    ← sub_comparisonProjector f N t a]
  abel

/-- The trailing coefficient produced by the homotopy identity: contracting the grading sign of
an element times the cycle returns its projection. -/
theorem comparisonContraction_signRingHom_mul (f : R) (N t k : ℕ)
    {a : comparisonExterior R} (ha : a ∈ exteriorGrade R (Fin 2 → R) k) :
    comparisonContraction R
        (signRingHom (exteriorGrade R (Fin 2 → R)) 1 a * comparisonCycle f N t) =
      comparisonProjector f N t a := by
  rw [signRingHom_mul_comparisonCycle f N t k ha,
    comparisonContraction_comparisonCycle_mul f N t a]

/-- The Koszul differential of `R⟨x, z⟩` anticommutes with the negated contraction. -/
theorem comparisonExteriorDifferential_neg_comparisonContraction (f : R) (N t : ℕ)
    (a : comparisonExterior R) :
    comparisonExteriorDifferential f N t (-comparisonContraction R a) +
        -comparisonContraction R (comparisonExteriorDifferential f N t a) = 0 := by
  rw [map_neg, ← neg_add]
  rw [show comparisonExteriorDifferential f N t (comparisonContraction R a) +
      comparisonContraction R (comparisonExteriorDifferential f N t a) = 0 from by
    rw [add_comm]
    exact comparisonContraction_comparisonExteriorDifferential f N t a]
  exact neg_zero

/-- The homotopy identity on a divided power monomial with homogeneous coefficient. -/
theorem comparisonHomotopy_monomial_eq_of_mem (f : R) (N t n k : ℕ)
    {a : comparisonExterior R} (ha : a ∈ exteriorGrade R (Fin 2 → R) k) :
    comparisonSectionMap R (comparisonAlgHom f N t (EvenVariableAlgebra.monomial n a)) -
        EvenVariableAlgebra.monomial n a =
      comparisonDifferential f N t
          (comparisonHomotopy R (EvenVariableAlgebra.monomial n a)) +
        comparisonHomotopy R
          (comparisonDifferential f N t (EvenVariableAlgebra.monomial n a)) := by
  have hzero : EvenVariableAlgebra.monomial (n + 1)
      (comparisonExteriorDifferential f N t (-comparisonContraction R a)) +
      EvenVariableAlgebra.monomial (n + 1)
        (-comparisonContraction R (comparisonExteriorDifferential f N t a)) = 0 := by
    rw [← EvenVariableAlgebra.monomial_add,
      comparisonExteriorDifferential_neg_comparisonContraction, evenMonomial_zero]
  match n with
  | 0 =>
      rw [comparisonSectionMap_comparisonAlgHom_monomial_zero, comparisonHomotopy_monomial,
        comparisonDifferential_monomial_succ, comparisonDifferential_monomial_zero,
        comparisonHomotopy_monomial, signRingHom_neg_comparisonContraction_mul f N t k ha]
      rw [show (0 : ℕ) + 1 = 1 from rfl] at hzero
      rw [add_comm (EvenVariableAlgebra.monomial 1
        (comparisonExteriorDifferential f N t (-comparisonContraction R a))), add_assoc,
        hzero, add_zero, evenMonomial_sub]
  | (j + 1) =>
      rw [comparisonSectionMap_comparisonAlgHom_monomial_succ, comparisonHomotopy_monomial,
        comparisonDifferential_monomial_succ, comparisonDifferential_monomial_succ,
        map_add, comparisonHomotopy_monomial, comparisonHomotopy_monomial,
        signRingHom_neg_comparisonContraction_mul f N t k ha,
        comparisonContraction_signRingHom_mul f N t k ha]
      rw [show j + 1 + 1 = j + 2 from rfl] at hzero ⊢
      rw [show (EvenVariableAlgebra.monomial (j + 2)
            (comparisonExteriorDifferential f N t (-comparisonContraction R a)) +
          EvenVariableAlgebra.monomial (j + 1)
            (comparisonProjector f N t a - a)) +
          (EvenVariableAlgebra.monomial (j + 2)
            (-comparisonContraction R (comparisonExteriorDifferential f N t a)) +
          EvenVariableAlgebra.monomial (j + 1) (-comparisonProjector f N t a)) =
          (EvenVariableAlgebra.monomial (j + 2)
            (comparisonExteriorDifferential f N t (-comparisonContraction R a)) +
          EvenVariableAlgebra.monomial (j + 2)
            (-comparisonContraction R (comparisonExteriorDifferential f N t a))) +
          (EvenVariableAlgebra.monomial (j + 1) (comparisonProjector f N t a - a) +
          EvenVariableAlgebra.monomial (j + 1) (-comparisonProjector f N t a)) from by abel]
      rw [hzero, zero_add, ← EvenVariableAlgebra.monomial_add]
      rw [show comparisonProjector f N t a - a + -comparisonProjector f N t a = -a from by abel]
      rw [zero_sub, evenMonomial_neg]

/-- The homotopy identity on a divided power monomial. -/
theorem comparisonHomotopy_monomial_eq (f : R) (N t n : ℕ) (a : comparisonExterior R) :
    comparisonSectionMap R (comparisonAlgHom f N t (EvenVariableAlgebra.monomial n a)) -
        EvenVariableAlgebra.monomial n a =
      comparisonDifferential f N t
          (comparisonHomotopy R (EvenVariableAlgebra.monomial n a)) +
        comparisonHomotopy R
          (comparisonDifferential f N t (EvenVariableAlgebra.monomial n a)) := by
  induction a using DirectSum.Decomposition.inductionOn (exteriorGrade R (Fin 2 → R)) with
  | zero => simp
  | homogeneous b => exact comparisonHomotopy_monomial_eq_of_mem f N t n _ b.property
  | add b c hb hc =>
      rw [EvenVariableAlgebra.monomial_add]
      simp only [map_add]
      rw [add_sub_add_comm]
      rw [hb, hc]
      abel

/-- **The homotopy identity.** The section composed with the comparison homomorphism differs from
the identity of `B_{N,t}` by the commutator of the homotopy operator with the differential, so
`B_{N,t} → K_t` is a homotopy equivalence of complexes of `R`-modules. -/
theorem comparisonHomotopy_eq (f : R) (N t : ℕ)
    (x : EvenVariableAlgebra (comparisonExterior R)) :
    comparisonSectionMap R (comparisonAlgHom f N t x) - x =
      comparisonDifferential f N t (comparisonHomotopy R x) +
        comparisonHomotopy R (comparisonDifferential f N t x) := by
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add n a y hy =>
      simp only [map_add]
      rw [add_sub_add_comm]
      rw [comparisonHomotopy_monomial_eq f N t n a, hy]
      abel

end HomotopyIdentity

section Grading

variable {R : Type u} [CommRing R]

/-- `comparisonContraction` is contraction with `comparisonDualZ`. -/
theorem comparisonContraction_apply (a : comparisonExterior R) :
    comparisonContraction R a = contraction (comparisonDualZ R) a := rfl

/-- The section preserves the exterior degree. -/
theorem comparisonSectionMap_mem (m : ℕ) {y : ExteriorAlgebra R (Fin 1 → R)}
    (hy : y ∈ exteriorGrade R (Fin 1 → R) m) :
    comparisonSectionMap R y ∈
      EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2 m := by
  rw [comparisonSectionMap_apply, ← EvenVariableAlgebra.coeffEmbedding_apply]
  exact (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff _ 2 m _).2
    (ExteriorAlgebra.map_mem_exteriorPower (comparisonXInclusion R) hy)

/-- The section preserves the cohomological grading. -/
theorem comparisonSectionMap_mem_grading (n : ℤ) {y : ExteriorAlgebra R (Fin 1 → R)}
    (hy : y ∈ cohomologicalExteriorGrade R (Fin 1 → R) n) :
    comparisonSectionMap R y ∈ cohomologicalGrade
      (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalExteriorGrade_neg_natCast] at hy
    rw [cohomologicalGrade_neg_natCast]
    exact comparisonSectionMap_mem k hy
  · have h0 : y = 0 := eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R _ (by omega) hy
    rw [h0, map_zero]
    exact Submodule.zero_mem _

/-- The section commutes with the differentials. -/
theorem comparisonDifferential_comparisonSectionMap (f : R) (N t : ℕ)
    (y : ExteriorAlgebra R (Fin 1 → R)) :
    comparisonDifferential f N t (comparisonSectionMap R y) =
      comparisonSectionMap R (contraction (seqDual fun _ : Fin 1 => f ^ t) y) := by
  rw [comparisonSectionMap_apply, comparisonDifferential_monomial_zero,
    comparisonSectionMap_apply, comparisonExteriorDifferential,
    contractLeft_exteriorAlgebraMap (comparisonXInclusion R) (seqDual (comparisonSeq f N t)) y,
    seqDual_comp_comparisonXInclusion]

/-- The homotopy operator raises the exterior degree by one. -/
theorem comparisonHomotopy_mem (m : ℕ) {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2 m) :
    comparisonHomotopy R x ∈
      EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2 (m + 1) := by
  refine EvenVariableAlgebra.homogeneous_induction_on hx ?_ ?_ ?_
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro n a hn ha
    rw [comparisonHomotopy_monomial, EvenVariableAlgebra.monomial_mem_grade_iff]
    split_ifs with hle
    · obtain ⟨j, hj⟩ : ∃ j, m - n * 2 = j + 1 := ⟨m - n * 2 - 1, by omega⟩
      rw [hj] at ha
      rw [show m + 1 - (n + 1) * 2 = j from by omega, comparisonContraction_apply]
      exact Submodule.neg_mem _ (contraction_mem _ j ha)
    · rw [show m - n * 2 = 0 from by omega] at ha
      rw [comparisonContraction_apply, contraction_eq_zero_of_mem_zero _ ha, neg_zero]
      exact Submodule.zero_mem _
  · intro y z _ _ ihy ihz
    rw [map_add]
    exact Submodule.add_mem _ ihy ihz

/-- The homotopy operator lowers the cohomological grading by one. -/
theorem comparisonHomotopy_mem_grading (n : ℤ)
    {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ cohomologicalGrade
      (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n) :
    comparisonHomotopy R x ∈ cohomologicalGrade
      (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) (n - 1) := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [cohomologicalGrade_neg_natCast] at hx
    rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring,
      cohomologicalGrade_neg_natCast]
    exact comparisonHomotopy_mem k hx
  · have h0 : x = 0 := eq_zero_of_mem_cohomologicalGrade_of_pos _ (by omega) hx
    rw [h0, map_zero]
    exact Submodule.zero_mem _

end Grading

section QuasiIsomorphism

variable {R : Type u} [CommRing R]

/-- Every cocycle of `K_t` is the image of a cocycle of `B_{N,t}` of the same degree, so the
comparison homomorphism is surjective on cohomology. -/
theorem exists_cycle_comparisonAlgHom (f : R) (N t : ℕ) (n : ℤ)
    {y : ExteriorAlgebra R (Fin 1 → R)}
    (hy : y ∈ cohomologicalExteriorGrade R (Fin 1 → R) n)
    (hdy : contraction (seqDual fun _ : Fin 1 => f ^ t) y = 0) :
    ∃ x : EvenVariableAlgebra (comparisonExterior R),
      x ∈ cohomologicalGrade (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n ∧
        comparisonDifferential f N t x = 0 ∧ comparisonAlgHom f N t x = y := by
  refine ⟨comparisonSectionMap R y, comparisonSectionMap_mem_grading n hy, ?_, ?_⟩
  · rw [comparisonDifferential_comparisonSectionMap, hdy, map_zero]
  · exact comparisonAlgHom_comparisonSectionMap f N t y

/-- A cocycle of `B_{N,t}` whose image in `K_t` is a coboundary is itself a coboundary, so the
comparison homomorphism is injective on cohomology. -/
theorem exists_primitive_of_comparisonAlgHom (f : R) (N t : ℕ) (n : ℤ)
    {x : EvenVariableAlgebra (comparisonExterior R)}
    (hx : x ∈ cohomologicalGrade
      (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) n)
    (hdx : comparisonDifferential f N t x = 0)
    {z : ExteriorAlgebra R (Fin 1 → R)}
    (hz : z ∈ cohomologicalExteriorGrade R (Fin 1 → R) (n - 1))
    (hzx : contraction (seqDual fun _ : Fin 1 => f ^ t) z = comparisonAlgHom f N t x) :
    ∃ w : EvenVariableAlgebra (comparisonExterior R),
      w ∈ cohomologicalGrade
          (EvenVariableAlgebra.grade (exteriorGrade R (Fin 2 → R)) 2) (n - 1) ∧
        comparisonDifferential f N t w = x := by
  refine ⟨comparisonSectionMap R z - comparisonHomotopy R x, ?_, ?_⟩
  · exact Submodule.sub_mem _ (comparisonSectionMap_mem_grading (n - 1) hz)
      (comparisonHomotopy_mem_grading n hx)
  · have hkey := comparisonHomotopy_eq f N t x
    rw [hdx, map_zero, add_zero] at hkey
    rw [map_sub, comparisonDifferential_comparisonSectionMap, hzx, ← hkey]
    abel

/-- The differential of `K_t` is contraction with the functional sending the generator `x` to
`f^t`. -/
theorem powAlgebra_one_d (f : R) (t : ℕ) (y : ExteriorAlgebra R (Fin 1 → R)) :
    (powAlgebra (fun _ : Fin 1 => f) t).d y =
      contraction (seqDual fun _ : Fin 1 => f ^ t) y := rfl

/-- **The comparison homomorphism is surjective on cohomology.** Stated for the bundled
differential graded algebras `B_{N,t}` and `K_t`. -/
theorem exists_cycle_comparisonToKoszul (f : R) {N t : ℕ} (h : t ≤ N) (n : ℤ)
    {y : (powAlgebra (fun _ : Fin 1 => f) t).A}
    (hy : y ∈ (powAlgebra (fun _ : Fin 1 => f) t).grading n)
    (hdy : (powAlgebra (fun _ : Fin 1 => f) t).d y = 0) :
    ∃ x : (comparisonAlgebra f h).A, x ∈ (comparisonAlgebra f h).grading n ∧
      (comparisonAlgebra f h).d x = 0 ∧
      (comparisonToKoszul f h).toAlgebraHom x = y := by
  rw [powAlgebra_grading] at hy
  have hdy' : contraction (seqDual fun _ : Fin 1 => f ^ t) y = 0 := hdy
  obtain ⟨x, hx, hdx, hxy⟩ := exists_cycle_comparisonAlgHom f N t n hy hdy'
  refine ⟨x, ?_, ?_, hxy⟩
  · rw [comparisonAlgebra_grading]
    exact hx
  · rw [comparisonAlgebra_d]
    exact hdx

/-- **The comparison homomorphism is injective on cohomology.** Stated for the bundled
differential graded algebras `B_{N,t}` and `K_t`. -/
theorem exists_primitive_of_comparisonToKoszul (f : R) {N t : ℕ} (h : t ≤ N) (n : ℤ)
    {x : (comparisonAlgebra f h).A} (hx : x ∈ (comparisonAlgebra f h).grading n)
    (hdx : (comparisonAlgebra f h).d x = 0)
    {z : (powAlgebra (fun _ : Fin 1 => f) t).A}
    (hz : z ∈ (powAlgebra (fun _ : Fin 1 => f) t).grading (n - 1))
    (hzx : (powAlgebra (fun _ : Fin 1 => f) t).d z =
      (comparisonToKoszul f h).toAlgebraHom x) :
    ∃ w : (comparisonAlgebra f h).A, w ∈ (comparisonAlgebra f h).grading (n - 1) ∧
      (comparisonAlgebra f h).d w = x := by
  rw [comparisonAlgebra_grading] at hx
  rw [comparisonAlgebra_d] at hdx
  rw [powAlgebra_grading] at hz
  have hzx' : contraction (seqDual fun _ : Fin 1 => f ^ t) z = comparisonAlgHom f N t x := hzx
  obtain ⟨w, hw, hdw⟩ := exists_primitive_of_comparisonAlgHom f N t n hx hdx hz hzx'
  refine ⟨w, ?_, ?_⟩
  · rw [comparisonAlgebra_grading]
    exact hw
  · rw [comparisonAlgebra_d]
    exact hdw

end QuasiIsomorphism

end Koszul
