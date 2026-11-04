module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalInterpretationCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf

/-!
# The cohomological interpretation of the L-function from the trace identities, basis-free

Over a coefficient ring of characteristic zero, comparing logarithmic derivatives shows that the
identity

`L(X, ℱ) = ∏_i det(1 - π_X^* T | H^i_c(X_k̄, ℱ)) ^ ((-1) ^ (i + 1))`

follows from the trace identities

`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n/d})^* | ℱ_x̄) = ∑_i (-1) ^ i tr((π_X^n)^* | H^i_c(X_k̄, ℱ))`

for all `n ≥ 1`. `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction_eq_alternatingCharSeries`
proves this for the cohomology presented by matrices. This file states it for the cohomology
as it arises: a family `i ↦ H^i` of finite free modules indexed by the cohomological degree
`i : ℤ`, each carrying an endomorphism `π_X^*`. Only finitely many of the modules are nonzero.
The determinants and traces are those of the endomorphisms, with no basis chosen.

## Main definitions

* `Stacks.EtaleCohomology.gradedCharFactor`: the factor
  `det(1 - φ_i T | V_i) ^ ((-1) ^ (i + 1))` in degree `i`.
* `Stacks.EtaleCohomology.gradedCharSeries`: the product of the factors over all degrees.

## Main results

* `Stacks.EtaleCohomology.gradedCharSeries_eq_prod`: the product is the finite product over
  any set of degrees outside which the modules vanish.
* `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction_eq_gradedCharSeries`: the trace
  identities for all `n ≥ 1` give the determinant identity.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction_eq_gradedCharSeries`: the same for the
  L-function of a `ℚ_ℓ`-sheaf (Tag 03UX), with the local traces taken on the rational stalks.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset PowerSeries

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The alternating product of the characteristic series of a graded endomorphism -/

section Graded

variable {Λ : Type v} [CommRing Λ] (V : ℤ → Type w) [∀ i, AddCommGroup (V i)]
  [∀ i, Module Λ (V i)] (φ : ∀ i, V i →ₗ[Λ] V i)

/-- The factor `det(1 - φ_i T | V_i) ^ ((-1) ^ (i + 1))` in cohomological degree `i`. In an even
degree it is the inverse of the characteristic series, in an odd degree the series itself. -/
public def gradedCharFactor (i : ℤ) : Λ⟦X⟧ :=
  if Even i then PowerSeries.invOfUnit (charPowerSeries (φ i) 1) 1 else charPowerSeries (φ i) 1

/-- The alternating product `∏_i det(1 - φ_i T | V_i) ^ ((-1) ^ (i + 1))` over all
cohomological degrees `i`. When only finitely many `V_i` are nonzero it is a finite product,
`gradedCharSeries_eq_prod`. -/
public def gradedCharSeries : Λ⟦X⟧ :=
  ∏ᶠ i : ℤ, gradedCharFactor V φ i

variable [Nontrivial Λ] [∀ i, Module.Finite Λ (V i)] [∀ i, Module.Free Λ (V i)]

/-- In a basis of `V_i` indexed by `Fin (finrank V_i)`, the factor in degree `i` is that of the
matrix of `φ_i`. -/
public theorem gradedCharFactor_eq_matrix (i : ℤ) :
    gradedCharFactor V φ i =
      if Even i then
        localEulerFactor (LinearMap.toMatrix (Module.finBasis Λ (V i))
          (Module.finBasis Λ (V i)) (φ i)) 1
      else
        localCharSeries (LinearMap.toMatrix (Module.finBasis Λ (V i))
          (Module.finBasis Λ (V i)) (φ i)) 1 := by
  rw [gradedCharFactor, charPowerSeries_eq_localCharSeries (Module.finBasis Λ (V i))]
  rfl

/-- A degree in which the module vanishes contributes the factor `1`. -/
public theorem gradedCharFactor_eq_one {i : ℤ} (hi : Subsingleton (V i)) :
    gradedCharFactor V φ i = 1 := by
  rw [gradedCharFactor_eq_matrix]
  exact alternatingCharSeries_factor_eq_one (ι := ℤ) id (fun i => Module.finrank Λ (V i))
    (fun i => LinearMap.toMatrix (Module.finBasis Λ (V i)) (Module.finBasis Λ (V i)) (φ i))
    Module.finrank_zero_of_subsingleton

/-- If the modules vanish outside the finite set of degrees `S`, the alternating product is the
finite product over `S`. -/
public theorem gradedCharSeries_eq_prod (S : Finset ℤ) (hS : ∀ i ∉ S, Subsingleton (V i)) :
    gradedCharSeries V φ = ∏ i ∈ S, gradedCharFactor V φ i := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun i hi => ?_
  by_contra h
  exact hi (gradedCharFactor_eq_one V φ (hS i h))

/-- The alternating product over `S` is `alternatingCharSeries` of the matrices of the `φ_i` in
the bases `Module.finBasis`. -/
theorem gradedCharSeries_eq_alternatingCharSeries (S : Finset ℤ)
    (hS : ∀ i ∉ S, Subsingleton (V i)) :
    gradedCharSeries V φ =
      alternatingCharSeries (fun a : S => (a : ℤ)) (fun a => Module.finrank Λ (V a))
        (fun a => LinearMap.toMatrix (Module.finBasis Λ (V a)) (Module.finBasis Λ (V a))
          (φ a)) := by
  rw [gradedCharSeries_eq_prod V φ S hS, alternatingCharSeries, ← Finset.prod_coe_sort S]
  exact Finset.prod_congr rfl fun a _ => gradedCharFactor_eq_matrix V φ a

/-- The trace of a power of `φ_i` is the trace of the corresponding power of its matrix. -/
theorem trace_pow_eq_matrix (i : ℤ) (m : ℕ) :
    LinearMap.trace Λ (V i) (φ i ^ m) =
      ((LinearMap.toMatrix (Module.finBasis Λ (V i)) (Module.finBasis Λ (V i))
        (φ i)) ^ m).trace := by
  rw [LinearMap.trace_eq_matrix_trace Λ (Module.finBasis Λ (V i)), LinearMap.toMatrix_pow]

end Graded

/-! ### The criterion -/

namespace FrobeniusMatrices

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] {Λ : Type v} [CommRing Λ] [Nontrivial Λ]
  (D : FrobeniusMatrices f Λ)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module Λ (V i)]
  [∀ i, Module.Finite Λ (V i)] [∀ i, Module.Free Λ (V i)] (φ : ∀ i, V i →ₗ[Λ] V i)

/-- **The trace identities give the cohomological interpretation.** Let `V_i` be finite free
modules over a coefficient ring with torsion-free additive group, vanishing outside the finite
set of degrees `S`, with endomorphisms `φ_i`. Suppose that for every `n ≥ 1`

`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n / d})^*) = ∑_{i ∈ S} (-1) ^ i tr(φ_i ^ n)`.

Then `L(X) = ∏_i det(1 - φ_i T | V_i) ^ ((-1) ^ (i + 1))`. -/
public theorem lFunction_eq_gradedCharSeries [IsAddTorsionFree Λ] (S : Finset ℤ)
    (hS : ∀ i ∉ S, Subsingleton (V i))
    (htrace : ∀ m : ℕ, m ≠ 0 →
      ∑ x ∈ (D.eulerSystem.support m).filter fun x => residueDegree f x.1 ∣ m,
          (residueDegree f x.1 : Λ) * ((D.matrix x) ^ (m / residueDegree f x.1)).trace
        = ∑ i ∈ S, (if Even i then (1 : Λ) else -1) * LinearMap.trace Λ (V i) (φ i ^ m)) :
    D.lFunction = gradedCharSeries V φ := by
  rw [gradedCharSeries_eq_alternatingCharSeries V φ S hS]
  refine D.lFunction_eq_alternatingCharSeries _ _ _ fun m hm => ?_
  rw [htrace m hm, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun a _ => by rw [trace_pow_eq_matrix V φ a m]

/-- Conversely, the determinant identity gives the trace identities. -/
public theorem traceIdentity_of_lFunction_eq_gradedCharSeries (S : Finset ℤ)
    (hS : ∀ i ∉ S, Subsingleton (V i)) (h : D.lFunction = gradedCharSeries V φ) (m : ℕ)
    (hm : m ≠ 0) :
    ∑ x ∈ (D.eulerSystem.support m).filter fun x => residueDegree f x.1 ∣ m,
        (residueDegree f x.1 : Λ) * ((D.matrix x) ^ (m / residueDegree f x.1)).trace
      = ∑ i ∈ S, (if Even i then (1 : Λ) else -1) * LinearMap.trace Λ (V i) (φ i ^ m) := by
  rw [gradedCharSeries_eq_alternatingCharSeries V φ S hS] at h
  rw [D.traceFormula_of_lFunction_eq _ _ _ h m hm, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun a _ => by rw [trace_pow_eq_matrix V φ a m]

end FrobeniusMatrices

/-! ### The L-function of a `ℚ_ℓ`-sheaf -/

section LAdic

open AlgebraicGeometry.SmallEtale CategoryTheory.Limits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Finite k]

/-- The trace of a power of the matrix of `π_x^*` at a closed point is the trace of the
corresponding power of `π_x^*` acting on the rational stalk. -/
public theorem LAdicSheaf.trace_frobeniusMatrices_pow (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : closedPoints X.1) (m : ℕ) :
    (((LAdicSheaf.frobeniusMatrices B X ℓ F f).matrix x) ^ m).trace =
      LinearMap.trace (Padic ℓ) _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^ m) := by
  rw [LinearMap.trace_eq_matrix_trace (Padic ℓ) (chooseBasisFin (Padic ℓ)
    (LAdicSheaf.rationalStalkLeft B X ℓ F (Stacks.Frobenius.geometricPointAt X.1 x.1))),
    ← LinearMap.toMatrix_pow]
  rfl

/-- **The trace identities give the cohomological interpretation of `L(X, F)`.** Let `F` be a
`ℚ_ℓ`-sheaf on a scheme `X` of finite type over a finite field `k`. Let `V_i` be
finite-dimensional `ℚ_ℓ`-vector spaces, vanishing outside the finite set of degrees `S`, with
endomorphisms `φ_i`. Suppose that for every `n ≥ 1`

`∑_{d ∣ n} d ∑_{deg x = d} tr((π_x^{n / d})^* | F_x̄) = ∑_i (-1) ^ i tr(φ_i ^ n | V_i)`,

the local traces being taken on the rational stalks. Then

`L(X, F) = ∏_i det(1 - φ_i T | V_i) ^ ((-1) ^ (i + 1))`. -/
public theorem LAdicSheaf.rationalLFunction_eq_gradedCharSeries (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (Padic ℓ) (V i)]
    [∀ i, FiniteDimensional (Padic ℓ) (V i)] (φ : ∀ i, V i →ₗ[Padic ℓ] V i) (S : Finset ℤ)
    (hS : ∀ i ∉ S, Subsingleton (V i))
    (htrace : ∀ m : ℕ, m ≠ 0 →
      ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ m),
          (residueDegree f x.1 : Padic ℓ) * LinearMap.trace (Padic ℓ) _
            (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
              (m / residueDegree f x.1))
        = ∑ i ∈ S, (-1 : Padic ℓ) ^ i * LinearMap.trace (Padic ℓ) (V i) (φ i ^ m)) :
    LAdicSheaf.rationalLFunction B X ℓ F f = gradedCharSeries V φ := by
  refine FrobeniusMatrices.lFunction_eq_gradedCharSeries _ V φ S hS fun m hm => ?_
  have h := htrace m hm
  simp only [neg_one_zpow_eq_ite] at h
  rw [← h, finsum_cond_eq_sum_of_cond_iff]
  · exact Finset.sum_congr rfl fun x _ => by rw [LAdicSheaf.trace_frobeniusMatrices_pow]
  · intro x _
    rw [Finset.mem_filter, EulerSystem.mem_support]
    exact ⟨fun hx => ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hx, hx⟩, And.right⟩

/-- The form of `LAdicSheaf.rationalLFunction_eq_gradedCharSeries` with the alternating sum taken
over all degrees `i : ℤ`, for vector spaces of which only finitely many are nonzero. -/
public theorem LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_finite (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (Padic ℓ) (V i)]
    [∀ i, FiniteDimensional (Padic ℓ) (V i)] (φ : ∀ i, V i →ₗ[Padic ℓ] V i)
    (hfin : {i : ℤ | Nontrivial (V i)}.Finite)
    (htrace : ∀ m : ℕ, m ≠ 0 →
      ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ m),
          (residueDegree f x.1 : Padic ℓ) * LinearMap.trace (Padic ℓ) _
            (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
              (m / residueDegree f x.1))
        = ∑ᶠ i : ℤ, (-1 : Padic ℓ) ^ i * LinearMap.trace (Padic ℓ) (V i) (φ i ^ m)) :
    LAdicSheaf.rationalLFunction B X ℓ F f = gradedCharSeries V φ := by
  have hS : ∀ i ∉ hfin.toFinset, Subsingleton (V i) := fun i hi =>
    not_nontrivial_iff_subsingleton.1 fun h => hi (hfin.mem_toFinset.2 h)
  refine LAdicSheaf.rationalLFunction_eq_gradedCharSeries B X ℓ F f V φ hfin.toFinset hS
    fun m hm => ?_
  rw [htrace m hm]
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  by_contra h
  have := hS i h
  exact hi (by simp only [Subsingleton.elim (φ i ^ m) 0, map_zero, mul_zero])

end LAdic

end Stacks.EtaleCohomology

end
