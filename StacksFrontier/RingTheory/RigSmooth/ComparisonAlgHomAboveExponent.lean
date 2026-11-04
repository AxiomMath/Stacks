module

public import StacksFrontier.RingTheory.RigSmooth.ComparisonAlgHom

/-!
# The comparison map, with the dual situations asked only above the exponent

A dual situation of Local Cohomology, Section 0GA6, at thickness `m` and exponent `c` exists only
for `c ≤ m`. The inputs of the lifting lemma Stacks 0GAQ for the target `P ⧸ b`, with the family
of dual situations given at the thicknesses `m ≥ c`, are bundled as
`Rig.PerturbedPresentation.LiftingInputsAboveExponent`. From them we obtain the comparison map
`P ⧸ a → P ⧸ b` and the form of Stacks 0GAR over `P = A[x₁, …, x_r]^∧`.

## Main definitions

* `Rig.PerturbedPresentation.LiftingInputsAboveExponent`: the inputs of Stacks 0GAQ for
  `P ⧸ b`, with the dual situations asked at the thicknesses `m ≥ c`.

## Main results

* `Rig.PerturbedPresentation.exists_dualSituation_family`: a family of dual situations for
  `P ⧸ b`, one at each thickness `m ≥ c`, with `d = q₀ = 0`.
* `Rig.PerturbedPresentation.exists_comparison_algHom_of_liftingInputsAboveExponent` and
  `exists_comparison_algHom_of_congruentModPow_of_liftingInputsAboveExponent`:
  the comparison map `P ⧸ a → P ⧸ b`.
* `Rig.PerturbedPresentation.exists_perturbationBound_algEquiv_of_liftingInputsAboveExponent`:
  Stacks 0GAR over `P`, the isomorphism holding whenever a `LiftingInputsAboveExponent` is given.
* `Rig.PerturbedPresentation.exists_perturbationBound_algEquiv_of_isRigSmooth`: the same for a
  rig-smooth `P ⧸ (g₁, …, g_m)`, with the exponent `c` obtained from rig-smoothness.

## References

* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GAQ](https://stacks.math.columbia.edu/tag/0GAQ)
* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.LocalCohomology.UniformityIII

universe u

namespace Rig.PerturbedPresentation

/-! ### The inputs of the lifting lemma, above the exponent -/

section Inputs

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

/-- **The inputs of the lifting lemma Stacks 0GAQ for the target `P ⧸ b`.** A family of dual
situations of Local Cohomology, Section 0GA6, one at each thickness `m ≥ c`, whose invariants
`d` and `q₀` do not depend on `m`, together with the open duality input of Tag 0GAC at every
level `m ≥ n`: the section of `p^*(M^∨)` at level `m - 2c` obtained by factoring through
`can : p^*(M^∨) → (p^*M)^∨`. -/
public structure LiftingInputsAboveExponent (b : Ideal (completedPolynomialAlgebra I r))
    (n c d q₀ : ℕ) where
  /-- The dual situation of Section 0GA6 at each thickness `m ≥ c`. -/
  dualSituation : ∀ m : ℕ, c ≤ m → DualSituation (quotRing A I r b) (quotIdeal A I r b) m c
  /-- The invariant `d` does not depend on the thickness. -/
  dim_eq : ∀ m (hm : c ≤ m), (dualSituation m hm).d = d
  /-- The invariant `q₀` does not depend on the thickness. -/
  bound_eq : ∀ m (hm : c ≤ m), (dualSituation m hm).q₀ = q₀
  /-- The open duality input of Tag 0GAC, at every level `m ≥ n`. -/
  openDuality : ∀ (m e : ℕ) (hm : c ≤ m) (_ : n ≤ m) (hem : e + 2 * c = m)
      (hq : (dualSituation m hm).q₀ ≤ e)
      (M : ANCModule (quotIdeal A I r b) m c)
      (ϕ : resModule (quotIdeal A I r b) m M.1 →ₗ[quotRing A I r b]
        powQuot (quotIdeal A I r b) m m),
    ∃ σ' : (dualSituation m hm).H M.dual 0 (e : ℤ),
      (dualSituation m hm).ev M e hq σ'
        = (powQuotLe (quotIdeal A I r b) (Nat.le.intro hem)).comp ϕ

/-- For every `c` there is a family of dual situations for `P ⧸ b`, one at each thickness
`m ≥ c`, whose invariants are `d = 0` and `q₀ = 0`: the affine dual situation
`affineDualSituation`, with `H⁰(X, p^*(M^∨)(q))` given by `I^q ⊗_A M^∨` and the evaluation of
Remark 0GAB given by the canonical map. -/
public theorem exists_dualSituation_family (b : Ideal (completedPolynomialAlgebra I r))
    (c : ℕ) :
    ∃ S : ∀ m : ℕ, c ≤ m → DualSituation (quotRing A I r b) (quotIdeal A I r b) m c,
      (∀ m (hm : c ≤ m), (S m hm).d = 0) ∧ (∀ m (hm : c ≤ m), (S m hm).q₀ = 0) :=
  ⟨fun m hm => affineDualSituation (quotIdeal A I r b) m c hm,
    fun _ _ => rfl, fun _ _ => rfl⟩

end Inputs

/-! ### The comparison map -/

section Comparison

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

/-- **The comparison map of Stacks 0GAQ for a pair of ideals of `P = A[x₁, …, x_r]^∧`.**

Let `a, b ⊆ P` be ideals with `a ⊆ b + (IP)ⁿ`, let `I ^ c` annihilate `Ext¹` from the completed
naive cotangent complex of the tautological presentation of `P ⧸ a`, and let the invariants of
`P ⧸ b` of Local Cohomology, Section 0GA6 be carried by `L`. Then, for `n` as large as the
lifting lemma requires, there is an `A`-algebra map

`φ : P ⧸ a → P ⧸ b`  with  `φ(z mod a) - (z mod b) ∈ (I · (P ⧸ b))^{n - (k+3)c}`

for every `z ∈ P`, where `max(d, 1) = k + 1`. -/
public theorem exists_comparison_algHom_of_liftingInputsAboveExponent
    (a b : Ideal (completedPolynomialAlgebra I r)) (n c d q₀ k : ℕ)
    (hab : a ≤ b ⊔ (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ n)
    (hExt : ExtAnnihilated A I r a c) (L : LiftingInputsAboveExponent A I r b n c d q₀)
    (hk : max d 1 = k + 1)
    (hn₁ : q₀ + (k + 2) * c ≤ n) (hn₂ : 2 * ((k + 3) * c) < n) :
    ∃ φ : (completedPolynomialAlgebra I r ⧸ a) →ₐ[A] (quotRing A I r b),
      ∀ z : completedPolynomialAlgebra I r,
        φ (Ideal.Quotient.mk a z) - Ideal.Quotient.mk b z
          ∈ (quotIdeal A I r b) ^ (n - (k + 3) * c) := by
  have : IsAdicComplete (quotIdeal A I r b) (quotRing A I r b) :=
    isAdicComplete_quotRing A I r b
  obtain ⟨φ, hφ⟩ := Rig.exists_algHom_lift_of_dualSituation' (quotientObj A I r a)
    (quotientPresentation A I r a) c hExt L.dualSituation d q₀ k L.dim_eq L.bound_eq hk
    n hn₁ hn₂ L.openDuality (compareModPow I hab)
  refine ⟨φ, fun z => ?_⟩
  have h : Ideal.Quotient.mk ((quotIdeal A I r b) ^ (n - (k + 3) * c))
        (Ideal.Quotient.mk b z)
      = Ideal.Quotient.mk ((quotIdeal A I r b) ^ (n - (k + 3) * c))
        (φ (Ideal.Quotient.mk a z)) :=
    DFunLike.congr_fun hφ (Ideal.Quotient.mk a z)
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h.symm

/-- **The comparison map of Stacks 0GAQ for a perturbed presentation.** If the maps `g, g'` are
congruent modulo `(IP)ⁿ`, then, for `n` as large as the lifting lemma requires, there is an
`A`-algebra map

`φ : P ⧸ (g₁, …, g_m) → P ⧸ (g'₁, …, g'_m)`

congruent to the identity modulo `(I · (P ⧸ (g'₁, …, g'_m)))^{n - (k+3)c}`. -/
public theorem exists_comparison_algHom_of_congruentModPow_of_liftingInputsAboveExponent {m : ℕ}
    (g g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (n c d q₀ k : ℕ)
    (hgg' : CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n)
    (hExt : ExtAnnihilated A I r (LinearMap.range g) c)
    (L : LiftingInputsAboveExponent A I r (LinearMap.range g') n c d q₀)
    (hk : max d 1 = k + 1)
    (hn₁ : q₀ + (k + 2) * c ≤ n) (hn₂ : 2 * ((k + 3) * c) < n) :
    ∃ φ : (completedPolynomialAlgebra I r ⧸
          (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) →ₐ[A]
        (quotRing A I r (LinearMap.range g')),
      ∀ z : completedPolynomialAlgebra I r,
        φ (Ideal.Quotient.mk (LinearMap.range g :
            Ideal (completedPolynomialAlgebra I r)) z)
          - Ideal.Quotient.mk (LinearMap.range g' :
            Ideal (completedPolynomialAlgebra I r)) z
        ∈ (quotIdeal A I r (LinearMap.range g')) ^ (n - (k + 3) * c) :=
  exists_comparison_algHom_of_liftingInputsAboveExponent A I r _ _ n c d q₀ k
    (le_sup_left.trans
      (le_of_eq (range_sup_pow_eq_of_congruentModPow
        (I.map (algebraMap A (completedPolynomialAlgebra I r))) hgg')))
    hExt L hk hn₁ hn₂

end Comparison

/-! ### Stacks 0GAR over `P = A[x₁, …, x_r]^∧` -/

section Full

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

/-- **Stacks 0GAR over `P = A[x₁, …, x_r]^∧`, given `LiftingInputsAboveExponent`.**

Given a resolution `P^⊕t --K--> P^⊕m --g--> P → B → 0`, an exponent `c` for which `I ^ c`
annihilates `Ext¹` from the completed naive cotangent complex of the tautological presentation
of `B = P ⧸ (g₁, …, g_m)`, and numbers `d`, `q₀`, `k` with `max(d, 1) = k + 1`, there is an
integer `n₀` such that for every `n ≥ n₀` and every complex `P^⊕t --K'--> P^⊕m --g'--> P`
congruent to the given one modulo `IⁿP`:

* the perturbed complex is again a resolution, and
* `P ⧸ (g₁, …, g_m) ≃ₐ[A] P ⧸ (g'₁, …, g'_m)` as `A`-algebras, once the geometric input for
  `B' = P ⧸ (g'₁, …, g'_m)` is given as a `LiftingInputsAboveExponent`. -/
public theorem exists_perturbationBound_algEquiv_of_liftingInputsAboveExponent {t m : ℕ}
    (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      (Fin m → completedPolynomialAlgebra I r))
    (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (hexact : LinearMap.ker g = LinearMap.range K)
    (c d q₀ k : ℕ) (hk : max d 1 = k + 1)
    (hExt : ExtAnnihilated A I r (LinearMap.range g) c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r))
        (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r),
      g'.comp K' = 0 →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) K K' n →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n →
        LinearMap.ker g' = LinearMap.range K' ∧
        (LiftingInputsAboveExponent A I r (LinearMap.range g') n c d q₀ →
          Nonempty
            ((completedPolynomialAlgebra I r ⧸
                (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) ≃ₐ[A]
              (completedPolynomialAlgebra I r ⧸
                (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r))))) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_perturbationBound_algEquiv_of_algHom A I r ((k + 3) * c) K g hexact
  refine ⟨max n₀ (max (q₀ + (k + 2) * c) (2 * ((k + 3) * c) + 1)),
    fun n hn K' g' hcomplex hKK' hgg' => ?_⟩
  obtain ⟨hker, hbound⟩ :=
    hn₀ n ((le_max_left _ _).trans hn) K' g' hcomplex hKK' hgg'
  refine ⟨hker, fun L => ?_⟩
  have hn₁ : q₀ + (k + 2) * c ≤ n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : 2 * ((k + 3) * c) < n :=
    Nat.lt_of_succ_le (((le_max_right _ _).trans (le_max_right _ _)).trans hn)
  obtain ⟨φ, hφ⟩ := exists_comparison_algHom_of_congruentModPow_of_liftingInputsAboveExponent
    A I r g g' n c d q₀ k hgg' hExt L hk hn₁ hn₂
  exact hbound φ hφ

/-- **Stacks 0GAR over `P = A[x₁, …, x_r]^∧` for a rig-smooth quotient.**

Let `P^⊕t --K--> P^⊕m --g--> P → B → 0` be a resolution and let `B = P ⧸ (g₁, …, g_m)` be
rig-smooth over `(A, I)`. Then there is an exponent `c` such that for all `d` and `q₀` there is
an integer `n₀` such that for every `n ≥ n₀` and every complex
`P^⊕t --K'--> P^⊕m --g'--> P` congruent to the given one modulo `IⁿP`:

* the perturbed complex is again a resolution, and
* `P ⧸ (g₁, …, g_m) ≃ₐ[A] P ⧸ (g'₁, …, g'_m)` as `A`-algebras, once the geometric input for
  `P ⧸ (g'₁, …, g'_m)` is given as a `LiftingInputsAboveExponent`. -/
public theorem exists_perturbationBound_algEquiv_of_isRigSmooth {t m : ℕ}
    (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      (Fin m → completedPolynomialAlgebra I r))
    (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (hexact : LinearMap.ker g = LinearMap.range K)
    (hB : IsRigSmooth (quotientObj A I r (LinearMap.range g))) :
    ∃ c : ℕ, ∀ d q₀ : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r))
        (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r),
      g'.comp K' = 0 →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) K K' n →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n →
        LinearMap.ker g' = LinearMap.range K' ∧
        (LiftingInputsAboveExponent A I r (LinearMap.range g') n c d q₀ →
          Nonempty
            ((completedPolynomialAlgebra I r ⧸
                (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) ≃ₐ[A]
              (completedPolynomialAlgebra I r ⧸
                (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r))))) := by
  obtain ⟨c₀, hc₀⟩ := exists_extAnnihilated_of_isRigSmooth A I r (LinearMap.range g) hB
  exact ⟨c₀, fun d q₀ =>
    exists_perturbationBound_algEquiv_of_liftingInputsAboveExponent A I r K g hexact
      c₀ d q₀ (max d 1 - 1) (Nat.sub_add_cancel (le_max_right d 1)).symm (hc₀ c₀ le_rfl)⟩

end Full

end Rig.PerturbedPresentation

end
