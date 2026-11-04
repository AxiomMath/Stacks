module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RestrictedPowerSeries

/-!
# The coefficient ideal of a restricted power series ring

Let `I` be a finitely generated ideal of a commutative ring `A` and let `A{σ}` denote the
restricted power series ring, the inverse limit of the polynomial rings `(A ⧸ I ^ n)[σ]`. The
`n`-th power of the extended ideal `I · A{σ}` is exactly the kernel of the projection to
`(A ⧸ I ^ n)[σ]`, so that projection identifies `A{σ} ⧸ (I · A{σ}) ^ n` with `(A ⧸ I ^ n)[σ]`
and the inverse limit topology on `A{σ}` is the `I · A{σ}`-adic one.

## Main definitions

* `RestrictedPowerSeries.coefficientIdeal`: the extended ideal `I · A{σ}`.
* `RestrictedPowerSeries.quotientCoefficientIdealPowEquiv`: the identification
  `A{σ} ⧸ (I · A{σ}) ^ n ≃+* (A ⧸ I ^ n)[σ]`.

## Main results

* `RestrictedPowerSeries.coefficientProjection_surjective`: the projection to the polynomial
  ring over `A ⧸ I ^ n` is surjective.
* `RestrictedPowerSeries.ker_coefficientProjection`: its kernel is `(I · A{σ}) ^ n`.
* `RestrictedPowerSeries.isAdic_coefficientIdeal`: the inverse limit topology on `A{σ}` is the
  `I · A{σ}`-adic topology.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0AL0](https://stacks.math.columbia.edu/tag/0AL0)
-/

@[expose] public section

namespace RestrictedPowerSeries

section

universe u v

variable {A : Type u} [CommRing A]

/-- The extended coefficient ideal `I · A{σ}` of a restricted power series ring. -/
public noncomputable abbrev coefficientIdeal (I : Ideal A) (σ : Type v) :
    Ideal (RestrictedPowerSeries I σ) :=
  I.map (coefficientRingHom I σ)

/-- Every polynomial over `A ⧸ I ^ n` is the level `n` coefficient reduction of a restricted
power series. -/
public theorem coefficientProjection_surjective (I : Ideal A) (σ : Type v) (n : ℕ) :
    Function.Surjective (coefficientProjection I σ n) := by
  intro q
  obtain ⟨p, hp⟩ :=
    MvPolynomial.map_surjective (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective q
  exact ⟨polynomialRingHom I σ p, (coefficientProjection_polynomialRingHom I σ n p).trans hp⟩

/-- The canonical equivalence with the completion of the polynomial ring carries the `n`-th
power of the extended coefficient ideal to the `n`-th power of the extended coefficient ideal
of that completion. -/
private theorem map_coefficientIdeal_pow (I : Ideal A) (σ : Type v) (n : ℕ) :
    ((coefficientIdeal I σ) ^ n).map
        (adicCompletionEquiv I σ : RestrictedPowerSeries I σ →+*
          AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
            (MvPolynomial σ A)) =
      (I.map (algebraMap A (AdicCompletion
        (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)))) ^ n := by
  have hcomp : ((adicCompletionEquiv I σ : RestrictedPowerSeries I σ →+*
        AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
          (MvPolynomial σ A))).comp (coefficientRingHom I σ) =
      algebraMap A (AdicCompletion
        (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)) :=
    RingHom.ext fun a => (adicCompletionAlgEquiv I σ).commutes a
  rw [← Ideal.map_pow, Ideal.map_map, hcomp, Ideal.map_pow]

/-- Membership in the `n`-th power of the extended coefficient ideal is detected by the
canonical equivalence with the completion of the polynomial ring. -/
private theorem mem_coefficientIdeal_pow_iff_mem_map (I : Ideal A) (σ : Type v) (n : ℕ)
    (x : RestrictedPowerSeries I σ) :
    x ∈ (coefficientIdeal I σ) ^ n ↔
      adicCompletionEquiv I σ x ∈ (I.map (algebraMap A (AdicCompletion
        (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)))) ^ n := by
  rw [← map_coefficientIdeal_pow I σ n]
  refine ⟨fun hx => Ideal.mem_map_of_mem _ hx, fun hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_of_equiv (adicCompletionEquiv I σ) _).mp hx
  exact ((adicCompletionEquiv I σ).injective hyx) ▸ hy

/-- Over a finitely generated coefficient ideal, membership in the `n`-th power of the extended
coefficient ideal is detected by the level `n` coefficient reduction. -/
public theorem mem_coefficientIdeal_pow_iff (I : Ideal A) (hI : I.FG) (σ : Type v) (n : ℕ)
    (x : RestrictedPowerSeries I σ) :
    x ∈ (coefficientIdeal I σ) ^ n ↔ coefficientProjection I σ n x = 0 := by
  have hKfg : (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)).FG := hI.map _
  have hmapcomp : (algebraMap (MvPolynomial σ A)
        (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
          (MvPolynomial σ A))).comp (MvPolynomial.C : A →+* MvPolynomial σ A) =
      algebraMap A (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)) := by
    simpa only [MvPolynomial.C_eq_algebraMap] using
      (IsScalarTower.algebraMap_eq A (MvPolynomial σ A)
        (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
          (MvPolynomial σ A))).symm
  have htarget : ∀ y : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A),
      y ∈ (I.map (algebraMap A (AdicCompletion
          (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)))) ^ n ↔
        AdicCompletion.evalₐ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) n y = 0 := by
    intro y
    have hquot : ((I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n •
        (⊤ : Ideal (MvPolynomial σ A))) =
        (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n := by ext z; simp
    have heval :
        AdicCompletion.eval (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
            (MvPolynomial σ A) n y = 0 ↔
          AdicCompletion.evalₐ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) n y = 0 := by
      change _ = 0 ↔ (Ideal.quotientEquivAlgOfEq (MvPolynomial σ A) hquot)
        (AdicCompletion.eval (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
          (MvPolynomial σ A) n y) = 0
      exact (map_eq_zero_iff (Ideal.quotientEquivAlgOfEq (MvPolynomial σ A) hquot)
        (AlgEquiv.injective (Ideal.quotientEquivAlgOfEq (MvPolynomial σ A) hquot))).symm
    rw [← hmapcomp, ← Ideal.map_map, ← Ideal.map_pow]
    change y ∈ (Submodule.restrictScalars (MvPolynomial σ A)
      (Ideal.map (algebraMap (MvPolynomial σ A) _)
        ((I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n)) : Submodule (MvPolynomial σ A) _)
      ↔ _
    rw [← Ideal.smul_top_eq_map]
    simpa only [AdicCompletion.pow_smul_top_eq_ker_eval hKfg, LinearMap.mem_ker] using heval
  rw [mem_coefficientIdeal_pow_iff_mem_map I σ n, htarget, eval_adicCompletionEquiv]
  change (polynomialQuotientEquiv I σ n) (coefficientProjection I σ n x) = 0 ↔ _
  exact map_eq_zero_iff _ (polynomialQuotientEquiv I σ n).injective

/-- The kernel of the level `n` coefficient reduction is the `n`-th power of the extended
coefficient ideal, provided the coefficient ideal is finitely generated. -/
public theorem ker_coefficientProjection (I : Ideal A) (hI : I.FG) (σ : Type v) (n : ℕ) :
    RingHom.ker (coefficientProjection I σ n) = (coefficientIdeal I σ) ^ n := by
  ext x
  rw [RingHom.mem_ker, mem_coefficientIdeal_pow_iff I hI σ n]

/-- The level `n` coefficient reduction identifies `A{σ} ⧸ (I · A{σ}) ^ n` with the polynomial
ring `(A ⧸ I ^ n)[σ]`. -/
public noncomputable def quotientCoefficientIdealPowEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (n : ℕ) :
    RestrictedPowerSeries I σ ⧸ (coefficientIdeal I σ) ^ n ≃+*
      MvPolynomial σ (A ⧸ I ^ n) :=
  (Ideal.quotEquivOfEq (ker_coefficientProjection I hI σ n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (coefficientProjection_surjective I σ n))

/-- The identification of `A{σ} ⧸ (I · A{σ}) ^ n` with `(A ⧸ I ^ n)[σ]` is induced by the level
`n` coefficient reduction. -/
@[simp]
public theorem quotientCoefficientIdealPowEquiv_mk (I : Ideal A) (hI : I.FG) (σ : Type v)
    (n : ℕ) (x : RestrictedPowerSeries I σ) :
    quotientCoefficientIdealPowEquiv I hI σ n (Ideal.Quotient.mk _ x) =
      coefficientProjection I σ n x := rfl

/-- Powers of the extended coefficient ideal are a fundamental system of neighbourhoods of zero
for the inverse limit topology on restricted power series. -/
public theorem hasBasis_nhds_zero_coefficientIdeal (I : Ideal A) (hI : I.FG) (σ : Type v) :
    (nhds (0 : RestrictedPowerSeries I σ)).HasBasis (fun _ : ℕ => True)
      (fun n => (((coefficientIdeal I σ) ^ n : Ideal (RestrictedPowerSeries I σ)) :
        Set (RestrictedPowerSeries I σ))) := by
  let _ : TopologicalSpace (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A)) := polynomialCompletionAdicTopology I σ
  have hf := isHomeomorph_adicCompletionEquiv I σ hI
  rw [hf.isInducing.nhds_eq_comap, map_zero]
  have hb := (I.map (algebraMap A (AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)))).hasBasis_nhds_zero_adic.comap
      (adicCompletionEquiv I σ : RestrictedPowerSeries I σ →
        AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A))
  exact hb.congr (fun _ => Iff.rfl) fun n _ =>
    Set.ext fun x => (mem_coefficientIdeal_pow_iff_mem_map I σ n x).symm

/-- The inverse limit topology on restricted power series over a finitely generated coefficient
ideal is the adic topology of the extended coefficient ideal. -/
@[ega "0 7.5.4" "(ii)"]
public theorem isAdic_coefficientIdeal (I : Ideal A) (hI : I.FG) (σ : Type v) :
    IsAdic (coefficientIdeal I σ) := by
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · exact ((coefficientIdeal I σ) ^ n).toAddSubgroup.isOpen_of_mem_nhds
      ((hasBasis_nhds_zero_coefficientIdeal I hI σ).mem_of_mem (i := n) trivial)
  · obtain ⟨n, -, hn⟩ := (hasBasis_nhds_zero_coefficientIdeal I hI σ).mem_iff.mp hU
    exact ⟨n, hn⟩

/-- Restricted power series over a finitely generated coefficient ideal carry a linear
topology. -/
public theorem isLinearTopology_restrictedPowerSeries (I : Ideal A) (hI : I.FG) (σ : Type v) :
    IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
  IsLinearTopology.mk_of_hasBasis _ (hasBasis_nhds_zero_coefficientIdeal I hI σ)

/-- The inverse limit topology on restricted power series is Hausdorff. -/
public theorem t2Space_restrictedPowerSeries (I : Ideal A) (σ : Type v) :
    T2Space (RestrictedPowerSeries I σ) := by
  let _ : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⊥
  let _ : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  exact inferInstanceAs (T2Space (↑(inverseLimitSubring I σ)))

end

end RestrictedPowerSeries

end
