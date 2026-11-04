module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesMap

/-!
# Restricted power series see only the coefficient quotients

Let `A → B` be a homomorphism of commutative rings, let `I` be an ideal of `A` and let
`J = I · B` be its extension.  A restricted power series ring is the inverse limit of the
polynomial rings over the coefficient quotients, and the induced map `A{σ} → B{σ}` is the
inverse limit of the reductions `A ⧸ I ^ n → B ⧸ J ^ n`; so as soon as every one of those
reductions is bijective, the induced map is an isomorphism.

This applies to the structure map of an adic completion: for a finitely generated ideal `J` of
`R`, the `n`-th evaluation identifies `R̂ ⧸ (J · R̂) ^ n` with `R ⧸ J ^ n`, and therefore
`R{σ} → R̂{σ}` is an isomorphism.  Restricted power series are thus insensitive to adically
completing the coefficient ring.

## Main results

* `TopologicalRing.bijective_restrictedPowerSeriesMap`: levelwise bijectivity of the coefficient
  reductions implies bijectivity of the induced map on restricted power series.
* `TopologicalRing.bijective_coefficientQuotientMap_adicCompletion`: the coefficient quotients
  of `R` and of its `J`-adic completion agree.
* `TopologicalRing.bijective_restrictedPowerSeriesMap_adicCompletion`: `R{σ} → R̂{σ}` is an
  isomorphism.
* `TopologicalRing.bijective_restrictedPowerSeriesMap_completedAway`: the same for the
  completion of a principal localization.

## Implementation notes

The isomorphism is not constructed: it is the canonical map `restrictedPowerSeriesMap`, which is
pinned down by its values on polynomials and on constants, and only its bijectivity is asserted.
The inverse of a level is taken as the inverse of a ring isomorphism obtained from the given
bijection, so no choice of data is involved.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public section

namespace TopologicalRing

section

universe u v

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Coefficient reduction commutes with the transition maps of the two inverse limits. -/
private theorem coefficientTransition_map_coefficientQuotientMap (I : Ideal A) (σ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (p : MvPolynomial σ (A ⧸ I ^ n)) :
    MvPolynomial.map (coefficientQuotientMap (B := B) I m)
        (RestrictedPowerSeries.coefficientTransition I σ hmn p) =
      RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn
        (MvPolynomial.map (coefficientQuotientMap (B := B) I n) p) := by
  rw [show RestrictedPowerSeries.coefficientTransition I σ hmn =
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn) from rfl,
    show RestrictedPowerSeries.coefficientTransition (I.map (algebraMap A B)) σ hmn =
      MvPolynomial.map (Ideal.Quotient.factorPow (I.map (algebraMap A B)) hmn) from rfl,
    MvPolynomial.map_map, MvPolynomial.map_map, factorPow_comp_coefficientQuotientMap I hmn]

/-- **Restricted power series see only the coefficient quotients.**  If every coefficient
reduction `A ⧸ I ^ n → B ⧸ (I · B) ^ n` is bijective, then the induced map `A{σ} → B{σ}` is an
isomorphism. -/
public theorem bijective_restrictedPowerSeriesMap (I : Ideal A) (σ : Type v)
    (h : ∀ n : ℕ, Function.Bijective (coefficientQuotientMap (B := B) I n)) :
    Function.Bijective (restrictedPowerSeriesMap (B := B) I σ) := by
  have hbij : ∀ n : ℕ,
      Function.Bijective (MvPolynomial.map (σ := σ) (coefficientQuotientMap (B := B) I n)) :=
    fun n => ⟨MvPolynomial.map_injective _ (h n).1, MvPolynomial.map_surjective _ (h n).2⟩
  let F : ∀ n : ℕ, MvPolynomial σ (A ⧸ I ^ n) ≃+*
      MvPolynomial σ (B ⧸ (I.map (algebraMap A B)) ^ n) :=
    fun n => RingEquiv.ofBijective _ (hbij n)
  have hF : ∀ (n : ℕ) (p : MvPolynomial σ (A ⧸ I ^ n)),
      F n p = MvPolynomial.map (coefficientQuotientMap (B := B) I n) p := fun _ _ => rfl
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · refine RestrictedPowerSeries.idealSystem_ext fun n => ?_
    exact (hbij n).1 <| congrArg (RestrictedPowerSeries.coefficientProjection _ σ n) hxy
  · refine ⟨⟨fun n => (F n).symm (y.val n), fun m n hmn => ?_⟩, ?_⟩
    · refine (F m).injective ?_
      rw [RingEquiv.apply_symm_apply, hF, coefficientTransition_map_coefficientQuotientMap,
        ← hF, RingEquiv.apply_symm_apply]
      exact y.property hmn
    · exact Subtype.ext (funext fun n => (F n).apply_symm_apply (y.val n))

end

section Completion

universe u v

variable {R : Type u} [CommRing R]

/-- The coefficient quotients of `R` and of its `J`-adic completion agree: the level `n`
evaluation inverts the reduction `R ⧸ J ^ n → R̂ ⧸ (J · R̂) ^ n`. -/
public theorem bijective_coefficientQuotientMap_adicCompletion (J : Ideal R) (hJ : J.FG)
    (n : ℕ) :
    Function.Bijective (coefficientQuotientMap (B := AdicCompletion J R) J n) := by
  let E : AdicCompletion J R ⧸ (J.map (algebraMap R (AdicCompletion J R))) ^ n →+* R ⧸ J ^ n :=
    Ideal.Quotient.lift _ (AdicCompletion.evalₐ J n).toRingHom fun b hb =>
      RingHom.mem_ker.mp (by rwa [AdicCompletion.ker_evalₐ J hJ n])
  have hEc : ∀ z : R ⧸ J ^ n, E (coefficientQuotientMap (B := AdicCompletion J R) J n z) = z := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    show E (Ideal.quotientMap _ (algebraMap R (AdicCompletion J R)) _
      (Ideal.Quotient.mk (J ^ n) x)) = _
    rw [Ideal.quotientMap_mk]
    show AdicCompletion.evalₐ J n (algebraMap R (AdicCompletion J R) x) = _
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rfl
  have hEinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).mpr fun w hw => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rwa [← AdicCompletion.ker_evalₐ J hJ n, RingHom.mem_ker]
  exact ⟨Function.LeftInverse.injective hEc, fun w => ⟨E w, hEinj (hEc (E w))⟩⟩

/-- **Restricted power series do not change when the coefficient ring is completed.**  For a
finitely generated ideal `J` of `R`, the canonical map from the restricted power series ring
over `R` to the one over the `J`-adic completion of `R` is an isomorphism. -/
public theorem bijective_restrictedPowerSeriesMap_adicCompletion (J : Ideal R) (hJ : J.FG)
    (σ : Type v) :
    Function.Bijective (restrictedPowerSeriesMap (B := AdicCompletion J R) J σ) :=
  bijective_restrictedPowerSeriesMap J σ
    (bijective_coefficientQuotientMap_adicCompletion J hJ)

/-- **Restricted power series over a completed principal localization.**  For a finitely
generated ideal `I` of `R` and an element `f`, the canonical map from the restricted power
series ring over the localization `R[1/f]` to the one over the completion of `R[1/f]` along the
extension of `I` is an isomorphism. -/
public theorem bijective_restrictedPowerSeriesMap_completedAway (I : Ideal R) (hI : I.FG)
    (f : R) (σ : Type v) :
    Function.Bijective (restrictedPowerSeriesMap
      (B := AdicCompletion (I.map (algebraMap R (Localization.Away f)))
        (Localization.Away f))
      (I.map (algebraMap R (Localization.Away f))) σ) :=
  bijective_restrictedPowerSeriesMap_adicCompletion _ (hI.map _) σ

end Completion

end TopologicalRing

end
