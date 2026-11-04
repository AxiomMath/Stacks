module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Examples.PolynomialRetract

/-!
# Nilpotents on every nonempty open of the polynomial retract

For the square-zero extension of a polynomial ring over an infinite field, every nonempty open
of its spectrum contains a rational closed point at which the square-zero ideal is still
nonzero after localizing.

The point is found by transporting the open across the homeomorphism of spectra to a nonempty
basic open of `Spec k[x]`, and choosing `α` where the defining polynomial does not vanish —
possible because the field is infinite. At the resulting point `x = α` the variable `y_α`
survives, which is detected by mapping to the dual numbers.

## Main definitions

* `AlgebraicGeometry.PolynomialRetract.evaluationPrime` is the prime of the extension ring
  obtained by evaluating the polynomial variable at a field element and killing the square-zero
  variables.

## Main results

* `exists_evaluationPrime_mem_and_projectionKernel_localization_ne_bot`: every nonempty open
  contains a point `evaluationPrime k α` at whose local ring the image of the square-zero ideal
  is nonzero.

## Implementation notes

The evaluation prime is the preimage under the retraction of `(x - α)`, so it is the point
denoted `P_α = J + (x - α)` in the source. The localized ideal is expressed as the image of the
retraction kernel under the localization map. The field is required to be infinite, as it is in
the source's proof.

## References

* [Stacks Project, Tag 01RQ](https://stacks.math.columbia.edu/tag/01RQ), Example 29.50.4
-/

@[expose] public section

namespace AlgebraicGeometry.PolynomialRetract

open Cardinal


variable (k : Type*) [Field k]

/-- Over an infinite field a nonzero polynomial in one variable is nonzero at some point. -/
private lemma exists_eval_ne_zero_of_nonzero_mvPolynomial (p : MvPolynomial Unit k)
    [Infinite k] (hp : p ≠ 0) : ∃ α : k, MvPolynomial.eval (fun _ : Unit => α) p ≠ 0 := by
  obtain ⟨α, hα⟩ := (MvPolynomial.uniqueAlgEquiv k Unit p).exists_eval_ne_zero_of_natDegree_lt_card
    ((EmbeddingLike.map_ne_zero_iff).2 hp) (natCast_lt_aleph0.trans_le (aleph0_le_mk k))
  exact ⟨α, by rwa [Polynomial.eval, MvPolynomial.eval₂_const_uniqueAlgEquiv] at hα⟩

/-- The ring map from the extension ring to the dual numbers `k[ε]` sending `x` to `α`, `y_α`
to `ε` and every other `y_a` to `0`. -/
private noncomputable def detectSquareZero (α : k) :
    extensionRing k →+* TrivSqZeroExt k k := by
  classical
  let φ : MvPolynomial (Unit ⊕ k) k →+* TrivSqZeroExt k k :=
    MvPolynomial.eval₂Hom (TrivSqZeroExt.inlHom k k) (fun i => match i with
      | Sum.inl _ => TrivSqZeroExt.inl α
      | Sum.inr a => if a = α then TrivSqZeroExt.inr (1 : k) else 0)
  refine Ideal.Quotient.lift (relationIdeal k) φ ?_
  change relationIdeal k ≤ RingHom.ker φ
  rw [relationIdeal]
  apply Ideal.span_le.2
  rintro f (hf | hf)
  · obtain ⟨a, rfl⟩ := hf
    by_cases ha : a = α <;> simp [φ, ha]
  · obtain ⟨⟨a, b⟩, rfl⟩ := hf
    by_cases ha : a = α <;> by_cases hb : b = α <;>
      simp [φ, ha, hb, TrivSqZeroExt.inr_mul_inr]

/-- Discarding the dual-number part of that evaluation leaves evaluation of the retraction
at `x = α`. -/
private lemma detectSquareZero_fst (α : k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (detectSquareZero k α) =
      (MvPolynomial.eval (fun _ : Unit => α)).comp (retractionMap k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext'
  · ext a
    simp [detectSquareZero, retractionMap]
  · intro i
    cases i with
    | inl u => simp [detectSquareZero, retractionMap]
    | inr a => by_cases ha : a = α <;> simp [detectSquareZero, retractionMap, ha]

/-- The dual-number generator stays nonzero in the localization of the dual numbers at the
kernel of their first projection. -/
private lemma algebraMap_detectSquareZero_ne_zero
    [((RingHom.ker ((TrivSqZeroExt.fstHom k k k).toRingHom)).IsPrime)] :
    algebraMap (TrivSqZeroExt k k)
      (Localization.AtPrime (RingHom.ker ((TrivSqZeroExt.fstHom k k k).toRingHom)))
      (TrivSqZeroExt.inr (1 : k)) ≠ 0 := by
  intro hzero
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
    (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom).primeCompl _ _).mp hzero
  exact s.2 (by simpa [TrivSqZeroExt.snd_mul] using congrArg TrivSqZeroExt.snd hs)

/-- The rational point of the extension ring over `x = α`. -/
noncomputable def evaluationPrime (α : k) : PrimeSpectrum (extensionRing k) :=
  ⟨RingHom.ker ((MvPolynomial.eval (fun _ : Unit => α)).comp (retractionMap k)),
    RingHom.ker_isPrime _⟩

/-- Every nonempty open of the spectrum of the extension ring contains a rational point
`evaluationPrime k α` at which the image of the square-zero ideal `projectionKernel k` in the
local ring is nonzero. -/
theorem exists_evaluationPrime_mem_and_projectionKernel_localization_ne_bot
    [Infinite k] (V : TopologicalSpace.Opens (PrimeSpectrum (extensionRing k)))
    (hV : (V : Set (PrimeSpectrum (extensionRing k))).Nonempty) :
    ∃ α : k, evaluationPrime k α ∈ V ∧
      Ideal.map (algebraMap (extensionRing k)
        (Localization.AtPrime (evaluationPrime k α).asIdeal))
        (projectionKernel k) ≠ ⊥ := by
  classical
  let H : PrimeSpectrum (extensionRing k) ≃ₜ PrimeSpectrum (baseRing k) :=
    (isHomeomorph_comap_inclusionMap k).homeomorph
  let W : Set (PrimeSpectrum (baseRing k)) := H '' (V : Set (PrimeSpectrum (extensionRing k)))
  have hWopen : IsOpen W := H.isOpenMap _ V.isOpen
  obtain ⟨p, hpV⟩ := hV
  have hpW : H p ∈ W := ⟨p, hpV, rfl⟩
  obtain ⟨U, hgW, hgPoint, hgSub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hWopen (H p) hpW
  obtain ⟨g, rfl⟩ := hgW
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hgPoint
  obtain ⟨α, hα⟩ := exists_eval_ne_zero_of_nonzero_mvPolynomial (k := k) g hg0
  let qα : PrimeSpectrum (baseRing k) :=
    ⟨RingHom.ker (MvPolynomial.eval (fun _ : Unit => α)), RingHom.ker_isPrime _⟩
  have hqα : qα ∈ PrimeSpectrum.basicOpen g := by
    simpa [qα, PrimeSpectrum.mem_basicOpen, RingHom.mem_ker] using hα
  have hqαW : qα ∈ W := hgSub hqα
  obtain ⟨pα, hpαV, hpαeq⟩ := hqαW
  have hHα : H (evaluationPrime k α) = qα := by
    apply PrimeSpectrum.ext
    show Ideal.comap (inclusionMap k) (evaluationPrime k α).asIdeal = qα.asIdeal
    apply Ideal.ext
    intro a
    show inclusionMap k a ∈ RingHom.ker
        ((MvPolynomial.eval (fun _ : Unit => α)).comp (retractionMap k)) ↔
      a ∈ RingHom.ker (MvPolynomial.eval (fun _ : Unit => α))
    have hc : (retractionMap k) (inclusionMap k a) = a :=
      RingHom.congr_fun (retractionMap_comp_inclusionMap k) a
    rw [RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, hc]
  obtain rfl : pα = evaluationPrime k α := H.injective (hpαeq.trans hHα.symm)
  refine ⟨α, hpαV, ?_⟩
  let P : Ideal (extensionRing k) := (evaluationPrime k α).asIdeal
  let Q : Ideal (TrivSqZeroExt k k) :=
    RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom
  let δ : extensionRing k →+* TrivSqZeroExt k k := detectSquareZero k α
  have hP : P = RingHom.ker
      ((MvPolynomial.eval (fun _ : Unit => α)).comp (retractionMap k)) := rfl
  have : Q.IsPrime := RingHom.ker_isPrime _
  have hcompl : P.primeCompl ≤ Q.primeCompl.comap δ := by
    intro s hs
    change (s : extensionRing k) ∉ P at hs
    show δ s ∉ Q
    show (TrivSqZeroExt.fstHom k k k).toRingHom (δ s) ≠ 0
    rw [hP, ← detectSquareZero_fst] at hs
    simpa [RingHom.mem_ker, RingHom.comp_apply] using hs
  let locMap : Localization.AtPrime P →+* Localization.AtPrime Q :=
    IsLocalization.map (M := P.primeCompl) (T := Q.primeCompl)
      (Localization.AtPrime Q) δ hcompl
  let y : extensionRing k := Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X (Sum.inr α))
  have hyP : y ∈ projectionKernel k := by
    show retractionMap k y = 0
    simp [y, retractionMap]
  have hδy : δ y = TrivSqZeroExt.inr (1 : k) := by
    simp [y, δ, detectSquareZero]
  have hyLocal : algebraMap (extensionRing k) (Localization.AtPrime P) y ≠ 0 := fun hy0 =>
    algebraMap_detectSquareZero_ne_zero (k := k)
      (show algebraMap _ (Localization.AtPrime Q) (TrivSqZeroExt.inr (1 : k)) = 0 by
        simpa [locMap, hδy] using congrArg locMap hy0)
  intro hbot
  have hymap := Ideal.mem_map_of_mem (algebraMap _ (Localization.AtPrime P)) hyP
  exact hyLocal (by rwa [hbot, Ideal.mem_bot] at hymap)

end AlgebraicGeometry.PolynomialRetract
