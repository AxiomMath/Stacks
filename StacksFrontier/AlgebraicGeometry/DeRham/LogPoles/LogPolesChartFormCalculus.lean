module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles

/-!
# Calculus of the local presentation `ω + dlog t ∧ η` of forms with logarithmic poles

Over an open `U` on which the ideal sheaf of an effective Cartier divisor `Y ⊆ X` is trivialized,
with local equation `t`, every form with logarithmic poles is locally of the form
`ω + dlog t ∧ η`
(`Stacks.Divisors.IdealTrivialization.logPolesChartForm`, Stacks Tag 0FMW). This file records how
that presentation behaves under the operations the morphisms of short exact sequences in the proof
of Stacks Tag 0FUQ are checked with: it is additive and `𝒪_X`-linear in the pair `(ω, η)`, it
commutes with restriction, and under a change of local equation `t = w t'` it transforms by
`dlog t = dlog w + dlog t'`.

## Main results

* `Stacks.Divisors.IdealTrivialization.logPolesChartForm_add`,
  `Stacks.Divisors.IdealTrivialization.logPolesChartForm_smul`: linearity.
* `Stacks.Divisors.IdealTrivialization.logPolesChartForm_res`: restriction.
* `Stacks.Divisors.IdealTrivialization.logPolesChartForm_eq_of_equationAt_eq_mul`: **change of
  chart.**

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- The values of `ω + dlog t ∧ η`: at a local section `a` of the ideal sheaf, the coordinate of
`a` times `t ω + dt ∧ η`. -/
theorem logEval_logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) {W' : X.Opens} (h : W' ≤ W)
    (a : (negativeTwist I).val.obj (op W')) :
    logEval f I (e.logPolesChartForm hW ω η) h a =
      e.coordLE (h.trans hW) a • (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE h).op (e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) η) :=
  rfl

/-- `ω + dlog t ∧ η` is additive in the pair `(ω, η)`. -/
theorem logPolesChartForm_add {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω ω' : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η η' : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    e.logPolesChartForm hW (ω + ω') (η + η') =
      e.logPolesChartForm hW ω η + e.logPolesChartForm hW ω' η' := by
  refine logEval_ext fun W' h a => ?_
  rw [logEval_add, logEval_logPolesChartForm, logEval_logPolesChartForm,
    logEval_logPolesChartForm, ← smul_add, ← map_add]
  congr 2
  rw [smul_add, exactWedge_add_right]
  abel

/-- `ω + dlog t ∧ η` is `𝒪_X`-linear in the pair `(ω, η)`. -/
theorem logPolesChartForm_smul {p : ℕ} {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W))
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    e.logPolesChartForm hW (r • ω) (r • η) =
      (show X.ringCatSheaf.obj.obj (op W) from r) • e.logPolesChartForm hW ω η := by
  refine logEval_ext fun W' h a => ?_
  have hz : e.equationAt hW • (r • ω) + exactWedge f p W (e.equationAt hW) (r • η) =
      r • (e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) η) := by
    rw [smul_add, exactWedge_smul_right, smul_comm]
  rw [logEval_smul_left, logEval_logPolesChartForm, logEval_logPolesChartForm, hz,
    forms_map_smul, smul_comm]

/-- `ω + dlog t ∧ η` commutes with restriction to smaller opens. -/
theorem logPolesChartForm_res {p : ℕ} {W W₁ : X.Opens} (hW : W ≤ U) (h₁ : W₁ ≤ W)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    (logPolesForms f I (p + 1)).val.map (homOfLE h₁).op (e.logPolesChartForm hW ω η) =
      e.logPolesChartForm (h₁.trans hW)
        ((relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h₁).op ω)
        ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h₁).op η) := by
  refine logEval_ext fun W' h a => ?_
  rw [logEval_res, logEval_logPolesChartForm, logEval_logPolesChartForm, ← forms_map_map h₁ h]
  congr 2
  rw [map_add, forms_map_smul, exactWedge_res, e.equationAt_res hW h₁]

/-- **Change of chart.** If the local equations of two trivializations over a common open `W`
are related by `t = w t'`, with `v w = 1`, then
`ω + dlog t ∧ η = (ω + v dw ∧ η) + dlog t' ∧ η`, i.e. `dlog t = dlog w + dlog t'`. -/
theorem logPolesChartForm_eq_of_equationAt_eq_mul {U' : X.Opens} (e' : IdealTrivialization I U')
    {p : ℕ} {W : X.Opens} (hW : W ≤ U) (hW' : W ≤ U') (v w : Γ(X, W))
    (ht : e.equationAt hW = w * e'.equationAt hW') (hvw : v * w = 1)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    e.logPolesChartForm hW ω η =
      e'.logPolesChartForm hW' (ω + v • exactWedge f p W w η) η := by
  have hcoord : e.coordLE hW (e'.basisLE hW') = v := by
    have h1 := e.negativeTwistSection_eq_mul hW (e'.basisLE hW')
    change e'.equationAt hW' = _ at h1
    rw [ht, ← mul_assoc] at h1
    have h2 : (e.coordLE hW (e'.basisLE hW') * w - 1) * e'.equationAt hW' = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    linear_combination v * sub_eq_zero.mp (e'.mul_equationAt_eq_zero hW' _ h2) -
      e.coordLE hW (e'.basisLE hW') * hvw
  rw [← e'.logOfCoord_logEval_basisLE hW' (e.logPolesChartForm hW ω η)]
  refine e'.logOfCoord_congr hW' ?_ _ _
  rw [logEval_logPolesChartForm, hcoord, forms_map_refl, ht, exactWedge_mul_left, smul_add,
    smul_add, smul_smul, smul_smul, smul_smul, ← mul_assoc, hvw, one_mul, one_smul, smul_add,
    smul_smul, mul_comm (e'.equationAt hW') v]
  abel

end Stacks.Divisors.IdealTrivialization
