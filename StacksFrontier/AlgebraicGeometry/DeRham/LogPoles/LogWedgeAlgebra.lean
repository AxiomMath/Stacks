module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedgeResidue

/-!
# Associativity and unit of the wedge product of forms with logarithmic poles

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined. This file proves that the wedge product of forms with
logarithmic poles is associative and has the form `1` with no pole as a two-sided unit.

Both are checked on a chart with local equation `t` by multiplying by a power of `t`: a form with
logarithmic poles times `t` has no pole, `t φ = ι(φ(b₀))`, so after multiplying by `t³` (resp.
`t`) the identities become the identities of forms with no pole, and `t` is a nonzerodivisor on
the forms with logarithmic poles.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logFormsWedge_assoc`: `(φ ∧ ψ) ∧ χ = φ ∧ (ψ ∧ χ)`.
* `AlgebraicGeometry.Scheme.Hom.logFormsWedge_one_left`, `logFormsWedge_one_right`: `1 ∧ φ = φ`
  and `φ ∧ 1 = φ`.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}

/-- The wedge product of relative differential forms with no pole is associative:
`(κ ∧ ν) ∧ μ = κ ∧ (ν ∧ μ)`, up to the cast along `p + q + r = p + (q + r)`. -/
theorem formWedge_assoc (p q r : ℕ) (V : X.Opens) (κ : Γ(relativeDifferentialForms f (p : ℤ), V))
    (ν : Γ(relativeDifferentialForms f (q : ℤ), V))
    (μ : Γ(relativeDifferentialForms f (r : ℤ), V)) :
    formCast (Nat.add_assoc p q r) (formWedge f (p + q) r V (formWedge f p q V κ ν) μ) =
      formWedge f p (q + r) V κ (formWedge f q r V ν μ) := by
  refine totForm_injective (p + (q + r)) V ?_
  refine (totForm_formCast _ _).trans ?_
  refine ((totForm_formWedge (p + q) r V _ μ).trans ?_).trans (totForm_formWedge p (q
      + r) V κ _).symm
  refine (congrArg (· * totForm f r V μ) (totForm_formWedge p q V κ ν)).trans ?_
  refine (mul_assoc _ _ _).trans ?_
  exact congrArg (totForm f p V κ * ·) (totForm_formWedge q r V ν μ).symm

/-- The unit `1` of the relative forms over an open, a `0`-form. -/
abbrev formOne (V : X.Opens) : Γ(relativeDifferentialForms f ((0 : ℕ) : ℤ), V) :=
  (deRhamAlgebras f).exterior.one.eval (op V)

/-- The form `formOne V` is a left unit for the wedge product: `1 ∧ κ = κ`. -/
theorem formWedge_formOne_left (p : ℕ) (V : X.Opens)
    (κ : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    formCast (Nat.zero_add p) (formWedge f 0 p V (formOne V) κ) = κ := by
  refine totForm_injective p V ?_
  refine (totForm_formCast _ _).trans ?_
  refine (totForm_formWedge 0 p V _ κ).trans ?_
  exact (congrArg (· * totForm f p V κ)
    (AlgebraicGeometry.SheafOfModules.ofGradedForm_one (deRhamAlgebras f) (op V))).trans
    (one_mul _)

/-- The form `formOne V` is a right unit for the wedge product: `κ ∧ 1 = κ`. -/
theorem formWedge_formOne_right (p : ℕ) (V : X.Opens)
    (κ : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    formWedge f p 0 V κ (formOne V) = κ := by
  refine totForm_injective p V ?_
  refine (totForm_formWedge p 0 V κ _).trans ?_
  exact (congrArg (totForm f p V κ * ·)
    (AlgebraicGeometry.SheafOfModules.ofGradedForm_one (deRhamAlgebras f) (op V))).trans
    (mul_one _)

/-- The restriction of `formOne W` to an open `V ≤ W` is `formOne V`. -/
theorem formOne_res {V W : X.Opens} (h : V ≤ W) :
    (relativeDifferentialForms f ((0 : ℕ) : ℤ)).presheaf.map (homOfLE h).op (formOne W) =
      formOne (f := f) V :=
  (deRhamAlgebras f).exterior.one.2 (homOfLE h).op

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- Cancelling a power of the local equation on forms with logarithmic poles. -/
theorem logForms_eq_of_equationAt_smul_eq (hlog : f.HasLogPolesDeRhamComplex I) {V : X.Opens}
    (hV : V ≤ U) {p : ℕ}
    {χ χ' : (logPolesForms f I p).val.obj (op V)}
    (h : e.equationAtR hV • χ = e.equationAtR hV • χ') : χ = χ' := by
  have h3 : e.equationAtR hV • (χ - χ') = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (e.logForms_eq_zero_of_equationAt_smul_eq_zero hlog hV _ h3)

variable (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

include e in
/-- **Associativity on a chart.** -/
theorem logFormsWedge_assoc_of_le {p q r : ℕ} {V : X.Opens} (hV : V ≤ U)
    (φ : (logPolesForms f I p).val.obj (op V)) (ψ : (logPolesForms f I q).val.obj (op V))
    (χ : (logPolesForms f I r).val.obj (op V)) :
    logFormsCast (Nat.add_assoc p q r) (logFormsWedge hI hlog (logFormsWedge hI hlog φ ψ) χ) =
      logFormsWedge hI hlog φ (logFormsWedge hI hlog ψ χ) := by
  set t := e.equationAtR hV
  have hA : logFormsWedge hI hlog (logFormsWedge hI hlog (t • φ) (t • ψ)) (t • χ) =
      t • t • t • logFormsWedge hI hlog (logFormsWedge hI hlog φ ψ) χ := by
    simp only [logFormsWedge_smul_left, logFormsWedge_smul_right]
  have hB : logFormsWedge hI hlog (t • φ) (logFormsWedge hI hlog (t • ψ) (t • χ)) =
      t • t • t • logFormsWedge hI hlog φ (logFormsWedge hI hlog ψ χ) := by
    simp only [logFormsWedge_smul_left, logFormsWedge_smul_right]
  rw [e.equationAt_smul_eq_logPolesFormsInclusion hV φ,
    e.equationAt_smul_eq_logPolesFormsInclusion hV ψ,
    e.equationAt_smul_eq_logPolesFormsInclusion hV χ, logFormsWedge_logPolesFormsInclusion,
    logFormsWedge_logPolesFormsInclusion] at hA hB
  refine e.logForms_eq_of_equationAt_smul_eq hlog hV
    (e.logForms_eq_of_equationAt_smul_eq hlog hV (e.logForms_eq_of_equationAt_smul_eq hlog hV ?_))
  rw [← logFormsCast_smul, ← logFormsCast_smul, ← logFormsCast_smul, ← hA, ← hB,
    logFormsCast_logPolesFormsInclusion, formWedge_assoc]

include e in
/-- **The unit is a left unit, on a chart.** -/
theorem logFormsWedge_one_left_of_le {p : ℕ} {V : X.Opens} (hV : V ≤ U)
    (φ : (logPolesForms f I p).val.obj (op V)) :
    logFormsCast (Nat.zero_add p) (logFormsWedge hI hlog
      ((logPolesFormsInclusion f I 0).val.app (op V) (formOne V)) φ) = φ := by
  refine e.logForms_eq_of_equationAt_smul_eq hlog hV ?_
  rw [← logFormsCast_smul, ← logFormsWedge_smul_right,
    e.equationAt_smul_eq_logPolesFormsInclusion hV φ, logFormsWedge_logPolesFormsInclusion,
    logFormsCast_logPolesFormsInclusion, formWedge_formOne_left]

include e in
/-- **The unit is a right unit, on a chart.** -/
theorem logFormsWedge_one_right_of_le {p : ℕ} {V : X.Opens} (hV : V ≤ U)
    (φ : (logPolesForms f I p).val.obj (op V)) :
    logFormsWedge hI hlog φ ((logPolesFormsInclusion f I 0).val.app (op V) (formOne V)) = φ := by
  refine e.logForms_eq_of_equationAt_smul_eq hlog hV ?_
  rw [← logFormsWedge_smul_left, e.equationAt_smul_eq_logPolesFormsInclusion hV φ,
    logFormsWedge_logPolesFormsInclusion, formWedge_formOne_right]
  rfl

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- Two forms with logarithmic poles agree if they agree on `W ⊓ U` for every chart `U`. -/
private theorem logPolesForms_ext_of_trivialization
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) {p : ℕ} {W : X.Opens}
    {χ χ' : (logPolesForms f I p).val.obj (op W)}
    (h : ∀ {U : X.Opens}, Stacks.Divisors.IdealTrivialization I U →
      (logPolesForms f I p).val.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op χ =
        (logPolesForms f I p).val.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op χ') : χ = χ' := by
  refine logPolesForms_ext_of_local fun x hx => ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  exact ⟨W ⊓ Ux, inf_le_left, ⟨hx, hxU⟩, h e⟩

/-- **The wedge product of forms with logarithmic poles is associative.** -/
theorem logFormsWedge_assoc {p q r : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    (ψ : (logPolesForms f I q).val.obj (op W)) (χ : (logPolesForms f I r).val.obj (op W)) :
    logFormsCast (Nat.add_assoc p q r) (logFormsWedge hI hlog (logFormsWedge hI hlog φ ψ) χ) =
      logFormsWedge hI hlog φ (logFormsWedge hI hlog ψ χ) := by
  refine logPolesForms_ext_of_trivialization hI fun e => ?_
  rw [logFormsCast_map, ← logFormsWedge_res, ← logFormsWedge_res, ← logFormsWedge_res,
    ← logFormsWedge_res]
  exact e.logFormsWedge_assoc_of_le hI hlog inf_le_right _ _ _

/-- The unit of the forms with logarithmic poles over an open: the form `1` with no pole. -/
abbrev logFormsOne (W : X.Opens) : (logPolesForms f I 0).val.obj (op W) :=
  (logPolesFormsInclusion f I 0).val.app (op W) (formOne W)

/-- The restriction of `logFormsOne W` to an open `V ≤ W` is `logFormsOne V`. -/
theorem logFormsOne_res {V W : X.Opens} (h : V ≤ W) :
    (logPolesForms f I 0).val.map (homOfLE h).op (logFormsOne W) = logFormsOne (f := f)
    (I := I) V :=
  logEval_ext fun W' h' a => by
    rw [logEval_res, logEval_logPolesFormsInclusion, logEval_logPolesFormsInclusion, formOne_res,
      formOne_res]

/-- **The unit is a left unit for the wedge product.** -/
theorem logFormsWedge_one_left {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W)) :
    logFormsCast (Nat.zero_add p) (logFormsWedge hI hlog (logFormsOne W) φ) = φ := by
  refine logPolesForms_ext_of_trivialization hI fun e => ?_
  rw [logFormsCast_map, ← logFormsWedge_res, logFormsOne_res]
  exact e.logFormsWedge_one_left_of_le hI hlog inf_le_right _

/-- **The unit is a right unit for the wedge product.** -/
theorem logFormsWedge_one_right {p : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W)) :
    logFormsWedge hI hlog φ (logFormsOne W) = φ := by
  refine logPolesForms_ext_of_trivialization hI fun e => ?_
  rw [← logFormsWedge_res, logFormsOne_res]
  exact e.logFormsWedge_one_right_of_le hI hlog inf_le_right _

end AlgebraicGeometry.Scheme.Hom
