module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedge

/-!
# The Leibniz rule for the wedge product of forms with logarithmic poles

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined. This file proves that the wedge product of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogWedge` and the differential of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogDifferential` satisfy the graded Leibniz rule

`d(φ ∧ ψ) = dφ ∧ ψ + (-1)^p φ ∧ dψ`

of [Stacks, Tag 0FUP] (1).

The identity is checked on a chart with local equation `t`, at the basis element `b₀`. There each
of `dφ`, `dψ`, `φ ∧ ψ`, `d(φ ∧ ψ)`, `dφ ∧ ψ` and `φ ∧ dψ` is determined by its value at `b₀`, and
that value is characterised by an equation after multiplying by `t`
(`Stacks.Divisors.IdealTrivialization.equationAt_smul_logEval_logD`,
`equationAt_smul_logEval_logFormsWedge`). Combined with the Leibniz rule for forms with no pole,
these equations give `t³ d(φ ∧ ψ)(b₀) = t³ (dφ ∧ ψ + (-1)^p φ ∧ dψ)(b₀)` in the ring of all local
forms (`Stacks.LogPoles.leibniz_algebra`), and `t` is a nonzerodivisor on the forms.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logFormsCast`: a form with logarithmic poles read in another,
  equal, degree.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logD_logFormsWedge`: **the Leibniz rule**.
* `Stacks.Divisors.IdealTrivialization.map_eq_of_logEval_basisLE`: on a chart, a form with
  logarithmic poles is determined by its value at the basis element.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul AlgebraicGeometry.SheafOfModules.gradedFormsGRing

universe u

namespace Stacks.LogPoles

/-- The ring identity behind the Leibniz rule for the wedge product of forms with logarithmic
poles. On a chart with local equation `t` (here `s`, read in the ring of all forms, and `d = dt`),
the values at the basis element of `dφ`, `dψ`, `φ ∧ ψ`, `d(φ ∧ ψ)`, `dφ ∧ ψ` and `φ ∧ dψ` are
`K'`, `L'`, `M`, `M'`, `N₁` and `N₂`, each characterised by an equation after multiplying by `s`;
then `s³ M' = s³ (N₁ + ε N₂)`, `ε = (-1)^p`. -/
theorem leibniz_algebra {R : Type*} [Ring R]
    (s d K L DK DL K' L' M M' N₁ N₂ DM DKL : R) (ε : ℤ) (hε : ε * ε = 1)
    (hsd : s * d = d * s) (hsK : s * K = K * s) (hKd : K * d = ε • (d * K))
    (hK' : s * K' = s * DK - d * K) (hL' : s * L' = s * DL - d * L)
    (hM : s * M = K * L) (hDKL : DKL = d * M + s * DM) (hlf : DKL = DK * L + ε • (K * DL))
    (hM' : s * M' = s * DM - d * M) (hN₁ : s * N₁ = K' * L) (hN₂ : s * N₂ = K * L') :
    s * (s * (s * M')) = s * (s * (s * (N₁ + ε • N₂))) := by
  have hsDM : s * DM = DKL - d * M := by rw [hDKL]; abel
  have hsdM : s * (d * M) = d * (K * L) := by rw [← mul_assoc, hsd, mul_assoc, hM]
  have lhs : s * (s * (s * M')) = s * (s * DKL) - (s * (d * (K * L)) + s * (d * (K * L))) := by
    rw [hM', mul_sub, hsDM, mul_sub, mul_sub, hsdM]; noncomm_ring
  have r1 : s * (s * (s * N₁)) = s * (s * (DK * L)) - s * (d * (K * L)) := by
    rw [hN₁, ← mul_assoc s K', hK']; noncomm_ring
  have hKs : ∀ x, K * (s * x) = s * (K * x) := fun x => by rw [← mul_assoc, ← hsK, mul_assoc]
  have r2 : s * (s * (s * N₂)) = s * (s * (K * DL)) - ε • (s * (d * (K * L))) := by
    rw [hN₂, ← mul_assoc s K L', hsK, mul_assoc, hL', mul_sub, mul_sub, hKs, ← mul_assoc K d L, hKd,
      smul_mul_assoc, mul_smul_comm, mul_assoc]
  have rhs : s * (s * (s * (N₁ + ε • N₂))) = s * (s * (s * N₁)) + ε • (s * (s * (s * N₂))) := by
    rw [mul_add, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm]
  rw [lhs, rhs, r1, r2, hlf, smul_sub, smul_smul, hε, one_smul, mul_add, mul_add, mul_smul_comm,
    mul_smul_comm]
  abel

/-- `s³ (a - b) = 0` once `s³ a = s³ b`. -/
theorem mul_mul_mul_sub_eq_zero {R : Type*} [Ring R] (s a b : R)
    (h : s * (s * (s * a)) = s * (s * (s * b))) : s * (s * (s * (a - b))) = 0 := by
  rw [mul_sub, mul_sub, mul_sub, h, sub_self]

end Stacks.LogPoles

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}

/-- A form with logarithmic poles, read in another, equal, degree. -/
abbrev logFormsCast {m n : ℕ} (h : m = n) {W : X.Opens}
    (φ : (logPolesForms f I m).val.obj (op W)) : (logPolesForms f I n).val.obj (op W) :=
  _root_.SheafOfModules.gradedCast (fun k => (logPolesForms f I k).val.obj (op W)) h φ

/-- Reading a form with logarithmic poles in an equal degree does not change its value at a local
section, as an element of the ring of all forms. -/
theorem totForm_logEval_logFormsCast {m n : ℕ} (h : m = n) {W : X.Opens}
    (φ : (logPolesForms f I m).val.obj (op W)) {W' : X.Opens} (hW' : W' ≤ W)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    totForm f n W' (logEval f I (logFormsCast h φ) hW' a)
        = totForm f m W' (logEval f I φ hW' a) := by
  subst h
  rfl

/-- Reading a form with logarithmic poles in an equal degree commutes with scalar
multiplication. -/
theorem logFormsCast_smul {m n : ℕ} (h : m = n) {W : X.Opens} (r : X.ringCatSheaf.obj.obj (op W))
    (φ : (logPolesForms f I m).val.obj (op W)) :
    logFormsCast h (r • φ) = r • logFormsCast h φ := by
  subst h
  rfl

/-- Reading a form with logarithmic poles in an equal degree commutes with subtraction. -/
theorem logFormsCast_sub {m n : ℕ} (h : m = n) {W : X.Opens}
    (φ ψ : (logPolesForms f I m).val.obj (op W)) :
    logFormsCast h (φ - ψ) = logFormsCast h φ - logFormsCast h ψ := by
  subst h
  rfl

/-- Reading a form with logarithmic poles in an equal degree commutes with restriction. -/
theorem logFormsCast_map {m n : ℕ} (h : m = n) {W V : X.Opens} (hV : V ≤ W)
    (φ : (logPolesForms f I m).val.obj (op W)) :
    (logPolesForms f I n).val.map (homOfLE hV).op (logFormsCast h φ) =
      logFormsCast h ((logPolesForms f I m).val.map (homOfLE hV).op φ) := by
  subst h
  rfl

/-- Reading in an equal degree commutes with the inclusion of forms with no pole into forms with
logarithmic poles. -/
theorem logFormsCast_logPolesFormsInclusion {m n : ℕ} (h : m = n) {W : X.Opens}
    (x : Γ(relativeDifferentialForms f (m : ℤ), W)) :
    logFormsCast h ((logPolesFormsInclusion f I m).val.app (op W) x) =
      (logPolesFormsInclusion f I n).val.app (op W) (formCast h x) := by
  subst h
  rfl

/-- A form with logarithmic poles read in an equal degree is heterogeneously equal to itself. -/
theorem logFormsCast_heq {m n : ℕ} (h : m = n) {W : X.Opens}
    (φ : (logPolesForms f I m).val.obj (op W)) : logFormsCast h φ ≍ φ := by
  subst h
  rfl

/-- Evaluation at a local section of the ideal sheaf, as an additive map. -/
def logEvalHom {p : ℕ} {W : X.Opens} {W' : X.Opens} (hW' : W' ≤ W)
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    (logPolesForms f I p).val.obj (op W) →+ Γ(relativeDifferentialForms f (p : ℤ), W') :=
  AddMonoidHom.mk' (fun φ => logEval f I φ hW' a) fun φ ψ => logEval_add φ ψ hW' a

/-- Evaluation at a local section of the ideal sheaf commutes with integer multiples. -/
theorem logEval_zsmul {p : ℕ} {W : X.Opens} (k : ℤ) (φ : (logPolesForms f I p).val.obj (op W))
    {W' : X.Opens} (hW' : W' ≤ W) (a : (Stacks.Divisors.negativeTwist I).val.obj (op W')) :
    logEval f I (k • φ) hW' a = k • logEval f I φ hW' a :=
  map_zsmul (logEvalHom hW' a) k φ

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- Cancelling the local equation on forms. -/
theorem eq_of_equationAt_smul_eq (hlog : f.HasLogPolesDeRhamComplex I) {W : X.Opens} (hW : W ≤ U)
    {n : ℕ} {x y : Γ(relativeDifferentialForms f (n : ℤ), W)}
    (h : e.equationAt hW • x = e.equationAt hW • y) : x = y := by
  have h3 : e.equationAt hW • (x - y) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (e.eq_zero_of_equationAt_smul_eq_zero hlog hW n _ h3)

/-- On a chart, a form with logarithmic poles is determined by its value at the basis element. -/
theorem map_eq_of_logEval_basisLE {p : ℕ} {W : X.Opens}
    {χ χ' : (logPolesForms f I p).val.obj (op W)} {V : X.Opens} (hVW : V ≤ W) (hVU : V ≤ U)
    (h : logEval f I χ hVW (e.basisLE hVU) = logEval f I χ' hVW (e.basisLE hVU)) :
    (logPolesForms f I p).val.map (homOfLE hVW).op χ =
      (logPolesForms f I p).val.map (homOfLE hVW).op χ' := by
  refine logEval_ext fun W' h' a => ?_
  rw [logEval_res, logEval_res, e.logEval_eq_coord_smul χ _ (h'.trans hVU),
    e.logEval_eq_coord_smul χ' _ (h'.trans hVU), e.logEval_basisLE_res χ hVW hVU h',
    e.logEval_basisLE_res χ' hVW hVU h', h]

variable (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **The value of `dφ` at the basis element of a chart**: `t (dφ)(b₀) = t dκ - dt ∧ κ` for
`κ = φ(b₀)`; this is `t d(t⁻¹ κ)`. -/
theorem equationAt_smul_logEval_logD {p : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I p).val.obj (op W)) {V : X.Opens} (hVW : V ≤ W) (hVU : V ≤ U) :
    e.equationAt hVU • logEval f I (logD hI hlog φ) hVW (e.basisLE hVU) =
      e.equationAt hVU • deRhamD f p V (logEval f I φ hVW (e.basisLE hVU)) -
        exactWedge f p V (e.equationAt hVU) (logEval f I φ hVW (e.basisLE hVU)) := by
  have h := leibnizRel_logDValue hI hlog φ hVW (e.basisLE hVU) V le_rfl (e.basisLE hVU)
  rw [forms_map_refl, leibnizRHS, idealRes_refl] at h
  exact h

/-- **The value of `φ ∧ ψ` at the basis element of a chart**: `t (φ ∧ ψ)(b₀) = φ(b₀) ∧ ψ(b₀)`. -/
theorem equationAt_smul_logEval_logFormsWedge {p q : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I p).val.obj (op W)) (ψ : (logPolesForms f I q).val.obj (op W))
    {V : X.Opens} (hVW : V ≤ W) (hVU : V ≤ U) :
    e.equationAt hVU • logEval f I (logFormsWedge hI hlog φ ψ) hVW (e.basisLE hVU) =
      formWedge f p q V (logEval f I φ hVW (e.basisLE hVU))
          (logEval f I ψ hVW (e.basisLE hVU)) := by
  have h := wedgeRel_logWedgeValue hI hlog φ ψ hVW (e.basisLE hVU) V le_rfl (e.basisLE hVU)
  rw [forms_map_refl, wedgeRHS, idealRes_refl] at h
  exact h

/-- **The Leibniz rule on a chart**, read at the basis element. -/
theorem logEval_logD_logFormsWedge {p q : ℕ} {W : X.Opens}
    (φ : (logPolesForms f I p).val.obj (op W)) (ψ : (logPolesForms f I q).val.obj (op W))
    {V : X.Opens} (hVW : V ≤ W) (hVU : V ≤ U) :
    logEval f I (logD hI hlog (logFormsWedge hI hlog φ ψ)) hVW (e.basisLE hVU) =
      logEval f I (logFormsCast (Nat.add_right_comm p 1 q)
          (logFormsWedge hI hlog (logD hI hlog φ) ψ)) hVW (e.basisLE hVU) +
        ((-1 : ℤ) ^ p) • logEval f I (logFormsWedge hI hlog φ (logD hI hlog ψ)) hVW
          (e.basisLE hVU) := by
  let b₀ := e.basisLE hVU
  let t := e.equationAt hVU
  let K := logEval f I φ hVW b₀
  let L := logEval f I ψ hVW b₀
  let K' := logEval f I (logD hI hlog φ) hVW b₀
  let L' := logEval f I (logD hI hlog ψ) hVW b₀
  let M := logEval f I (logFormsWedge hI hlog φ ψ) hVW b₀
  let M' := logEval f I (logD hI hlog (logFormsWedge hI hlog φ ψ)) hVW b₀
  let N₁ := logEval f I (logFormsWedge hI hlog (logD hI hlog φ) ψ) hVW b₀
  let N₂ := logEval f I (logFormsWedge hI hlog φ (logD hI hlog ψ)) hVW b₀
  let B := logEval f I (logFormsCast (Nat.add_right_comm p 1 q)
      (logFormsWedge hI hlog (logD hI hlog φ) ψ)) hVW b₀ + ((-1 : ℤ) ^ p) • N₂
  have hD : ∀ {n : ℕ} (χ : (logPolesForms f I n).val.obj (op W)),
      totScalar f V t * totForm f (n + 1) V (logEval f I (logD hI hlog χ) hVW b₀) =
        totScalar f V t * totForm f (n + 1) V (deRhamD f n V (logEval f I χ hVW b₀)) -
          totExact f V t * totForm f n V (logEval f I χ hVW b₀) := fun {n} χ =>
    (totForm_smul (n + 1) V t _).symm.trans
      ((congrArg (totForm f (n + 1) V) (e.equationAt_smul_logEval_logD hI hlog χ hVW hVU)).trans
        ((map_sub (totForm f (n + 1) V) _ _).trans
          (congrArg₂ (· - ·) (totForm_smul (n + 1) V t _) (totForm_exactWedge n V t _))))
  have hW : ∀ {m n : ℕ} (χ : (logPolesForms f I m).val.obj (op W))
      (ω : (logPolesForms f I n).val.obj (op W)),
      totScalar f V t * totForm f (m + n) V (logEval f I (logFormsWedge hI hlog χ ω) hVW b₀) =
        totForm f m V (logEval f I χ hVW b₀) * totForm f n V (logEval f I ω hVW b₀) :=
    fun {m n} χ ω => (totForm_smul (m + n) V t _).symm.trans
      ((congrArg (totForm f (m + n) V)
        (e.equationAt_smul_logEval_logFormsWedge hI hlog χ ω hVW hVU)).trans
        (totForm_formWedge m n V _ _))
  have hMf : t • M = formWedge f p q V K L :=
    e.equationAt_smul_logEval_logFormsWedge hI hlog φ ψ hVW hVU
  have hDKL : totForm f (p + q + 1) V (deRhamD f (p + q) V (t • M)) =
      totExact f V t * totForm f (p + q) V M +
        totScalar f V t * totForm f (p + q + 1) V (deRhamD f (p + q) V M) :=
    totForm_deRhamD_smul (p + q) V t M
  have hlf : totForm f (p + q + 1) V (deRhamD f (p + q) V (t • M)) =
      totForm f (p + 1) V (deRhamD f p V K) * totForm f q V L +
        ((-1 : ℤ) ^ p) • (totForm f p V K * totForm f (q + 1) V (deRhamD f q V L)) :=
    (congrArg (fun z => totForm f (p + q + 1) V (deRhamD f (p + q) V z)) hMf).trans
      (totForm_deRhamD_formWedge p q V K L)
  have hε : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by rw [← mul_pow]; simp
  have key := Stacks.LogPoles.leibniz_algebra
    (R := AlgebraicGeometry.SheafOfModules.totalForms
      (AlgebraicGeometry.SheafOfModules.differentialAlgebras (inverseImageStructureMap f)) (op V))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hε (totScalar_mul_totExact_comm V t t)
        (totScalar_mul_comm V t p K)
    (totForm_mul_totExact p V K t) (hD φ) (hD ψ) (hW φ ψ) hDKL hlf (hD (logFormsWedge hI hlog φ ψ))
      (hW (logD hI hlog φ) ψ) (hW φ (logD hI hlog ψ))
  have hB : totForm f (p + q + 1) V B =
      totForm f (p + 1 + q) V N₁ + ((-1 : ℤ) ^ p) • totForm f (p + (q + 1)) V N₂ :=
    (map_add (totForm f (p + q + 1) V) _ _).trans (congrArg₂ (· + ·)
      (totForm_logEval_logFormsCast (Nat.add_right_comm p 1 q) _ hVW b₀)
      (map_zsmul (totForm f (p + q + 1) V) _ _))
  have h3 : t • t • t • (M' - B) = 0 := by
    refine totForm_injective (p + q + 1) V
      (((totForm_smul (p + q + 1) V t _).trans (congrArg (totScalar f V t * ·)
        ((totForm_smul (p + q + 1) V t _).trans (congrArg (totScalar f V t * ·)
          ((totForm_smul (p + q + 1) V t _).trans (congrArg (totScalar f V t * ·)
            (map_sub (totForm f (p + q + 1) V) _ _))))))).trans
        ((Stacks.LogPoles.mul_mul_mul_sub_eq_zero _ _ _ (key.trans (by rw [hB]))).trans
          (map_zero _).symm))
  exact sub_eq_zero.mp (e.eq_zero_of_equationAt_smul_eq_zero hlog hVU (p + q + 1) _
    (e.eq_zero_of_equationAt_smul_eq_zero hlog hVU (p + q + 1) _
      (e.eq_zero_of_equationAt_smul_eq_zero hlog hVU (p + q + 1) _ h3)))

end Stacks.Divisors.IdealTrivialization

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- **The Leibniz rule for the wedge product of forms with logarithmic poles**:
`d(φ ∧ ψ) = dφ ∧ ψ + (-1)^p φ ∧ dψ`, the first summand read in degree `p + q + 1`. -/
theorem logD_logFormsWedge {p q : ℕ} {W : X.Opens} (φ : (logPolesForms f I p).val.obj (op W))
    (ψ : (logPolesForms f I q).val.obj (op W)) :
    logD hI hlog (logFormsWedge hI hlog φ ψ) =
      logFormsCast (Nat.add_right_comm p 1 q) (logFormsWedge hI hlog (logD hI hlog φ) ψ) +
        ((-1 : ℤ) ^ p) • logFormsWedge hI hlog φ (logD hI hlog ψ) := by
  refine logPolesForms_ext_of_local fun x hx => ?_
  obtain ⟨Ux, hxU, ⟨e⟩⟩ := Stacks.Divisors.IdealTrivialization.exists_mem_nonempty hI x
  refine ⟨W ⊓ Ux, inf_le_left, ⟨hx, hxU⟩,
    e.map_eq_of_logEval_basisLE inf_le_left inf_le_right ?_⟩
  rw [logEval_add, logEval_zsmul]
  exact e.logEval_logD_logFormsWedge hI hlog φ ψ inf_le_left inf_le_right

end AlgebraicGeometry.Scheme.Hom
