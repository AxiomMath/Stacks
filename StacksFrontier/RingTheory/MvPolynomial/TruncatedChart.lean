module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The truncated chart of a node: `(us − vt) + (s,t)ⁿ` against `(tⁿ)`

Let `S` be a commutative ring and `u, v : S` with `u` a *unit*. This file proves

`S[s,t] ⧸ ((us − vt) + (s,t)ⁿ) ≃ₐ[S] S[t] ⧸ (tⁿ)`,

which is the change of variables `s ↦ s + (v/u)t`: it carries `us − vt` to `us`, hence — `u`
being a unit — to `s`, and it leaves the ideal `(s,t)` alone. Here it is not run as an
automorphism of `S[s,t]` but as a pair of mutually inverse maps between the two quotients:
`s ↦ (v/u)t`, `t ↦ t` one way and `t ↦ t` the other.

The hypothesis on `u` is recorded as an explicit inverse `w` with `w·u = 1` rather than as
`IsUnit u`, so that the maps below are honest terms and not choices extracted from an existence
statement.

Nothing here truncates a power series: `S[s,t]` is a polynomial ring throughout. That is the
point of combining this with
`Stacks.MvPowerSeries.RegularParameters.polynomialTruncationEquiv`, where a power series ring
modulo a power of its ideal of variables is identified with the polynomial ring modulo the same.

## Main definitions

* `Stacks.TruncatedChart.chartIdeal` — the ideal `(us − vt) + (s,t)ⁿ` of `S[s,t]`.
* `Stacks.TruncatedChart.truncPoly` — the ring `S[t] ⧸ (tⁿ)`, with `Stacks.TruncatedChart.truncT`
  the image of `t` in it.
* `Stacks.TruncatedChart.chartEquiv` — the isomorphism.
* `Stacks.TruncatedChart.chartEquivSwap` — its twin for `v` a unit, which eliminates `t` instead
  of `s`, obtained from `chartEquiv` by interchanging the two variables.

## Main results

* `Stacks.TruncatedChart.X_zero_sub_mem_chartIdeal` — `s = (v/u)t` modulo `chartIdeal`, which is
  the change of variables and the only place the inverse of `u` is used.
* `Stacks.TruncatedChart.map_chartIdeal_renameEquiv_swap` — swapping the two variables carries
  `chartIdeal u v n` to `chartIdeal v u n`, which is why the twin needs no separate proof.
-/

@[expose] public section

namespace Stacks.TruncatedChart

variable {S : Type*} [CommRing S]

/-! ### The ideal and the two rings -/

/-- `Fin 2` has exactly the two elements `0` and `1`. -/
theorem eq_zero_or_eq_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

/-- The ideal `(u·s − v·t) + (s,t)ⁿ` of `S[s,t]`, with `s = X 0` and `t = X 1`. -/
noncomputable def chartIdeal (u v : S) (n : ℕ) : Ideal (MvPolynomial (Fin 2) S) :=
  Ideal.span {MvPolynomial.C u * MvPolynomial.X 0 - MvPolynomial.C v * MvPolynomial.X 1} ⊔
    Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S)) ^ n

/-- The ideal `(s,t)ⁿ` is contained in `chartIdeal u v n`. -/
theorem span_range_X_pow_le_chartIdeal (u v : S) (n : ℕ) :
    Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S)) ^ n ≤
      chartIdeal u v n := by
  unfold chartIdeal
  exact le_sup_right

/-- The relation `u·s − v·t` lies in `chartIdeal u v n`. -/
theorem relation_mem_chartIdeal (u v : S) (n : ℕ) :
    MvPolynomial.C u * MvPolynomial.X 0 - MvPolynomial.C v * MvPolynomial.X 1 ∈
      chartIdeal u v n := by
  unfold chartIdeal
  exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)

/-- **The change of variables**: if `w·u = 1`, then modulo `chartIdeal u v n` the variable `s` is
`(v·w)·t`. This is the one step that uses the invertibility of `u`. -/
theorem X_zero_sub_mem_chartIdeal {u v w : S} (hw : w * u = 1) (n : ℕ) :
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) S) -
        MvPolynomial.C (v * w) * MvPolynomial.X 1 ∈ chartIdeal u v n := by
  have hrw : (MvPolynomial.X 0 : MvPolynomial (Fin 2) S) -
      MvPolynomial.C (v * w) * MvPolynomial.X 1 =
      MvPolynomial.C w *
        (MvPolynomial.C u * MvPolynomial.X 0 - MvPolynomial.C v * MvPolynomial.X 1) := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc, ← MvPolynomial.C_mul, ← MvPolynomial.C_mul, hw,
      MvPolynomial.C_1, one_mul, mul_comm w v]
  rw [hrw]
  exact Ideal.mul_mem_left _ _ (relation_mem_chartIdeal u v n)

/-- The ring `S[t] ⧸ (tⁿ)`. -/
abbrev truncPoly (S : Type*) [CommRing S] (n : ℕ) : Type _ :=
  Polynomial S ⧸ (Ideal.span {Polynomial.X ^ n} : Ideal (Polynomial S))

/-- The image of `t` in `S[t] ⧸ (tⁿ)`. -/
noncomputable def truncT (S : Type*) [CommRing S] (n : ℕ) : truncPoly S n :=
  Ideal.Quotient.mk _ Polynomial.X

/-- The image of `t` in `S[t] ⧸ (tⁿ)` has `n`-th power zero. -/
@[simp]
theorem truncT_pow (S : Type*) [CommRing S] (n : ℕ) : truncT S n ^ n = 0 := by
  rw [truncT, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-! ### The two substitutions -/

/-- The substitution `s ↦ (v/u)·t`, `t ↦ t` of `S[s,t]` into `S[t] ⧸ (tⁿ)`. -/
noncomputable def toTruncAlgHom (v w : S) (n : ℕ) :
    MvPolynomial (Fin 2) S →ₐ[S] truncPoly S n :=
  MvPolynomial.aeval fun i : Fin 2 =>
    if i = 0 then algebraMap S (truncPoly S n) (v * w) * truncT S n else truncT S n

/-- `toTruncAlgHom v w n` sends the constant `a` to its image in `S[t] ⧸ (tⁿ)`. -/
@[simp]
theorem toTruncAlgHom_C (v w : S) (n : ℕ) (a : S) :
    toTruncAlgHom v w n (MvPolynomial.C a) = algebraMap S (truncPoly S n) a := by
  simp [toTruncAlgHom]

/-- `toTruncAlgHom v w n` sends `X 0` to `(v·w)·t` and `X 1` to `t`. -/
theorem toTruncAlgHom_X (v w : S) (n : ℕ) (i : Fin 2) :
    toTruncAlgHom v w n (MvPolynomial.X i) =
      if i = 0 then algebraMap S (truncPoly S n) (v * w) * truncT S n else truncT S n := by
  simp [toTruncAlgHom]

/-- `toTruncAlgHom v w n` sends `s = X 0` to `(v·w)·t`. -/
@[simp]
theorem toTruncAlgHom_X_zero (v w : S) (n : ℕ) :
    toTruncAlgHom v w n (MvPolynomial.X 0) =
      algebraMap S (truncPoly S n) (v * w) * truncT S n := by
  simp [toTruncAlgHom_X]

/-- `toTruncAlgHom v w n` sends `t = X 1` to `t`. -/
@[simp]
theorem toTruncAlgHom_X_one (v w : S) (n : ℕ) :
    toTruncAlgHom v w n (MvPolynomial.X 1) = truncT S n := by
  simp [toTruncAlgHom_X]

/-- If `w·u = 1`, then `chartIdeal u v n` lies in the kernel of `toTruncAlgHom v w n`. -/
theorem chartIdeal_le_ker_toTruncAlgHom {u v w : S} (hw : w * u = 1) (n : ℕ) :
    chartIdeal u v n ≤
      RingHom.ker (toTruncAlgHom v w n : MvPolynomial (Fin 2) S →+* truncPoly S n) := by
  have huvw : u * (v * w) = v := by
    rw [show u * (v * w) = v * (w * u) by ring, hw, mul_one]
  refine sup_le ?_ ?_
  · rw [Ideal.span_le]
    rintro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    change toTruncAlgHom v w n (MvPolynomial.C u * MvPolynomial.X 0 -
      MvPolynomial.C v * MvPolynomial.X 1) = 0
    rw [map_sub, map_mul, map_mul, toTruncAlgHom_C, toTruncAlgHom_C, toTruncAlgHom_X_zero,
      toTruncAlgHom_X_one, ← mul_assoc, ← map_mul, huvw, sub_self]
  · have hgen : Ideal.map (toTruncAlgHom v w n : MvPolynomial (Fin 2) S →+* truncPoly S n)
        (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S))) ≤
          Ideal.span {truncT S n} := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro y ⟨p, ⟨i, rfl⟩, rfl⟩
      refine Ideal.mem_span_singleton'.2
        ⟨if i = 0 then algebraMap S (truncPoly S n) (v * w) else 1, ?_⟩
      change (if i = 0 then algebraMap S (truncPoly S n) (v * w) else 1) * truncT S n =
        toTruncAlgHom v w n (MvPolynomial.X i)
      rw [toTruncAlgHom_X]
      split_ifs <;> simp
    have hzero : (Ideal.span {truncT S n} : Ideal (truncPoly S n)) ^ n = ⊥ := by
      rw [Ideal.span_singleton_pow, truncT_pow]
      simp
    intro z hz
    simp only [RingHom.mem_ker]
    have hmem := Ideal.pow_right_mono hgen n
      (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hz)
    rw [hzero, Ideal.mem_bot] at hmem
    exact hmem

/-- The substitution `s ↦ (v/u)·t`, `t ↦ t`, descended to the quotient by `chartIdeal`. -/
noncomputable def toTrunc {u v w : S} (hw : w * u = 1) (n : ℕ) :
    (MvPolynomial (Fin 2) S ⧸ chartIdeal u v n) →ₐ[S] truncPoly S n :=
  Ideal.Quotient.liftₐ _ (toTruncAlgHom v w n) fun _ ha =>
    chartIdeal_le_ker_toTruncAlgHom hw n ha

/-- `toTrunc hw n` sends the class of `p` to `toTruncAlgHom v w n p`. -/
@[simp]
theorem toTrunc_mk {u v w : S} (hw : w * u = 1) (n : ℕ) (p : MvPolynomial (Fin 2) S) :
    toTrunc hw n (Ideal.Quotient.mk (chartIdeal u v n) p) = toTruncAlgHom v w n p :=
  rfl

/-- The substitution `t ↦ t` of `S[t]` into `S[s,t] ⧸ chartIdeal`. -/
noncomputable def fromTrunc (u v : S) (n : ℕ) :
    truncPoly S n →ₐ[S] (MvPolynomial (Fin 2) S ⧸ chartIdeal u v n) :=
  Ideal.Quotient.liftₐ _
    (Polynomial.aeval (Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X 1))) <| by
      intro p hp
      rw [Ideal.mem_span_singleton] at hp
      obtain ⟨q, rfl⟩ := hp
      rw [map_mul, map_pow, Polynomial.aeval_X, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
        (span_range_X_pow_le_chartIdeal u v n
          (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self 1)) n)), zero_mul]

/-- `fromTrunc u v n` sends the class of `p` to `p` evaluated at the class of `t`. -/
@[simp]
theorem fromTrunc_mk (u v : S) (n : ℕ) (p : Polynomial S) :
    fromTrunc u v n (Ideal.Quotient.mk _ p) =
      Polynomial.aeval (Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X 1)) p :=
  rfl

/-- `fromTrunc u v n` sends `t` to the class of `t = X 1`. -/
@[simp]
theorem fromTrunc_truncT (u v : S) (n : ℕ) :
    fromTrunc u v n (truncT S n) = Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X 1) := by
  rw [truncT, fromTrunc_mk, Polynomial.aeval_X]

/-! ### The isomorphism -/

private theorem toTrunc_fromTrunc {u v w : S} (hw : w * u = 1) (n : ℕ) :
    toTrunc hw n (fromTrunc u v n
        (Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ n}) Polynomial.X)) =
      Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ n}) Polynomial.X := by
  change toTrunc hw n (fromTrunc u v n (truncT S n)) = truncT S n
  rw [fromTrunc_truncT, toTrunc_mk, toTruncAlgHom_X_one]

private theorem fromTrunc_toTrunc {u v w : S} (hw : w * u = 1) (n : ℕ) (i : Fin 2) :
    fromTrunc u v n (toTrunc hw n (Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X i))) =
      Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X i) := by
  rw [toTrunc_mk, toTruncAlgHom_X]
  split_ifs with h
  · subst h
    rw [map_mul, AlgHom.commutes, fromTrunc_truncT]
    have halg : algebraMap S (MvPolynomial (Fin 2) S ⧸ chartIdeal u v n) (v * w) =
        Ideal.Quotient.mk _ (MvPolynomial.C (v * w)) := rfl
    rw [halg, ← map_mul]
    exact (Ideal.Quotient.eq.2 (X_zero_sub_mem_chartIdeal (u := u) (v := v) hw n)).symm
  · have hi : i = 1 := (eq_zero_or_eq_one i).resolve_left h
    subst hi
    rw [fromTrunc_truncT]

/-- **The truncated chart isomorphism.** With `u` invertible, `S[s,t] ⧸ ((us − vt) + (s,t)ⁿ)` is
`S[t] ⧸ (tⁿ)`: the first variable is eliminated by the change of variables
`Stacks.TruncatedChart.X_zero_sub_mem_chartIdeal`, and nothing else survives because `(s,t)ⁿ`
becomes `(tⁿ)`. -/
noncomputable def chartEquiv {u v w : S} (hw : w * u = 1) (n : ℕ) :
    (MvPolynomial (Fin 2) S ⧸ chartIdeal u v n) ≃ₐ[S] truncPoly S n :=
  AlgEquiv.ofAlgHom (toTrunc hw n) (fromTrunc u v n)
    (Ideal.Quotient.algHom_ext (R₁ := S)
      (Polynomial.algHom_ext (by
        simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq]
          using toTrunc_fromTrunc hw n)))
    (Ideal.Quotient.algHom_ext (R₁ := S)
      (MvPolynomial.algHom_ext fun i => by
        simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq]
          using fromTrunc_toTrunc hw n i))

/-! ### The twin that eliminates the second variable

`Stacks.TruncatedChart.chartEquiv` eliminates `s = X 0`, and needs `u` — the coefficient of `s`
in the relation — to be a unit. Interchanging the two variables turns the relation `us − vt` into
`ut − vs`, so the same isomorphism run after a swap eliminates `t = X 1` and asks instead that
`v` be a unit. -/

/-- Renaming the variables by a permutation `e` of `Fin 2` carries the ideal `(s,t)` to itself. -/
theorem map_span_range_X_renameEquiv (e : Fin 2 ≃ Fin 2) :
    Ideal.map (MvPolynomial.renameEquiv S e : MvPolynomial (Fin 2) S →+* MvPolynomial (Fin 2) S)
        (Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S))) =
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) S)) := by
  rw [Ideal.map_span]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨e i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X (e.symm i), ⟨e.symm i, rfl⟩, by simp⟩

/-- **Swapping the two variables interchanges the roles of `u` and `v`.** The relation `us − vt`
becomes `ut − vs`, whose ideal is the one of `vs − ut`, and the ideal of variables is unchanged. -/
theorem map_chartIdeal_renameEquiv_swap (u v : S) (n : ℕ) :
    Ideal.map
        (MvPolynomial.renameEquiv S (Equiv.swap (0 : Fin 2) 1) :
          MvPolynomial (Fin 2) S →+* MvPolynomial (Fin 2) S)
        (chartIdeal u v n) = chartIdeal v u n := by
  have hrel : (MvPolynomial.renameEquiv S (Equiv.swap (0 : Fin 2) 1) :
        MvPolynomial (Fin 2) S →+* MvPolynomial (Fin 2) S)
        (MvPolynomial.C u * MvPolynomial.X 0 - MvPolynomial.C v * MvPolynomial.X 1) =
      -(MvPolynomial.C v * MvPolynomial.X 0 - MvPolynomial.C u * MvPolynomial.X 1) := by
    simp only [RingHom.coe_coe, MvPolynomial.renameEquiv_apply, map_sub, map_mul,
      MvPolynomial.rename_C, MvPolynomial.rename_X, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    ring
  rw [chartIdeal, chartIdeal, Ideal.map_sup, Ideal.map_pow, map_span_range_X_renameEquiv,
    Ideal.map_span, Set.image_singleton, hrel, Ideal.span_singleton_neg]

/-- **The truncated chart isomorphism that eliminates the second variable.** With `v` a unit,
`S[s,t] ⧸ ((us − vt) + (s,t)ⁿ)` is `S[s] ⧸ (sⁿ)`. It is `Stacks.TruncatedChart.chartEquiv` read
through the swap of the two variables, so the change of variables is now `t ↦ (u/v)s`. -/
noncomputable def chartEquivSwap {u v w : S} (hw : w * v = 1) (n : ℕ) :
    (MvPolynomial (Fin 2) S ⧸ chartIdeal u v n) ≃ₐ[S] truncPoly S n :=
  (Ideal.quotientEquivAlg (chartIdeal u v n) (chartIdeal v u n)
      (MvPolynomial.renameEquiv S (Equiv.swap (0 : Fin 2) 1))
      (map_chartIdeal_renameEquiv_swap u v n).symm).trans (chartEquiv hw n)

/-- The surviving variable `s` is carried to `t` of `S[t] ⧸ (tⁿ)`. -/
@[simp]
theorem chartEquivSwap_mk_X_zero {u v w : S} (hw : w * v = 1) (n : ℕ) :
    chartEquivSwap hw n (Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X 0)) =
      truncT S n := by
  change chartEquiv hw n (Ideal.Quotient.mk (chartIdeal v u n)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 0))) = truncT S n
  rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
  change toTruncAlgHom u w n (MvPolynomial.X 1) = truncT S n
  rw [toTruncAlgHom_X_one]

/-- **The change of variables of the twin**: the eliminated variable `t` is `(u/v)·s`. -/
@[simp]
theorem chartEquivSwap_mk_X_one {u v w : S} (hw : w * v = 1) (n : ℕ) :
    chartEquivSwap hw n (Ideal.Quotient.mk (chartIdeal u v n) (MvPolynomial.X 1)) =
      algebraMap S (truncPoly S n) (u * w) * truncT S n := by
  change chartEquiv hw n (Ideal.Quotient.mk (chartIdeal v u n)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 1))) = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_right]
  change toTruncAlgHom u w n (MvPolynomial.X 0) = _
  rw [toTruncAlgHom_X_zero]

end Stacks.TruncatedChart

end
