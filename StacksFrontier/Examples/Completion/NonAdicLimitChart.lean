module

public import StacksFrontier.Examples.Completion.NonAdicLimitTopology
public import StacksFrontier.RingTheory.MvPolynomial.TruncatedChart
public import StacksFrontier.RingTheory.MvPowerSeries.PolynomialTruncation
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# The truncated charts of `A = k[x,y][[s,t]]/(xs − yt)`, Stacks 0EH8

Stacks 0EH8's "computation omitted" needs the charts of `𝒪_X/Iⁿ𝒪_X` on `D(x)` and `D(y)`, and
the shape one first writes down for the `D(x)` chart — `A[1/x] ≅ k[x^{±1}, y][[t]]` — is
**false**: see the docstring of `Stacks.Examples.NonAdicLimit.not_isUnit_mul_add_mul`. Inverting
`x` in a power series ring is not inverting it in the coefficients, and `A[1/x]` is a proper
subring of that target.

What is true, and what the computation uses, is the *truncation*:

`A[1/x] ⧸ Iⁿ ≃+* k[x^{±1}, y][t] ⧸ (tⁿ)`,

together with its `D(y)` twin `A[1/y] ⧸ Iⁿ ≃+* k[x, y^{±1}][s] ⧸ (sⁿ)`.

Each is assembled here in three steps, none of which is available untruncated.

1. Modulo `Iⁿ = (s,t)ⁿ` only the coefficients in total degree below `n` survive, so the power
   series ring is the polynomial ring:
   `A ⧸ Iⁿ ≃+* k[x,y][s,t] ⧸ ((xs − yt) + (s,t)ⁿ)`
   (`Stacks.Examples.NonAdicLimit.truncationEquiv`, from
   `Stacks.MvPowerSeries.RegularParameters.polynomialTruncationEquiv`).
2. A polynomial ring, unlike a power series ring, commutes with localization
   (`MvPolynomial.isLocalization`), and so therefore does the quotient by `Iⁿ`. This is the step
   that fails untruncated, and it is why the truncation has to come first.
3. Over a ring in which `x` is a unit the change of variables `s ↦ (y/x)t` eliminates `s`:
   `k[x^{±1}, y][s,t] ⧸ ((xs − yt) + (s,t)ⁿ) ≃ k[x^{±1}, y][t] ⧸ (tⁿ)`
   (`Stacks.TruncatedChart.chartEquiv`).

Only the third step distinguishes the two charts, and only because
`Stacks.TruncatedChart.chartEquiv` eliminates the first variable: on `D(y)` it is applied through
`Stacks.TruncatedChart.chartEquivSwap`, which runs it after `MvPolynomial.rename (Equiv.swap 0 1)`
and so eliminates `t` by `t ↦ (x/y)s`. Steps 1 and 2 are stated once for both, step 2 over an
arbitrary `k[x,y]`-algebra of coefficients.

## Main definitions

* `Stacks.Examples.NonAdicLimit.relationPoly` — the relation `xs − yt` as a polynomial.
* `Stacks.Examples.NonAdicLimit.coeffAwayX`, `.coeffAwayY` — the coefficient rings
  `k[x^{±1}, y] = k[x,y][1/x]` and `k[x, y^{±1}] = k[x,y][1/y]` of the two charts.

## Main results

* `Stacks.Examples.NonAdicLimit.coe_relationPoly` — the relation of `A` is a polynomial.
* `Stacks.Examples.NonAdicLimit.adicIdeal_eq_map_span_range_X` — `I = (s,t)` is the image of the
  ideal of variables of `k[x,y][[s,t]]`.
* `Stacks.Examples.NonAdicLimit.truncationEquiv` — step 1, with
  `Stacks.Examples.NonAdicLimit.truncationEquiv_mk` computing it on a polynomial.
* `Stacks.Examples.NonAdicLimit.map_chartIdeal` — step 2, over any `k[x,y]`-algebra.
* `Stacks.Examples.NonAdicLimit.chartTruncationEquivX` — **the `D(x)` truncated chart
  isomorphism** `A[1/x] ⧸ Iⁿ ≃+* k[x^{±1}, y][t] ⧸ (tⁿ)`.
* `Stacks.Examples.NonAdicLimit.chartTruncationEquivY` — **the `D(y)` twin**
  `A[1/y] ⧸ Iⁿ ≃+* k[x, y^{±1}][s] ⧸ (sⁿ)`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Examples.NonAdicLimit

open Stacks.TruncatedChart Stacks.MvPowerSeries.RegularParameters

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (k : Type u) [Field k]

/-! ### The relation and the ideal of variables, read on polynomials -/

private alias fin_two_cases := Stacks.TruncatedChart.eq_zero_or_eq_one

/-- `k[x,y][s,t]`, the polynomial ring of which `k[x,y][[s,t]]` is the completion in `s` and
`t`. -/
abbrev ambientPoly : Type u := MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k)

/-- The relation `xs − yt` as an element of `k[x,y][s,t]`. -/
def relationPoly : ambientPoly k :=
  MvPolynomial.C (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 0 -
    MvPolynomial.C (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1

/-- **The relation of `A` is a polynomial**: `xs − yt` is the image of
`Stacks.Examples.NonAdicLimit.relationPoly`. -/
theorem coe_relationPoly : ((relationPoly k : ambientPoly k) : ambient k) = relation k := by
  change MvPolynomial.coeToMvPowerSeries.ringHom (relationPoly k) = relation k
  rw [relationPoly, map_sub, map_mul, map_mul]
  simp [relation, ambientX, ambientY, ambientS, ambientT,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply]

/-- The ideal of variables `(s,t)` of `k[x,y][[s,t]]`. -/
abbrev seriesVarsIdeal : Ideal (ambient k) :=
  Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → ambient k))

/-- The ideal of variables `(s,t)` of `k[x,y][s,t]`. -/
abbrev polyVarsIdeal : Ideal (ambientPoly k) :=
  Ideal.span (Set.range (MvPolynomial.X : Fin 2 → ambientPoly k))

/-- **`I = (s,t)` is the image of the ideal of variables of `k[x,y][[s,t]]`.** -/
theorem adicIdeal_eq_map_span_range_X :
    adicIdeal k =
      Ideal.map (Ideal.Quotient.mk (Ideal.span {relation k})) (seriesVarsIdeal k) := by
  refine le_antisymm ?_ ?_
  · rw [adicIdeal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self 0))
    · exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self 1))
  · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro z ⟨i, rfl⟩
    rcases fin_two_cases i with rfl | rfl
    · exact coordS_mem_adicIdeal k
    · exact coordT_mem_adicIdeal k

/-- `Iⁿ` is the image of the `n`-th power of the ideal of variables of `k[x,y][[s,t]]`. -/
theorem adicIdeal_pow_eq_map_span_range_X_pow (n : ℕ) :
    adicIdeal k ^ n =
      Ideal.map (Ideal.Quotient.mk (Ideal.span {relation k})) (seriesVarsIdeal k ^ n) := by
  rw [Ideal.map_pow, adicIdeal_eq_map_span_range_X]

/-! ### Step 1: `A ⧸ Iⁿ` is a polynomial chart -/

/-- The chart ideal of `x` and `y` in `k[x,y][s,t]` is `(s,t)ⁿ + (xs − yt)`. -/
theorem chartIdeal_eq_sup (n : ℕ) :
    chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n =
      polyVarsIdeal k ^ n ⊔ Ideal.span {relationPoly k} := by
  rw [chartIdeal, relationPoly]
  exact sup_comm _ _

/-- The image of `(xs − yt)` in `k[x,y][[s,t]] ⧸ (s,t)ⁿ` is the image of `(xs − yt)` in
`k[x,y][s,t] ⧸ (s,t)ⁿ` under `Stacks.MvPowerSeries.RegularParameters.polynomialTruncationEquiv`. -/
theorem map_span_relation_eq (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk (seriesVarsIdeal k ^ n)) (Ideal.span {relation k}) =
      Ideal.map
        (polynomialTruncationEquiv (R := MvPolynomial (Fin 2) k) (n := 2) n).toRingHom
        (Ideal.map (Ideal.Quotient.mk (polyVarsIdeal k ^ n)) (Ideal.span {relationPoly k})) := by
  rw [← coe_relationPoly k]
  exact map_mk_span_singleton_eq n (relationPoly k)

/-- **The truncation of `A`, Stacks 0EH8.** `A ⧸ Iⁿ` is the *polynomial* chart
`k[x,y][s,t] ⧸ ((xs − yt) + (s,t)ⁿ)`: modulo `Iⁿ = (s,t)ⁿ` only the coefficients in total degree
below `n` survive, so no power series does.

This is the step whose untruncated form is false. `A[1/x]` is a *proper* subring of
`k[x^{±1}, y][[t]]`, because the pole order in `x` of the image of `a/xᵐ` grows with the degree
in `t` while `m` does not — see the docstring of
`Stacks.Examples.NonAdicLimit.not_isUnit_mul_add_mul`. Modulo `Iⁿ` the degrees in `t` are
bounded, and what remains is a polynomial ring, which does commute with localization. -/
@[stacks 0EH8 "A/I^n is the polynomial chart k[x,y][s,t]/((xs - yt) + (s,t)^n): the truncation \
that makes the chart isomorphism true, where its untruncated form A[1/x] = k[x^{±1},y][[t]] is \
false"]
def truncationEquiv (n : ℕ) :
    (ambientPoly k ⧸
        chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n) ≃+*
      (exampleRing k ⧸ adicIdeal k ^ n) :=
  (Ideal.quotEquivOfEq (chartIdeal_eq_sup k n)).trans
    (((DoubleQuot.quotQuotEquivQuotSup (polyVarsIdeal k ^ n)
          (Ideal.span {relationPoly k})).symm.trans
        (Ideal.quotientEquiv _ _
          (polynomialTruncationEquiv (R := MvPolynomial (Fin 2) k) (n := 2) n)
          (map_span_relation_eq k n))).trans
      (((DoubleQuot.quotQuotEquivQuotSup (seriesVarsIdeal k ^ n)
            (Ideal.span {relation k})).trans
          (Ideal.quotEquivOfEq (sup_comm (seriesVarsIdeal k ^ n) (Ideal.span {relation k})))).trans
        ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {relation k})
            (seriesVarsIdeal k ^ n)).symm.trans
          (Ideal.quotEquivOfEq (adicIdeal_pow_eq_map_span_range_X_pow k n).symm))))

/-- **The truncation carries a polynomial to its own class.** -/
@[simp]
theorem truncationEquiv_mk (n : ℕ) (p : ambientPoly k) :
    truncationEquiv k n (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (adicIdeal k ^ n)
        (Ideal.Quotient.mk (Ideal.span {relation k}) (p : ambient k)) :=
  rfl

/-- `Stacks.Examples.NonAdicLimit.truncationEquiv` sends the class of `x` to the class of `x`. -/
theorem truncationEquiv_mk_C_X_zero (n : ℕ) :
    truncationEquiv k n (Ideal.Quotient.mk _
        (MvPolynomial.C (MvPolynomial.X 0 : MvPolynomial (Fin 2) k))) =
      Ideal.Quotient.mk (adicIdeal k ^ n) (coordX k) := by
  simp [coordX, ambientX]

/-- `Stacks.Examples.NonAdicLimit.truncationEquiv` sends the class of `y` to the class of `y`. -/
theorem truncationEquiv_mk_C_X_one (n : ℕ) :
    truncationEquiv k n (Ideal.Quotient.mk _
        (MvPolynomial.C (MvPolynomial.X 1 : MvPolynomial (Fin 2) k))) =
      Ideal.Quotient.mk (adicIdeal k ^ n) (coordY k) := by
  simp [coordY, ambientY]

/-! ### Steps 2 and 3: inverting `x`, or inverting `y` -/

/-- `k[x^{±1}, y] = k[x,y][1/x]`, the coefficient ring of the `D(x)`-chart. -/
abbrev coeffAwayX : Type u := Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)

/-- `k[x, y^{±1}] = k[x,y][1/y]`, the coefficient ring of the `D(y)`-chart. -/
abbrev coeffAwayY : Type u := Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)

/-- `x` is invertible in `k[x^{±1}, y]`, with `IsLocalization.Away.invSelf` as its inverse. -/
theorem invSelf_mul_algebraMap_X_zero :
    IsLocalization.Away.invSelf (S := coeffAwayX k)
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) *
        algebraMap (MvPolynomial (Fin 2) k) (coeffAwayX k) (MvPolynomial.X 0) = 1 := by
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf _

/-- `y` is invertible in `k[x, y^{±1}]`, with `IsLocalization.Away.invSelf` as its inverse. -/
theorem invSelf_mul_algebraMap_X_one :
    IsLocalization.Away.invSelf (S := coeffAwayY k)
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) *
        algebraMap (MvPolynomial (Fin 2) k) (coeffAwayY k) (MvPolynomial.X 1) = 1 := by
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf _

section Base

variable (R : Type u) [CommRing R] [Algebra (MvPolynomial (Fin 2) k) R]

/-- The structure map `k[x,y][s,t] ⟶ R[s,t]` of a `k[x,y]`-algebra `R` is
`MvPolynomial.map`. -/
theorem algebraMap_ambientPoly_eq :
    (algebraMap (ambientPoly k) (MvPolynomial (Fin 2) R)) =
      MvPolynomial.map (algebraMap (MvPolynomial (Fin 2) k) R) :=
  MvPolynomial.algebraMap_def

/-- The image of `(xs − yt)` in `R[s,t]` is the ideal generated by `xs − yt` with `x` and `y`
read in `R`. -/
theorem map_span_relationPoly :
    Ideal.map (algebraMap (ambientPoly k) (MvPolynomial (Fin 2) R))
        (Ideal.span {relationPoly k}) =
      Ideal.span {MvPolynomial.C
                      (algebraMap (MvPolynomial (Fin 2) k) R (MvPolynomial.X 0)) *
                    MvPolynomial.X 0 -
                  MvPolynomial.C
                      (algebraMap (MvPolynomial (Fin 2) k) R (MvPolynomial.X 1)) *
                    MvPolynomial.X 1} := by
  rw [Ideal.map_span, Set.image_singleton, algebraMap_ambientPoly_eq]
  congr 1
  rw [relationPoly, map_sub, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.map_X]

/-- The image of the ideal of variables `(s,t)` of `k[x,y][s,t]` in `R[s,t]` is the ideal of
variables of `R[s,t]`. -/
theorem map_polyVarsIdeal :
    Ideal.map (algebraMap (ambientPoly k) (MvPolynomial (Fin 2) R))
        (polyVarsIdeal k) =
      Ideal.span (Set.range
        (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) := by
  rw [Ideal.map_span, algebraMap_ambientPoly_eq]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.map_X _ i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, MvPolynomial.map_X _ i⟩

/-- **The chart ideal is carried to the chart ideal over any `k[x,y]`-algebra.** Taking `R` to be
`k[x^{±1}, y]` or `k[x, y^{±1}]` gives the two charts. -/
theorem map_chartIdeal (n : ℕ) :
    Ideal.map (algebraMap (ambientPoly k) (MvPolynomial (Fin 2) R))
        (chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n) =
      chartIdeal (algebraMap (MvPolynomial (Fin 2) k) R (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) k) R (MvPolynomial.X 1)) n := by
  rw [chartIdeal, chartIdeal, Ideal.map_sup, Ideal.map_pow]
  rw [show (Ideal.span {MvPolynomial.C (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) *
                            MvPolynomial.X 0 -
                          MvPolynomial.C (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) *
                            MvPolynomial.X 1} :
      Ideal (ambientPoly k)) = Ideal.span {relationPoly k} from by rw [relationPoly],
    map_span_relationPoly k R, map_polyVarsIdeal k R]

end Base

/-- **The truncated chart isomorphism of Stacks 0EH8, on `D(x)`.**

`A[1/x] ⧸ Iⁿ ≃+* k[x^{±1}, y][t] ⧸ (tⁿ)`, the `D(x)`-chart of `𝒪_X/Iⁿ𝒪_X` that the source's
"computation omitted" rests on. It sends `s ↦ (y/x)t`, hence `I = (s,t) ↦ (t)` and
`g = t/x ↦ x⁻¹t`.

Its *untruncated* form `A[1/x] ≅ k[x^{±1}, y][[t]]` is **false** — see the docstring of
`Stacks.Examples.NonAdicLimit.not_isUnit_mul_add_mul`. The truncation is what makes it true, and
the proof shows why: `A ⧸ Iⁿ` is a *polynomial* ring
(`Stacks.Examples.NonAdicLimit.truncationEquiv`), a polynomial ring does commute with
localization (`MvPolynomial.isLocalization`), and then `x` being a unit the change of variables
`s ↦ (y/x)t` eliminates `s` (`Stacks.TruncatedChart.chartEquiv`). The middle step is the one that
has no untruncated analogue.

The `D(y)` twin is `Stacks.Examples.NonAdicLimit.chartTruncationEquivY`. -/
@[stacks 0EH8 "the truncated chart isomorphism A[1/x]/I^n = k[x^{±1},y][t]/(t^n), sending s to \
(y/x)t; the chart the omitted computation of H^0(X, F_n) needs, and whose untruncated form is \
false"]
def chartTruncationEquivX (n : ℕ) :
    (Localization.Away (coordX k) ⧸
        (adicIdeal k ^ n).map
          (algebraMap (exampleRing k) (Localization.Away (coordX k)))) ≃+*
      truncPoly (coeffAwayX k) n :=
  (IsLocalization.ringEquivOfRingEquiv
      (M := Algebra.algebraMapSubmonoid (ambientPoly k ⧸
        chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n)
        ((Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)).map
          (MvPolynomial.C (σ := Fin 2))))
      (T := Algebra.algebraMapSubmonoid (exampleRing k ⧸ adicIdeal k ^ n)
        (Submonoid.powers (coordX k)))
      (MvPolynomial (Fin 2) (coeffAwayX k) ⧸
        (chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n).map
          (algebraMap (ambientPoly k) (MvPolynomial (Fin 2) (coeffAwayX k))))
      (Localization.Away (coordX k) ⧸
        (adicIdeal k ^ n).map (algebraMap (exampleRing k) (Localization.Away (coordX k))))
      (truncationEquiv k n)
      (by
        rw [Algebra.algebraMapSubmonoid, Algebra.algebraMapSubmonoid,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq,
          Submonoid.map_powers, Submonoid.map_powers, Submonoid.map_powers,
          Submonoid.map_powers]
        congr 1
        exact truncationEquiv_mk_C_X_zero k n)).symm.trans
    ((Ideal.quotEquivOfEq (map_chartIdeal k (coeffAwayX k) n)).trans
      (chartEquiv (invSelf_mul_algebraMap_X_zero k) n).toRingEquiv)

/-- **The truncated chart isomorphism of Stacks 0EH8, on `D(y)`.**

`A[1/y] ⧸ Iⁿ ≃+* k[x, y^{±1}][s] ⧸ (sⁿ)`, the twin of
`Stacks.Examples.NonAdicLimit.chartTruncationEquivX` and the second of the two charts the
source's "computation omitted" rests on. It sends `t ↦ (x/y)s`, hence `I = (s,t) ↦ (s)` and
`g = t/x ↦ y⁻¹s`.

The proof is the `D(x)` proof with the two variables interchanged, and only the last of its three
steps is asymmetric. Steps 1 and 2 — `A ⧸ Iⁿ` is the polynomial chart
`k[x,y][s,t] ⧸ ((xs − yt) + (s,t)ⁿ)` (`Stacks.Examples.NonAdicLimit.truncationEquiv`), and a
polynomial chart commutes with localization (`MvPolynomial.isLocalization`,
`Stacks.Examples.NonAdicLimit.map_chartIdeal`) — do not mention which variable is inverted. Step
3 does: `Stacks.TruncatedChart.chartEquiv` eliminates the *first* variable and wants the
coefficient of `s` to be a unit, so here it is used through
`Stacks.TruncatedChart.chartEquivSwap`, which runs it after `MvPolynomial.rename (Equiv.swap 0 1)`
and eliminates `t` instead.

As for `D(x)`, the untruncated form `A[1/y] ≅ k[x, y^{±1}][[s]]` is **false**: the pole-order
argument in the docstring of `Stacks.Examples.NonAdicLimit.not_isUnit_mul_add_mul` is symmetric
in the two variables. -/
@[stacks 0EH8 "the truncated chart isomorphism A[1/y]/I^n = k[x,y^{±1}][s]/(s^n), sending t to \
(x/y)s; the D(y) twin of the chart the omitted computation of H^0(X, F_n) needs, and whose \
untruncated form is likewise false"]
def chartTruncationEquivY (n : ℕ) :
    (Localization.Away (coordY k) ⧸
        (adicIdeal k ^ n).map
          (algebraMap (exampleRing k) (Localization.Away (coordY k)))) ≃+*
      truncPoly (coeffAwayY k) n :=
  (IsLocalization.ringEquivOfRingEquiv
      (M := Algebra.algebraMapSubmonoid (ambientPoly k ⧸
        chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n)
        ((Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)).map
          (MvPolynomial.C (σ := Fin 2))))
      (T := Algebra.algebraMapSubmonoid (exampleRing k ⧸ adicIdeal k ^ n)
        (Submonoid.powers (coordY k)))
      (MvPolynomial (Fin 2) (coeffAwayY k) ⧸
        (chartIdeal (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) n).map
          (algebraMap (ambientPoly k) (MvPolynomial (Fin 2) (coeffAwayY k))))
      (Localization.Away (coordY k) ⧸
        (adicIdeal k ^ n).map (algebraMap (exampleRing k) (Localization.Away (coordY k))))
      (truncationEquiv k n)
      (by
        rw [Algebra.algebraMapSubmonoid, Algebra.algebraMapSubmonoid,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq,
          Submonoid.map_powers, Submonoid.map_powers, Submonoid.map_powers,
          Submonoid.map_powers]
        congr 1
        exact truncationEquiv_mk_C_X_one k n)).symm.trans
    ((Ideal.quotEquivOfEq (map_chartIdeal k (coeffAwayY k) n)).trans
      (chartEquivSwap (invSelf_mul_algebraMap_X_one k) n).toRingEquiv)

end Stacks.Examples.NonAdicLimit

end
