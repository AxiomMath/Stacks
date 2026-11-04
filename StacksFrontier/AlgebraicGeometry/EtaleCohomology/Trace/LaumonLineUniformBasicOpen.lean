module

public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# A curve of the `(a, t)`-plane meeting every line `a = a₀` properly, from fibrewise data

Let `k` be a finite field. Suppose that for `m = 0` and for every irreducible `m ∈ k[a]` we are
given `h_m ∈ k[a, t]` not divisible by `m(a)`, satisfying some property `Q m h_m`. Then there is
one `D ∈ k[a, t]`, `D ≠ 0`, such that for every finite extension `k'` of `k` and every `a₀ ∈ k'`:

* `D(a₀, t) ≠ 0` in `k'[t]`, and
* there is such an `m` with `m(a₀) = 0` and `D(D(a₀, t)) ⊆ D(h_m(a₀, t))` in `Spec k'[t]`
  (`Stacks.EtaleCohomology.exists_laumonLine_uniform_basicOpen`).

This is the bookkeeping that makes the lisse locus of the Fourier family of Laumon's argument
uniform in `(k', a₀)` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). Write `h₀ = h_0` as
a polynomial in `t` over `k[a]`, `h₀ = c · P` with `c` the content and `P` primitive. A primitive
polynomial does not vanish identically on any line `a = a₀` (the minimal polynomial of `a₀` would
divide all its coefficients). On the finitely many lines through the roots of `c`, for an
irreducible factor `m` of `c` the reduction of `h_m` modulo `m` is a nonzero polynomial over the
finite field `k[a]/(m)`, so it divides some `tⁱ - tʲ`, `i ≠ j` (pigeonhole in the finite ring
`(k[a]/(m))[t]/(h_m)`). The curve is `D = P · ∏_m (tⁱᵐ - tʲᵐ)`.

## Main results

* `Stacks.EtaleCohomology.laumonPlaneToIter`, `Stacks.EtaleCohomology.laumonIterToPlane`: the two
  presentations `k[a, t] = MvPolynomial (Fin 2) k` and `k[a][t]`.
* `Stacks.EtaleCohomology.eval₂_laumonLine_eq_map`: `D(a₀, t)` is the image of `D` under
  `a ↦ a₀` coefficientwise.
* `Stacks.EtaleCohomology.exists_laumonLine_uniform_basicOpen`.
-/

@[expose] public noncomputable section

open Polynomial

universe v

namespace Stacks.EtaleCohomology

/-- `tⁱ - tʲ ≠ 0` for `i ≠ j`. -/
public theorem X_pow_sub_X_pow_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {i j : ℕ}
    (hij : i ≠ j) : (X ^ i - X ^ j : Polynomial R) ≠ 0 := fun h =>
  hij (by simpa using congrArg Polynomial.natDegree (sub_eq_zero.1 h))

/-- A basic open shrinks along divisibility: `f ∣ g → D(g) ⊆ D(f)`. -/
public theorem basicOpen_le_of_dvd {R : Type*} [CommSemiring R] {f g : R} (h : f ∣ g) :
    PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f := by
  obtain ⟨r, rfl⟩ := h
  rw [PrimeSpectrum.basicOpen_mul]
  exact inf_le_left

variable {k : Type*} [Field k]

/-- `k[a, t] → k[a][t]`: `a = X 0` goes to the inner variable, `t = X 1` to the outer one. -/
public def laumonPlaneToIter : MvPolynomial (Fin 2) k →+* Polynomial (Polynomial k) :=
  MvPolynomial.eval₂Hom (C.comp C) ![C X, X]

/-- `k[a][t] → k[a, t]`, the inverse of `Stacks.EtaleCohomology.laumonPlaneToIter`. -/
public def laumonIterToPlane : Polynomial (Polynomial k) →+* MvPolynomial (Fin 2) k :=
  eval₂RingHom (eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)

/-- `laumonPlaneToIter` is a left inverse of `laumonIterToPlane`. -/
public theorem laumonPlaneToIter_laumonIterToPlane (P : Polynomial (Polynomial k)) :
    laumonPlaneToIter (laumonIterToPlane P) = P := by
  have h : (laumonPlaneToIter (k := k)).comp laumonIterToPlane = RingHom.id _ := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' ?_ ?_) ?_
    · ext r
      simp [laumonPlaneToIter, laumonIterToPlane]
    · simp [laumonPlaneToIter, laumonIterToPlane]
    · simp [laumonPlaneToIter, laumonIterToPlane]
  exact RingHom.congr_fun h P

/-- `laumonIterToPlane` is a left inverse of `laumonPlaneToIter`. -/
public theorem laumonIterToPlane_laumonPlaneToIter (D : MvPolynomial (Fin 2) k) :
    laumonIterToPlane (laumonPlaneToIter D) = D := by
  have h : (laumonIterToPlane (k := k)).comp laumonPlaneToIter = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [laumonPlaneToIter, laumonIterToPlane]
    · fin_cases i <;> simp [laumonPlaneToIter, laumonIterToPlane]
  exact RingHom.congr_fun h D

/-- `laumonIterToPlane (C m) = m(a)`. -/
public theorem laumonIterToPlane_C (m : Polynomial k) :
    laumonIterToPlane (C m) = Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) m := by
  simp [laumonIterToPlane, Polynomial.aeval_def, MvPolynomial.algebraMap_eq]

/-- **`D(a₀, t)` is `D` with `a ↦ a₀` applied to the coefficients in `k[a]`.** -/
public theorem eval₂_laumonLine_eq_map {k' : Type*} [Field k'] [Algebra k k'] (a : k')
    (D : MvPolynomial (Fin 2) k) :
    MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X] D =
      (laumonPlaneToIter D).map (eval₂RingHom (algebraMap k k') a) := by
  have h : MvPolynomial.eval₂Hom (C.comp (algebraMap k k')) ![C a, X] =
      (mapRingHom (eval₂RingHom (algebraMap k k') a)).comp laumonPlaneToIter := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [laumonPlaneToIter]
    · fin_cases i <;> simp [laumonPlaneToIter]
  exact RingHom.congr_fun h D

/-- `m` divides a polynomial over `k[a]` if it divides every coefficient killed by `f`
and `f` kills the polynomial coefficientwise. -/
private theorem C_dvd_of_map_eq_zero {S : Type*} [Semiring S] {m : Polynomial k}
    {P : Polynomial (Polynomial k)} (f : Polynomial k →+* S) (hf : ∀ g, f g = 0 → m ∣ g)
    (hP : P.map f = 0) : C m ∣ P :=
  (Polynomial.C_dvd_iff_dvd_coeff m P).2 fun i =>
    hf _ (by rw [← Polynomial.coeff_map, hP, Polynomial.coeff_zero])

/-- **A polynomial over `k[a]` vanishing on the line `a = a₀` is divisible by every irreducible
`m` with `m(a₀) = 0`.** -/
public theorem C_dvd_of_map_eval₂RingHom_eq_zero {k' : Type*} [Field k'] [Algebra k k']
    {a : k'} (ha : IsIntegral k a) {m : Polynomial k} (hm : Irreducible m)
    (hma : Polynomial.aeval a m = 0) {P : Polynomial (Polynomial k)}
    (hP : P.map (eval₂RingHom (algebraMap k k') a) = 0) : C m ∣ P := by
  have hmin : Associated (minpoly k a) m :=
    (minpoly.irreducible ha).associated_of_dvd hm (minpoly.dvd k a hma)
  exact C_dvd_of_map_eq_zero _
    (fun g hg => hmin.symm.dvd.trans (minpoly.dvd k a (by simpa [Polynomial.aeval_def] using hg)))
    hP

/-- **A primitive polynomial over `k[a]` vanishes identically on no line `a = a₀`.** -/
public theorem map_eval₂RingHom_ne_zero_of_isPrimitive {k' : Type*} [Field k'] [Algebra k k']
    {a : k'} (ha : IsIntegral k a) {P : Polynomial (Polynomial k)} (hP : P.IsPrimitive) :
    P.map (eval₂RingHom (algebraMap k k') a) ≠ 0 := fun h0 =>
  (minpoly.irreducible ha).not_isUnit
    (hP _ (C_dvd_of_map_eval₂RingHom_eq_zero ha (minpoly.irreducible ha) (minpoly.aeval k a) h0))

/-- **Pigeonhole on a line over a finite field**: for `k` finite, `m ∈ k[a]` irreducible and
`P ∈ k[a][t]` not divisible by `m`, there are `i ≠ j` such that on every line `a = a₀` with
`m(a₀) = 0`, `P(a₀, t)` divides `tⁱ - tʲ`. -/
public theorem exists_ne_forall_map_dvd_X_pow_sub_X_pow [Finite k] {m : Polynomial k}
    (hm : Irreducible m) {P : Polynomial (Polynomial k)} (hP : ¬ C m ∣ P) :
    ∃ i j : ℕ, i ≠ j ∧ ∀ (k' : Type*) [Field k'] [Algebra k k'] (a : k'),
      Polynomial.aeval a m = 0 →
        P.map (eval₂RingHom (algebraMap k k') a) ∣ (X ^ i - X ^ j : Polynomial k') := by
  have := Fact.mk hm
  set Pb : Polynomial (AdjoinRoot m) := P.map (AdjoinRoot.mk m) with hPbdef
  have hPb : Pb ≠ 0 := fun h0 => hP (C_dvd_of_map_eq_zero _ (fun g => AdjoinRoot.mk_eq_zero.1) h0)
  have : Module.Finite k (AdjoinRoot m) := (AdjoinRoot.powerBasis hm.ne_zero).finite
  have : Finite (AdjoinRoot m) := Module.finite_of_finite k
  have : Module.Finite (AdjoinRoot m) (AdjoinRoot Pb) := (AdjoinRoot.powerBasis hPb).finite
  have : Finite (AdjoinRoot Pb) := Module.finite_of_finite (AdjoinRoot m)
  obtain ⟨i, j, hij, hpow⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (AdjoinRoot.root Pb) ^ i)
  refine ⟨i, j, hij, fun k' _ _ a hma => ?_⟩
  have hdvd : Pb ∣ (X ^ i - X ^ j : Polynomial (AdjoinRoot m)) := by
    rw [← AdjoinRoot.mk_eq_mk]
    simpa using hpow
  have hma' : m.eval₂ (algebraMap k k') a = 0 := by simpa [Polynomial.aeval_def] using hma
  have hφ : (AdjoinRoot.lift (algebraMap k k') a hma').comp (AdjoinRoot.mk m) =
      eval₂RingHom (algebraMap k k') a := by
    refine RingHom.ext fun g => ?_
    rw [RingHom.comp_apply, AdjoinRoot.lift_mk, coe_eval₂RingHom]
  have := Polynomial.map_dvd (AdjoinRoot.lift (algebraMap k k') a hma') hdvd
  rwa [hPbdef, Polynomial.map_map, hφ, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_pow,
    Polynomial.map_X] at this

/-- **A uniform curve from fibrewise data** (see the module docstring). -/
public theorem exists_laumonLine_uniform_basicOpen [Finite k]
    (Q : Polynomial k → MvPolynomial (Fin 2) k → Prop)
    (hF : ∀ m : Polynomial k, (m = 0 ∨ Irreducible m) → ∃ h : MvPolynomial (Fin 2) k,
      ¬ Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) m ∣ h ∧ Q m h) :
    ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ ∀ (k' : Type v) [Field k'] [Finite k'] [Algebra k k']
      (a : k'), MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X] D ≠ 0 ∧
        ∃ (m : Polynomial k) (h : MvPolynomial (Fin 2) k), Q m h ∧ Polynomial.aeval a m = 0 ∧
          PrimeSpectrum.basicOpen (MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X] D) ≤
            PrimeSpectrum.basicOpen
              (MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X] h) := by
  classical
  obtain ⟨h₀, hh₀, hQ₀⟩ := hF 0 (Or.inl rfl)
  have hh₀' : h₀ ≠ 0 := by rintro rfl; exact hh₀ (by simp)
  set H := laumonPlaneToIter h₀ with hH
  have hH0 : H ≠ 0 := by
    intro h0
    apply hh₀'
    rw [← laumonIterToPlane_laumonPlaneToIter h₀, ← hH, h0, map_zero]
  set c := H.content
  have hc0 : c ≠ 0 := fun h => hH0 (Polynomial.content_eq_zero_iff.1 h)
  have hfac : ∀ m ∈ UniqueFactorizationMonoid.normalizedFactors c, Irreducible m :=
    fun m hm => UniqueFactorizationMonoid.irreducible_of_normalized_factor m hm
  have hline : ∀ m ∈ UniqueFactorizationMonoid.normalizedFactors c, ∃ h : MvPolynomial (Fin 2) k,
      Q m h ∧ ∃ i j : ℕ, i ≠ j ∧ ∀ (k' : Type v) [Field k'] [Algebra k k'] (a : k'),
        Polynomial.aeval a m = 0 →
          (laumonPlaneToIter h).map (eval₂RingHom (algebraMap k k') a) ∣
            (X ^ i - X ^ j : Polynomial k') := by
    intro m hm
    obtain ⟨h, hmh, hQ⟩ := hF m (Or.inr (hfac m hm))
    refine ⟨h, hQ, exists_ne_forall_map_dvd_X_pow_sub_X_pow (hfac m hm) fun hd => hmh ?_⟩
    have := map_dvd laumonIterToPlane hd
    rwa [laumonIterToPlane_laumonPlaneToIter, laumonIterToPlane_C] at this
  choose! hl hlQ il jl hijl hdl using hline
  set S := (UniqueFactorizationMonoid.normalizedFactors c).toFinset
  let E : Polynomial (Polynomial k) := ∏ m ∈ S, (X ^ il m - X ^ jl m)
  let D' : Polynomial (Polynomial k) := H.primPart * E
  have hPne : H.primPart ≠ 0 := Polynomial.primPart_ne_zero H
  have hS : ∀ m ∈ S, il m ≠ jl m := fun m hm => hijl m (Multiset.mem_toFinset.1 hm)
  have hEne : E ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm => X_pow_sub_X_pow_ne_zero (hS m hm)
  refine ⟨laumonIterToPlane D', fun h0 => mul_ne_zero hPne hEne ?_, ?_⟩
  · exact (laumonPlaneToIter_laumonIterToPlane D').symm.trans (by rw [h0, map_zero])
  intro k' _ _ _ a
  have ha : IsIntegral k a := IsIntegral.of_finite k a
  set ev := eval₂RingHom (algebraMap k k') a
  simp only [eval₂_laumonLine_eq_map, laumonPlaneToIter_laumonIterToPlane]
  have hPmap : H.primPart.map ev ≠ 0 :=
    map_eval₂RingHom_ne_zero_of_isPrimitive ha (Polynomial.isPrimitive_primPart H)
  have hEmap : E.map ev = ∏ m ∈ S, (X ^ il m - X ^ jl m : Polynomial k') := by
    simp [E, Polynomial.map_prod]
  have hEmap0 : E.map ev ≠ 0 :=
    hEmap ▸ Finset.prod_ne_zero_iff.2 fun m hm => X_pow_sub_X_pow_ne_zero (hS m hm)
  have hDmap : D'.map ev = H.primPart.map ev * E.map ev := by
    simp [D', Polynomial.map_mul]
  refine ⟨hDmap ▸ mul_ne_zero hPmap hEmap0, ?_⟩
  by_cases hca : Polynomial.aeval a c = 0
  · obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hc0
    have hprod : Polynomial.aeval a (UniqueFactorizationMonoid.normalizedFactors c).prod = 0 := by
      have h1 := congrArg (Polynomial.aeval a) hu
      rw [map_mul, hca] at h1
      exact (mul_eq_zero.1 h1).resolve_right ((u.isUnit.map (Polynomial.aeval a)).ne_zero)
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hprod
    obtain ⟨m, hm, hma⟩ := Multiset.mem_map.1 hprod
    refine ⟨m, hl m, hlQ m hm, hma, basicOpen_le_of_dvd ?_⟩
    rw [hDmap, hEmap]
    exact ((hdl m hm k' a hma).trans
      (Finset.dvd_prod_of_mem (fun m => (X ^ il m - X ^ jl m : Polynomial k'))
        (Multiset.mem_toFinset.2 hm))).trans (dvd_mul_left _ _)
  · refine ⟨0, h₀, hQ₀, by simp, basicOpen_le_of_dvd ?_⟩
    have hHmap : H.map ev = C (ev c) * H.primPart.map ev := by
      conv_lhs => rw [Polynomial.eq_C_content_mul_primPart H]
      rw [Polynomial.map_mul, Polynomial.map_C]
    have hu : IsUnit (C (ev c) : Polynomial k') :=
      Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by simpa [ev, Polynomial.aeval_def] using hca))
    rw [← hH, hHmap, hDmap, hu.mul_left_dvd]
    exact dvd_mul_right _ _

end Stacks.EtaleCohomology

end
