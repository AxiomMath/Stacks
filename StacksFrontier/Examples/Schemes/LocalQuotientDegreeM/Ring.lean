module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Two points on a line, and a curve through both: the algebra

This file is the pure commutative algebra underlying a counterexample to the global clause of
Stacks Tag 08E5. Everything happens in `A = ℚ[x, y]`, the coordinate ring of `X = Spec ℚ[x, y]`,
and inside its fraction field `K = ℚ(x, y)`.

Four primes of `A` are singled out: the prime `pL` of the line `L = V(x)`, the prime `pC` of the
affine curve `V(g)` for `g = x - y(y - 1)`, and the primes `p0` and `p1` of the two points
`p0 = (0, 0)` and `p1 = (0, 1)`, which both lie on `L` and on `V(g)`. Each is the kernel of an
explicit ring map to a domain.

For a prime `q` we realise the local ring of `A` at `q` as the subalgebra `Op q` of `K` of
fractions `a / s` with `s ∉ q`, and we write `VanishesAt q h` for the maximal ideal of `Op q`,
i.e. for the fractions `a / s` with `a ∈ q` and `s ∉ q`.

## Main definitions

* `Op`: the local ring of `A` at a prime `q`, as a subalgebra of `K`.
* `VanishesAt`: membership in the maximal ideal of `Op q`.

## Main results

* `vanishesAt_p1_of_mem_Op_of_g_mul`: a fraction which is regular at `p1` and is `g` times a
  fraction regular at `p0` vanishes at `p1`.
* `g_notMem`: a prime containing `x` but neither `y` nor `y - 1` does not contain `g`.
-/

@[expose] public section

namespace Stacks.Examples.LocalQuotientDegreeM

noncomputable section

/-- `k[x, y]` with `k = ℚ`. -/
public abbrev Poly : Type := MvPolynomial (Fin 2) ℚ

/-- The fraction field `k(x, y)`. -/
public abbrev Frac : Type := FractionRing Poly

/-- The first coordinate `x` of `k[x, y]`. -/
public def xv : Poly := MvPolynomial.X 0

/-- The second coordinate `y` of `k[x, y]`. -/
public def yv : Poly := MvPolynomial.X 1

/-- `g = x - y(y-1)`, the equation of the irreducible curve through the two points. -/
public def gpoly : Poly := xv - yv * (yv - 1)

/-- The parametrisation `x ↦ 0`, `y ↦ t` of the line `x = 0`. -/
public def lineHom : Poly →+* Polynomial ℚ :=
  (MvPolynomial.aeval fun i : Fin 2 => if i = 0 then 0 else Polynomial.X).toRingHom

/-- The parametrisation `x ↦ t² - t`, `y ↦ t` of the curve `g = 0`. -/
public def curveHom : Poly →+* Polynomial ℚ :=
  (MvPolynomial.aeval fun i : Fin 2 =>
    if i = 0 then Polynomial.X ^ 2 - Polynomial.X else Polynomial.X).toRingHom

/-- The prime of the line `L = V(x)`. -/
public def pL : Ideal Poly := RingHom.ker lineHom

/-- The prime of the curve `V(g)`. -/
public def pC : Ideal Poly := RingHom.ker curveHom

/-- The prime of the point `(0, 0)`. -/
public def p0 : Ideal Poly := RingHom.ker (MvPolynomial.eval fun _ : Fin 2 => (0 : ℚ))

/-- The prime of the point `(0, 1)`. -/
public def p1 : Ideal Poly :=
  RingHom.ker (MvPolynomial.eval fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)

/-- The ideal `pL` is prime. -/
public lemma prime_pL : pL.IsPrime := RingHom.ker_isPrime lineHom

/-- The ideal `pC` is prime. -/
public lemma prime_pC : pC.IsPrime := RingHom.ker_isPrime curveHom

/-- The ideal `p0` is prime. -/
public lemma prime_p0 : p0.IsPrime := RingHom.ker_isPrime _

/-- The ideal `p1` is prime. -/
public lemma prime_p1 : p1.IsPrime := RingHom.ker_isPrime _

/-- The polynomial `g` is nonzero. -/
public lemma g_ne_zero : gpoly ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval fun i : Fin 2 => if i = 0 then (0 : ℚ) else 2) h
  norm_num [gpoly, xv, yv] at this

/-- The coordinate `x` lies in `pL`. -/
public lemma x_mem_pL : xv ∈ pL := by
  simp [pL, xv, lineHom, RingHom.mem_ker]

/-- The coordinate `y` does not lie in `pL`. -/
public lemma y_notMem_pL : yv ∉ pL := by
  simp [pL, yv, lineHom, RingHom.mem_ker]

/-- Evaluating the parametrisation of the line at `t = 0` is the point `(0, 0)`. -/
public lemma evalZero_comp_lineHom :
    (Polynomial.evalRingHom (0 : ℚ)).comp lineHom =
      MvPolynomial.eval fun _ : Fin 2 => (0 : ℚ) := by
  apply MvPolynomial.ringHom_ext
  · simp [lineHom]
  · intro i
    by_cases h : i = 0 <;> simp [lineHom, h]

/-- Evaluating the parametrisation of the line at `t = 1` is the point `(0, 1)`. -/
public lemma evalOne_comp_lineHom :
    (Polynomial.evalRingHom (1 : ℚ)).comp lineHom =
      MvPolynomial.eval fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1 := by
  apply MvPolynomial.ringHom_ext
  · simp [lineHom]
  · intro i
    by_cases h : i = 0 <;> simp [lineHom, h]

/-- Evaluating the parametrisation of the curve at `t = 0` is the point `(0, 0)`. -/
public lemma evalZero_comp_curveHom :
    (Polynomial.evalRingHom (0 : ℚ)).comp curveHom =
      MvPolynomial.eval fun _ : Fin 2 => (0 : ℚ) := by
  apply MvPolynomial.ringHom_ext
  · simp [curveHom]
  · intro i
    by_cases h : i = 0 <;> simp [curveHom, h]

/-- Evaluating the parametrisation of the curve at `t = 1` is the point `(0, 1)`. -/
public lemma evalOne_comp_curveHom :
    (Polynomial.evalRingHom (1 : ℚ)).comp curveHom =
      MvPolynomial.eval fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1 := by
  apply MvPolynomial.ringHom_ext
  · simp [curveHom]
  · intro i
    by_cases h : i = 0 <;> simp [curveHom, h]

/-- If `c ∘ f = e`, then the kernel of `f` is contained in the kernel of `e`. -/
private theorem ker_le_ker_of_comp_eq {f : Poly →+* Polynomial ℚ} {e : Poly →+* ℚ}
    (c : Polynomial ℚ →+* ℚ) (h : c.comp f = e) : RingHom.ker f ≤ RingHom.ker e := by
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [← h, RingHom.comp_apply, hx, map_zero]

/-- The point `(0, 0)` lies on the line `L`. -/
public lemma pL_le_p0 : pL ≤ p0 := ker_le_ker_of_comp_eq _ evalZero_comp_lineHom

/-- The point `(0, 1)` lies on the line `L`. -/
public lemma pL_le_p1 : pL ≤ p1 := ker_le_ker_of_comp_eq _ evalOne_comp_lineHom

/-- The polynomial `g` lies in `pC`. -/
public lemma g_mem_pC : gpoly ∈ pC := by
  simp only [pC, RingHom.mem_ker, gpoly, xv, yv, curveHom, map_sub, map_mul, map_one,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
  norm_num
  ring

/-- The point `(0, 0)` lies on the curve `V(g)`. -/
public lemma pC_le_p0 : pC ≤ p0 := ker_le_ker_of_comp_eq _ evalZero_comp_curveHom

/-- The point `(0, 1)` lies on the curve `V(g)`. -/
public lemma pC_le_p1 : pC ≤ p1 := ker_le_ker_of_comp_eq _ evalOne_comp_curveHom

/-- The coordinate `y` lies in `p0`. -/
public lemma y_mem_p0 : yv ∈ p0 := by
  simp [p0, yv, RingHom.mem_ker]

/-- The coordinate `y` does not lie in `p1`. -/
public lemma y_notMem_p1 : yv ∉ p1 := by
  simp [p1, yv, RingHom.mem_ker]

/-- The polynomial `y - 1` does not lie in `p0`. -/
public lemma ysub1_notMem_p0 : yv - 1 ∉ p0 := by
  simp [p0, yv, RingHom.mem_ker]

/-- The polynomial `y - 1` lies in `p1`. -/
public lemma ysub1_mem_p1 : yv - 1 ∈ p1 := by
  simp [p1, yv, RingHom.mem_ker]

/-- A prime containing `x` but neither `y` nor `y - 1` does not contain `g`. -/
public lemma g_notMem {q : Ideal Poly} (hq : q.IsPrime) (hx : xv ∈ q) (hy : yv ∉ q)
    (hy1 : yv - 1 ∉ q) : gpoly ∉ q := by
  intro hg
  have h : yv * (yv - 1) ∈ q := by
    have hsub := q.sub_mem hx hg
    simpa [gpoly] using hsub
  exact (hq.mem_or_mem h).elim hy hy1

/-- The multiplicative set generated by the complement of `q`; for `q` prime it is exactly the
complement of `q`. -/
public def complMonoid (q : Ideal Poly) : Submonoid Poly := Submonoid.closure {s : Poly | s ∉ q}

/-- The multiplicative set `complMonoid q` consists of nonzero divisors. -/
public lemma complMonoid_le_nonZeroDivisors (q : Ideal Poly) :
    complMonoid q ≤ nonZeroDivisors Poly :=
  Submonoid.closure_le.mpr fun s hs =>
    mem_nonZeroDivisors_of_ne_zero fun h => hs (by rw [h]; exact q.zero_mem)

/-- The local ring of `A` at a prime, as a subalgebra of the fraction field. -/
public def Op (q : Ideal Poly) : Subalgebra Poly Frac :=
  Localization.subalgebra Frac (complMonoid q) (complMonoid_le_nonZeroDivisors q)

/-- An element of the fraction field lies in `Op q` if and only if it is a fraction `a / s`
with `s ∈ complMonoid q`. -/
public lemma mem_Op_iff' {q : Ideal Poly} {h : Frac} :
    h ∈ Op q ↔ ∃ a s : Poly, s ∈ complMonoid q ∧
      h * algebraMap Poly Frac s = algebraMap Poly Frac a := by
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    exact ⟨a, s, hs, IsLocalization.mk'_spec _ _ _⟩
  · rintro ⟨a, s, hs, he⟩
    exact ⟨a, s, hs, IsLocalization.eq_mk'_iff_mul_eq.mpr he⟩

/-- For a prime `q`, the multiplicative set `complMonoid q` is the complement of `q`. -/
public lemma mem_complMonoid_iff {q : Ideal Poly} (hq : q.IsPrime) {s : Poly} :
    s ∈ complMonoid q ↔ s ∉ q := by
  refine ⟨fun hs => ?_, fun hs => Submonoid.subset_closure hs⟩
  have := hq
  exact (Submonoid.closure_le.mpr fun t ht => (Ideal.mem_primeCompl_iff).mpr ht) hs

/-- For a prime `q`, an element of the fraction field lies in `Op q` if and only if it is a
fraction `a / s` with `s ∉ q`. -/
public lemma mem_Op_iff {q : Ideal Poly} (hq : q.IsPrime) {h : Frac} :
    h ∈ Op q ↔ ∃ a s : Poly, s ∉ q ∧ h * algebraMap Poly Frac s = algebraMap Poly Frac a := by
  simp only [mem_Op_iff', mem_complMonoid_iff hq]

/-- Every polynomial lies in `Op q`. -/
public lemma algebraMap_mem_Op (q : Ideal Poly) (a : Poly) : algebraMap Poly Frac a ∈ Op q :=
  (Op q).algebraMap_mem a

/-- The multiplicative set `complMonoid q` is antitone in `q`. -/
public lemma complMonoid_mono {q q' : Ideal Poly} (h : q ≤ q') :
    complMonoid q' ≤ complMonoid q := by
  simp only [complMonoid]
  exact Submonoid.closure_mono
    (show {s : Poly | s ∉ q'} ⊆ {s : Poly | s ∉ q} from fun _ ht htq => ht (h htq))

/-- For `q ≤ q'`, the local ring at `q'` is contained in the local ring at `q`. -/
public lemma Op_le_Op {q q' : Ideal Poly} (h : q ≤ q') : Op q' ≤ Op q := by
  intro z hz
  rw [mem_Op_iff'] at hz ⊢
  obtain ⟨a, s, hs, he⟩ := hz
  exact ⟨a, s, complMonoid_mono h hs, he⟩

/-- When `g` is a unit at `q`, every element regular at `q` is `g` times one. -/
public lemma exists_g_mul_of_mem_Op {q : Ideal Poly} (hq : q.IsPrime) (hg : gpoly ∉ q) {h : Frac}
    (hh : h ∈ Op q) : ∃ u ∈ Op q, h = algebraMap Poly Frac gpoly * u := by
  obtain ⟨a, s, hs, he⟩ := (mem_Op_iff hq).mp hh
  have hg0 : algebraMap Poly Frac gpoly ≠ 0 := fun h0 =>
    hg (by rw [IsFractionRing.injective Poly Frac (h0.trans (map_zero _).symm)]; exact q.zero_mem)
  refine ⟨h * (algebraMap Poly Frac gpoly)⁻¹, ?_, ?_⟩
  · rw [mem_Op_iff hq]
    refine ⟨a, gpoly * s, fun hmem => (hq.mem_or_mem hmem).elim hg hs, ?_⟩
    calc h * (algebraMap Poly Frac gpoly)⁻¹ * algebraMap Poly Frac (gpoly * s)
        = h * algebraMap Poly Frac s *
            ((algebraMap Poly Frac gpoly)⁻¹ * algebraMap Poly Frac gpoly) := by
          rw [map_mul]; ring
      _ = algebraMap Poly Frac a := by rw [inv_mul_cancel₀ hg0, mul_one, he]
  · rw [mul_comm, mul_assoc, inv_mul_cancel₀ hg0, mul_one]

/-- `h` lies in the maximal ideal of the local ring at `q`. -/
public def VanishesAt (q : Ideal Poly) (h : Frac) : Prop :=
  ∃ a s : Poly, a ∈ q ∧ s ∉ q ∧ h * algebraMap Poly Frac s = algebraMap Poly Frac a

/-- The zero element vanishes at a prime `q`. -/
public lemma vanishesAt_zero (q : Ideal Poly) (hq : q.IsPrime) : VanishesAt q 0 :=
  ⟨0, 1, q.zero_mem, fun h => hq.ne_top ((Ideal.eq_top_iff_one q).mpr h), by simp⟩

/-- The elements vanishing at a prime `q` are closed under addition. -/
public lemma vanishesAt_add {q : Ideal Poly} (hq : q.IsPrime) {h h' : Frac}
    (hh : VanishesAt q h) (hh' : VanishesAt q h') : VanishesAt q (h + h') := by
  obtain ⟨a, s, ha, hs, he⟩ := hh
  obtain ⟨b, t, hb, ht, he'⟩ := hh'
  refine ⟨a * t + b * s, s * t,
    q.add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb),
    fun hmem => (hq.mem_or_mem hmem).elim hs ht, ?_⟩
  rw [map_add, map_mul, map_mul, map_mul]
  calc (h + h') * (algebraMap Poly Frac s * algebraMap Poly Frac t)
      = h * algebraMap Poly Frac s * algebraMap Poly Frac t +
          h' * algebraMap Poly Frac t * algebraMap Poly Frac s := by ring
    _ = algebraMap Poly Frac a * algebraMap Poly Frac t +
          algebraMap Poly Frac b * algebraMap Poly Frac s := by rw [he, he']

/-- An element of `Op q` times an element vanishing at `q` vanishes at `q`. -/
public lemma vanishesAt_mul {q : Ideal Poly} (hq : q.IsPrime) {c h : Frac} (hc : c ∈ Op q)
    (hh : VanishesAt q h) : VanishesAt q (c * h) := by
  obtain ⟨b, t, ht, hbt⟩ := (mem_Op_iff hq).mp hc
  obtain ⟨a, s, ha, hs, he⟩ := hh
  refine ⟨b * a, t * s, Ideal.mul_mem_left _ _ ha,
    fun hmem => (hq.mem_or_mem hmem).elim ht hs, ?_⟩
  rw [map_mul, map_mul]
  calc c * h * (algebraMap Poly Frac t * algebraMap Poly Frac s)
      = c * algebraMap Poly Frac t * (h * algebraMap Poly Frac s) := by ring
    _ = algebraMap Poly Frac b * algebraMap Poly Frac a := by rw [hbt, he]

/-- The element `1` does not vanish at a prime `q`. -/
public lemma not_vanishesAt_one {q : Ideal Poly} (_hq : q.IsPrime) : ¬ VanishesAt q 1 := by
  rintro ⟨a, s, ha, hs, he⟩
  rw [one_mul] at he
  exact hs (by rw [IsFractionRing.injective Poly Frac he]; exact ha)

/-- An element of the fraction field that is regular at `p1` and is `g` times an element regular
at `p0` vanishes at `p1`. -/
public lemma vanishesAt_p1_of_mem_Op_of_g_mul {h : Frac} (h1 : h ∈ Op p1)
    (h0 : ∃ u ∈ Op p0, h = algebraMap Poly Frac gpoly * u) : VanishesAt p1 h := by
  obtain ⟨a, s, hs, he⟩ := (mem_Op_iff prime_p1).mp h1
  obtain ⟨u, hu, rfl⟩ := h0
  obtain ⟨b, t, ht, hbt⟩ := (mem_Op_iff prime_p0).mp hu
  by_cases ha : a ∈ p1
  · exact ⟨a, s, ha, hs, he⟩
  · exfalso
    have key : algebraMap Poly Frac (a * t) = algebraMap Poly Frac (gpoly * b * s) := by
      rw [map_mul, map_mul, map_mul, ← he, ← hbt]
      ring
    have key' : a * t = gpoly * b * s := IsFractionRing.injective Poly Frac key
    have hmem : a * t ∈ pC := by
      rw [key']
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ g_mem_pC)
    exact (prime_pC.mem_or_mem hmem).elim (fun h' => ha (pC_le_p1 h')) fun h' => ht (pC_le_p0 h')

end

end Stacks.Examples.LocalQuotientDegreeM

end
