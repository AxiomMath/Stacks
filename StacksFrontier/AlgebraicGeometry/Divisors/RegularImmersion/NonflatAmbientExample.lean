module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksCore.Tactic.StacksAttribute

/-!
# A relative effective Cartier divisor with nonflat ambient scheme

A relative effective Cartier divisor is flat over the base by definition, but the scheme it
sits in need not be — not even near the divisor.  Over a field `k`, with `A = k[t]` and

`B = k[t, x, y, x⁻¹y, x⁻²y, …] / (t y, t x⁻¹y, t x⁻²y, …)`,

the ring `B` is not flat over `A`, while `B / xB ≅ A` is, and `x` is a nonzerodivisor of `B`.
So the closed subscheme of `Spec B` cut out by `x` is a relative effective Cartier divisor over
`Spec A`, and no open neighbourhood of it is flat over `Spec A`.

## Main definitions

* `AlgebraicGeometry.NonflatAmbient.ambientRing`: the ring `B`, presented by generators and
  relations.
* `AlgebraicGeometry.NonflatAmbient.baseMap`: the structural map `A = k[t] ⟶ B`.
* `AlgebraicGeometry.NonflatAmbient.divisor`: the closed subscheme of `Spec B` cut out by `x`.

## Main results

* `AlgebraicGeometry.NonflatAmbient.not_flat_ambientRing`: `B` is not flat over `A`.
* `AlgebraicGeometry.NonflatAmbient.quotientByX_equiv_polynomial`: `B / xB ≅ A`.
* `AlgebraicGeometry.NonflatAmbient.quotientByX_flat`: `B / xB` is flat over `A`.
* `AlgebraicGeometry.NonflatAmbient.x_isRegular`: `x` is a nonzerodivisor of `B`.
* `AlgebraicGeometry.NonflatAmbient.divisor_isRelativeEffectiveCartierDivisor`: the divisor is a
  relative effective Cartier divisor over `Spec A`.
* `AlgebraicGeometry.NonflatAmbient.no_flat_neighbourhood`: no open subscheme of `Spec B`
  containing the divisor is flat over `Spec A`.

## References

* [Stacks Project, Tag 062X](https://stacks.math.columbia.edu/tag/062X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.NonflatAmbient

variable (k : Type u) [Field k]

/-- The index set of the generators: `none` is `t`, `some 0` is `x`, and `some (n + 1)` is the
generator standing for `x⁻ⁿ y`. -/
abbrev Variable := Option ℕ

/-- The free polynomial algebra on the generators, before the relations are imposed. -/
abbrev Presentation := MvPolynomial Variable k

/-- The polynomial generator `t`. -/
def tPoly : Presentation k := MvPolynomial.X none

/-- The polynomial generator `x`. -/
def xPoly : Presentation k := MvPolynomial.X (some 0)

/-- The polynomial generator `yₙ`, standing for `x⁻ⁿ y`. -/
def yPoly (n : ℕ) : Presentation k := MvPolynomial.X (some (n + 1))

/-- The relations: each `yₙ` is killed by `t`, dividing `yₙ₊₁` by `x` gives `yₙ`, and the
product of `yₘ` and `yₙ` depends only on `m + n`. -/
def relationsIdeal : Ideal (Presentation k) :=
  Ideal.span ((Set.range fun n : ℕ => tPoly k * yPoly k n) ∪
    (Set.range fun n : ℕ => xPoly k * yPoly k (n + 1) - yPoly k n) ∪
    (Set.range fun ij : ℕ × ℕ =>
      yPoly k ij.1 * yPoly k ij.2 - yPoly k 0 * yPoly k (ij.1 + ij.2)))

/-- **Stacks Project, Tag 062X.** The ring `B = k[t, x, y, x⁻¹y, …] / (ty, tx⁻¹y, …)`. -/
abbrev ambientRing := Presentation k ⧸ relationsIdeal k

/-- The image of `t` in the ambient ring. -/
def t : ambientRing k := Ideal.Quotient.mk (relationsIdeal k) (tPoly k)

/-- The image of `x` in the ambient ring. -/
def x : ambientRing k := Ideal.Quotient.mk (relationsIdeal k) (xPoly k)

/-- **Stacks Project, Tag 062X.** The structural map `k[t] → B`, sending the coordinate to the
class of `t`. -/
def baseMap : Polynomial k →+* ambientRing k :=
  (Polynomial.aeval (t k)).toRingHom

/-- **Stacks Project, Tag 062X.** The closed subscheme of `Spec B` cut out by `x`. -/
def divisor : (Spec (.of (ambientRing k))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {((Scheme.ΓSpecIso (.of (ambientRing k))).inv (x k))})

/-- Evaluation into the field of rational functions `k(X)` with `t ↦ 0`, `x ↦ X` and
`yₙ ↦ X⁻ⁿ`. -/
private def witnessEvaluation : Presentation k →+* RatFunc k :=
  (MvPolynomial.aeval (R := k) (S₁ := RatFunc k)
    (fun v : Variable => match v with
      | none => 0
      | some 0 => RatFunc.X
      | some (n + 1) => RatFunc.X ^ (-(n : ℤ)))).toRingHom

/-- A ring map out of the free algebra kills `relationsIdeal` once it kills each generator. -/
private lemma relationsIdeal_le_ker {S : Type*} [CommRing S] (f : Presentation k →+* S)
    (ht : ∀ n, f (tPoly k * yPoly k n) = 0)
    (hx : ∀ n, f (xPoly k * yPoly k (n + 1) - yPoly k n) = 0)
    (hy : ∀ i j, f (yPoly k i * yPoly k j - yPoly k 0 * yPoly k (i + j)) = 0) :
    relationsIdeal k ≤ RingHom.ker f := by
  apply Ideal.span_le.mpr
  rintro z ((⟨n, rfl⟩ | ⟨n, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  exacts [ht n, hx n, hy i j]

private def witnessMap : ambientRing k →+* RatFunc k :=
  Ideal.Quotient.lift (relationsIdeal k) (witnessEvaluation k)
    (relationsIdeal_le_ker k _ (fun n => by simp [witnessEvaluation, tPoly, yPoly])
      (fun n => by
        simp [witnessEvaluation, xPoly, yPoly]
        field_simp [RatFunc.X_ne_zero]
        ring)
      (fun i j => by
        simp [witnessEvaluation, yPoly]
        field_simp [RatFunc.X_ne_zero]
        ring))

private def yZero : ambientRing k :=
  Ideal.Quotient.mk (relationsIdeal k) (yPoly k 0)

private lemma witnessMap_yZero : witnessMap k (yZero k) = 1 := by
  simp [witnessMap, yZero, witnessEvaluation, yPoly]

private lemma yZero_ne_zero : yZero k ≠ 0 := by
  intro h
  have := congrArg (witnessMap k) h
  simp [witnessMap_yZero] at this

private lemma t_mul_yZero : (t k) * yZero k = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  show tPoly k * yPoly k 0 ∈ relationsIdeal k
  exact Ideal.subset_span (Or.inl (Or.inl ⟨0, rfl⟩))

/-- The ring `B` is not flat over `k[t]`. -/
@[stacks 062X "ambient ring not flat"]
theorem not_flat_ambientRing : ¬ RingHom.Flat (baseMap k) := by
  intro hflat
  let _ : Algebra (Polynomial k) (ambientRing k) := (baseMap k).toAlgebra
  rw [RingHom.Flat] at hflat
  let _ : Module.Flat (Polynomial k) (ambientRing k) := hflat
  have hX : IsRegular (Polynomial.X : Polynomial k) :=
    isRegular_iff_ne_zero.mpr Polynomial.X_ne_zero
  have hinj : IsSMulRegular (ambientRing k) (Polynomial.X : Polynomial k) :=
    Module.Flat.isSMulRegular_of_isRegular
      (R := Polynomial k) (M := ambientRing k) hX
  have hkill : (Polynomial.X : Polynomial k) • yZero k = 0 := by
    show (baseMap k (Polynomial.X : Polynomial k)) * yZero k = 0
    rw [show baseMap k (Polynomial.X : Polynomial k) = t k by simp [baseMap]]
    exact t_mul_yZero k
  have heq : (Polynomial.X : Polynomial k) • yZero k =
      (Polynomial.X : Polynomial k) • (0 : ambientRing k) := by
    have hz : (Polynomial.X : Polynomial k) • (0 : ambientRing k) = 0 :=
      @smul_zero (Polynomial k) (ambientRing k) _ _ (Polynomial.X : Polynomial k)
    exact hkill.trans hz.symm
  exact yZero_ne_zero k (hinj heq)

private def quotientToPolynomial : Presentation k →+* Polynomial k :=
  MvPolynomial.eval₂Hom (algebraMap k (Polynomial k))
    (fun v : Variable => match v with
      | none => Polynomial.X
      | some _ => 0)

private def quotientFromPolynomial :
    Polynomial k →+* (ambientRing k ⧸ Ideal.span {x k}) :=
  (Ideal.Quotient.mk (Ideal.span {x k})).comp (baseMap k)

private lemma quotientFromPolynomial_C (a : k) :
    quotientFromPolynomial k (Polynomial.C a) =
      Ideal.Quotient.mk (Ideal.span {x k}) (algebraMap k (ambientRing k) a) := by
  simp [quotientFromPolynomial, baseMap, Polynomial.aeval_def]

private lemma algebraMap_ambient_eq_C (a : k) :
    algebraMap k (ambientRing k) a =
      Ideal.Quotient.mk (relationsIdeal k) (MvPolynomial.C a) :=
  rfl

private def quotientToPolynomialLift :
    ambientRing k ⧸ Ideal.span {x k} →+* Polynomial k := by
  let f : Presentation k →+* Polynomial k := quotientToPolynomial k
  have hrel : relationsIdeal k ≤ RingHom.ker f :=
    relationsIdeal_le_ker k f (fun n => by simp [f, quotientToPolynomial, tPoly, yPoly])
      (fun n => by simp [f, quotientToPolynomial, xPoly, yPoly])
      (fun i j => by simp [f, quotientToPolynomial, yPoly])
  let g : ambientRing k →+* Polynomial k := Ideal.Quotient.lift _ f hrel
  have hx : x k ∈ RingHom.ker g := by
    change g (Ideal.Quotient.mk _ (xPoly k)) = 0
    simp [g, f, quotientToPolynomial, xPoly]
  have hspan : Ideal.span {x k} ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hx
  exact Ideal.Quotient.lift _ g (fun a ha => RingHom.mem_ker.mp (hspan ha))

private lemma quotientToPolynomialLift_mk (p : Presentation k) :
    quotientToPolynomialLift k
      (Ideal.Quotient.mk (Ideal.span {x k})
        (Ideal.Quotient.mk (relationsIdeal k) p)) = quotientToPolynomial k p := by
  simp [quotientToPolynomialLift, quotientToPolynomial, Ideal.Quotient.lift_mk]

private lemma x_mul_yPoly_succ (n : ℕ) :
    x k * Ideal.Quotient.mk (relationsIdeal k) (yPoly k (n + 1)) =
      Ideal.Quotient.mk (relationsIdeal k) (yPoly k n) := by
  show Ideal.Quotient.mk (relationsIdeal k) (xPoly k * yPoly k (n + 1)) = _
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span (Or.inl (Or.inr ⟨n, rfl⟩))

private lemma quotient_yPoly_eq_zero (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {x k})
      (Ideal.Quotient.mk (relationsIdeal k) (yPoly k n)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← x_mul_yPoly_succ]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

private lemma quotient_x_eq_zero :
    Ideal.Quotient.mk (Ideal.span {x k}) (x k) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- The weight giving each `yₙ` degree one and `t`, `x` degree zero. -/
private def yWeight : Variable → ℕ
  | none => 0
  | some 0 => 0
  | some (_ + 1) => 1

/-- The reindexing `yₙ ↦ yₙ₊₁` fixing `t` and `x`; on the quotient it is division by `x` in
positive weight. -/
private def shiftVariable : Variable → Variable
  | none => none
  | some 0 => some 0
  | some (n + 1) => some (n + 2)

private def shiftPresentation : Presentation k →+* Presentation k :=
  (MvPolynomial.rename shiftVariable : Presentation k →ₐ[k] Presentation k).toRingHom

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- `t` has weight zero. -/
private lemma tPoly_isWeightedHomogeneous : (tPoly k).IsWeightedHomogeneous yWeight 0 := by
  simpa [tPoly, yWeight] using (MvPolynomial.isWeightedHomogeneous_X (R := k) yWeight none)

/-- `x` has weight zero. -/
private lemma xPoly_isWeightedHomogeneous : (xPoly k).IsWeightedHomogeneous yWeight 0 := by
  simpa [xPoly, yWeight] using (MvPolynomial.isWeightedHomogeneous_X (R := k) yWeight (some 0))

/-- Each `yₙ` has weight one. -/
private lemma yPoly_isWeightedHomogeneous (n : ℕ) :
    (yPoly k n).IsWeightedHomogeneous yWeight 1 := by
  simpa [yPoly, yWeight] using
    (MvPolynomial.isWeightedHomogeneous_X (R := k) yWeight (some (n + 1)))

private lemma relationsIdeal_isHomogeneous :
    Ideal.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule k yWeight)
      (relationsIdeal k) := by
  apply Ideal.homogeneous_span
  have hT := tPoly_isWeightedHomogeneous k
  have hX := xPoly_isWeightedHomogeneous k
  have hY := yPoly_isWeightedHomogeneous k
  rintro z ((⟨n, rfl⟩ | ⟨n, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · exact ⟨1, (MvPolynomial.mem_weightedHomogeneousSubmodule ..).mpr (hT.mul (hY n))⟩
  · exact ⟨1, (MvPolynomial.mem_weightedHomogeneousSubmodule ..).mpr
      ((hX.mul (hY (n + 1))).sub (hY n))⟩
  · exact ⟨2, (MvPolynomial.mem_weightedHomogeneousSubmodule ..).mpr
      (((hY i).mul (hY j)).sub ((hY 0).mul (hY (i + j))))⟩

private lemma weightedComponent_x_mul (n : ℕ) (p : Presentation k) :
    MvPolynomial.weightedHomogeneousComponent yWeight n (xPoly k * p) =
      xPoly k * MvPolynomial.weightedHomogeneousComponent yWeight n p := by
  classical
  ext d
  by_cases hd : d (some 0) = 0
  · simp [MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_X_mul', xPoly, hd]
  · have hw := Finsupp.weight_sub_single_add (w := yWeight) hd
    simp only [MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_X_mul', xPoly] at ⊢
    rw [show yWeight (some 0) = 0 by rfl] at hw
    simp only [add_zero] at hw
    have hiff : (Finsupp.weight yWeight d = n) ↔
        (Finsupp.weight yWeight (d - Finsupp.single (some 0) 1) = n) := by
      rw [hw]
    simp [hd, hiff]

private def shiftToAmbient : Presentation k →+* ambientRing k :=
  (Ideal.Quotient.mk (relationsIdeal k)).comp (shiftPresentation k)

private lemma shiftPresentation_preserves_relations :
    relationsIdeal k ≤ RingHom.ker (shiftToAmbient k) := by
  refine relationsIdeal_le_ker k _ (fun n => ?_) (fun n => ?_) (fun i j => ?_)
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span
      (Or.inl (Or.inl ⟨n + 1, by simp [shiftPresentation, shiftVariable, tPoly, yPoly]⟩))
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span
      (Or.inl (Or.inr ⟨n + 1, by simp [shiftPresentation, shiftVariable, xPoly, yPoly]⟩))
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simp only [map_sub, map_mul]
    have h₁ : yPoly k (i + 1) * yPoly k (j + 1) -
        yPoly k 0 * yPoly k (i + j + 2) ∈ relationsIdeal k :=
      Ideal.subset_span (Or.inr ⟨(i + 1, j + 1), by simp only [yPoly]; ring_nf⟩)
    have h₂ : yPoly k 1 * yPoly k (i + j + 1) -
        yPoly k 0 * yPoly k (i + j + 2) ∈ relationsIdeal k :=
      Ideal.subset_span (Or.inr ⟨(1, i + j + 1), by simp only [yPoly]; ring_nf⟩)
    have h : yPoly k (i + 1) * yPoly k (j + 1) -
        yPoly k 1 * yPoly k (i + j + 1) ∈ relationsIdeal k := by
      rw [show yPoly k (i + 1) * yPoly k (j + 1) - yPoly k 1 * yPoly k (i + j + 1) =
          (yPoly k (i + 1) * yPoly k (j + 1) - yPoly k 0 * yPoly k (i + j + 2)) -
          (yPoly k 1 * yPoly k (i + j + 1) - yPoly k 0 * yPoly k (i + j + 2)) by ring]
      exact (relationsIdeal k).sub_mem h₁ h₂
    simpa [shiftPresentation, shiftVariable, yPoly, add_assoc, add_comm,
      add_left_comm] using h

private def shiftAmbient : ambientRing k →+* ambientRing k :=
  Ideal.Quotient.lift (relationsIdeal k) (shiftToAmbient k)
    (shiftPresentation_preserves_relations k)

private lemma shiftAmbient_mk (p : Presentation k) :
    shiftAmbient k (Ideal.Quotient.mk (relationsIdeal k) p) =
      Ideal.Quotient.mk (relationsIdeal k) (shiftPresentation k p) := by
  simp [shiftAmbient, shiftToAmbient, shiftPresentation]

private lemma shiftAmbient_X (v : Variable) :
    shiftAmbient k (Ideal.Quotient.mk (relationsIdeal k) (MvPolynomial.X v)) =
      Ideal.Quotient.mk (relationsIdeal k) (MvPolynomial.X (shiftVariable v)) := by
  rw [shiftAmbient_mk]
  simp [shiftPresentation]

/-- Two ring maps out of a polynomial ring that agree on constants and differ on each variable
by a fixed scalar raised to its weight differ on a weighted-homogeneous polynomial of weight
`n` by that scalar raised to `n`. -/
private lemma weighted_hom_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    {σ : Type*} (w : σ → ℕ) (f g : MvPolynomial σ R →+* S) (a : S)
    (hC : ∀ r, f (MvPolynomial.C r) = g (MvPolynomial.C r))
    (hX : ∀ i, f (MvPolynomial.X i) = a ^ w i * g (MvPolynomial.X i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous w n) :
    f p = a ^ n * g p := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq, mul_add]
  | monomial d r hd =>
    simp only [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      hC, hX, mul_pow, ← pow_mul, Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    have hd' : ∑ i ∈ d.support, w i * d i = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_comm] using hd
    rw [hd']
    ring

private lemma shift_homogeneous (p : Presentation k) (n : ℕ)
    (hp : p.IsWeightedHomogeneous yWeight n) :
    Ideal.Quotient.mk (relationsIdeal k) p =
      x k ^ n * shiftAmbient k (Ideal.Quotient.mk (relationsIdeal k) p) := by
  apply weighted_hom_eq yWeight (Ideal.Quotient.mk (relationsIdeal k))
    ((shiftAmbient k).comp (Ideal.Quotient.mk (relationsIdeal k))) (x k) ?_ ?_ hp
  · intro a
    simp [shiftAmbient_mk, shiftPresentation]
  · intro v
    simp only [RingHom.comp_apply, shiftAmbient_X]
    cases v with
    | none => simp [yWeight, shiftVariable]
    | some i =>
      cases i with
      | zero => simp [yWeight, shiftVariable]
      | succ i =>
        simpa [yWeight, shiftVariable, yPoly] using (x_mul_yPoly_succ k i).symm

/-- Setting every `yₙ` to zero; the identity in weight zero. -/
private def eraseY : Presentation k →+* Presentation k :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v => (0 : Presentation k) ^ yWeight v * MvPolynomial.X v)

private lemma eraseY_homogeneous_zero (p : Presentation k)
    (hp : p.IsWeightedHomogeneous yWeight 0) : eraseY k p = p := by
  have h := weighted_hom_eq yWeight (eraseY k) (RingHom.id _) 0
    (by intro r; simp [eraseY]) (by intro i; simp [eraseY]) hp
  simpa using h

private lemma relationsIdeal_le_ker_eraseY :
    relationsIdeal k ≤ RingHom.ker (eraseY k) :=
  relationsIdeal_le_ker k _ (fun n => by simp [eraseY, tPoly, yPoly, yWeight])
    (fun n => by simp [eraseY, xPoly, yPoly, yWeight])
    (fun i j => by simp [eraseY, yPoly, yWeight])

private lemma x_mul_eq_zero (b : ambientRing k) (hb : x k * b = 0) : b = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem k yWeight
    (relationsIdeal_isHomogeneous k) p).mpr
  intro n
  set q := MvPolynomial.weightedHomogeneousComponent yWeight n p with hqdef
  have hq : q.IsWeightedHomogeneous yWeight n :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous n p
  have hmem : xPoly k * q ∈ relationsIdeal k := by
    have hm : xPoly k * p ∈ relationsIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp hb
    simpa [hqdef, weightedComponent_x_mul] using
      MvPolynomial.weightedHomogeneousComponent_mem_of_mem k yWeight
        (relationsIdeal_isHomogeneous k) hm n
  cases n with
  | zero =>
    have he : eraseY k (xPoly k * q) = 0 := relationsIdeal_le_ker_eraseY k hmem
    rw [map_mul, eraseY_homogeneous_zero k q hq] at he
    have hx : eraseY k (xPoly k) = xPoly k := by simp [eraseY, xPoly, yWeight]
    rw [hx] at he
    have hq0 : q = 0 :=
      (mul_eq_zero.mp he).resolve_left (MvPolynomial.X_ne_zero (some 0))
    show q ∈ relationsIdeal k
    rw [hq0]
    exact (relationsIdeal k).zero_mem
  | succ n =>
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he : x k * Ideal.Quotient.mk (relationsIdeal k) q = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hs := congrArg (shiftAmbient k) he
    have hsx : shiftAmbient k (x k) = x k := by
      simpa [x, xPoly, shiftVariable] using shiftAmbient_X k (some 0)
    simp only [map_mul, hsx, map_zero] at hs
    rw [shift_homogeneous k q (n + 1) hq, pow_succ, mul_assoc, hs, mul_zero]

/-- The quotient `B / xB` is isomorphic to `k[t]` by a ring isomorphism carrying the class of `t`
to the coordinate and constants to constants. -/
@[stacks 062X "quotient by x"]
theorem quotientByX_equiv_polynomial :
    ∃ e : (ambientRing k ⧸ Ideal.span {x k}) ≃+* Polynomial k,
      e (Ideal.Quotient.mk (Ideal.span {x k}) (t k)) = Polynomial.X ∧
        ∀ a : k,
          e (Ideal.Quotient.mk (Ideal.span {x k})
            (algebraMap k (ambientRing k) a)) = Polynomial.C a := by
  let f := quotientToPolynomialLift k
  let g := quotientFromPolynomial k
  have hfg : f.comp g = RingHom.id (Polynomial k) := by
    apply Polynomial.ringHom_ext
    · intro a
      show quotientToPolynomialLift k (quotientFromPolynomial k (Polynomial.C a)) = _
      rw [quotientFromPolynomial_C, algebraMap_ambient_eq_C, quotientToPolynomialLift_mk]
      simp [quotientToPolynomial]
    · simp [f, g, quotientToPolynomialLift, quotientFromPolynomial,
        quotientToPolynomial, t, tPoly, baseMap]
  have hgf : g.comp f = RingHom.id (ambientRing k ⧸ Ideal.span {x k}) := by
    repeat apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      show g (f (Ideal.Quotient.mk (Ideal.span {x k})
        (Ideal.Quotient.mk (relationsIdeal k) (MvPolynomial.C a)))) = _
      rw [quotientToPolynomialLift_mk]
      simp only [RingHom.comp_apply, RingHom.id_apply]
      have hC : quotientToPolynomial k (MvPolynomial.C a) = Polynomial.C a := by
        simp [quotientToPolynomial]
      rw [hC]
      show quotientFromPolynomial k (Polynomial.C a) = _
      rw [quotientFromPolynomial_C, algebraMap_ambient_eq_C]
    · intro v
      cases v with
      | none =>
        show g (f (Ideal.Quotient.mk (Ideal.span {x k})
          (Ideal.Quotient.mk (relationsIdeal k) (tPoly k)))) = _
        rw [quotientToPolynomialLift_mk]
        have heval : quotientToPolynomial k (tPoly k) = Polynomial.X := by
          simp [quotientToPolynomial, tPoly]
        rw [heval]
        simp [g, quotientFromPolynomial, baseMap, t, tPoly]
      | some n =>
        cases n with
        | zero =>
          show g (f (Ideal.Quotient.mk (Ideal.span {x k})
            (Ideal.Quotient.mk (relationsIdeal k) (xPoly k)))) = _
          rw [quotientToPolynomialLift_mk]
          have heval : quotientToPolynomial k (xPoly k) = 0 := by
            simp [quotientToPolynomial, xPoly]
          rw [heval, map_zero]
          simp only [RingHom.comp_apply, RingHom.id_apply]
          show 0 = Ideal.Quotient.mk (Ideal.span {x k}) (x k)
          exact (quotient_x_eq_zero k).symm
        | succ n =>
          show g (f (Ideal.Quotient.mk (Ideal.span {x k})
            (Ideal.Quotient.mk (relationsIdeal k) (yPoly k n)))) = _
          rw [quotientToPolynomialLift_mk]
          have heval : quotientToPolynomial k (yPoly k n) = 0 := by
            simp [quotientToPolynomial, yPoly]
          rw [heval, map_zero]
          simp only [RingHom.comp_apply, RingHom.id_apply]
          show 0 = Ideal.Quotient.mk (Ideal.span {x k})
            (Ideal.Quotient.mk (relationsIdeal k) (yPoly k n))
          exact (quotient_yPoly_eq_zero k n).symm
  refine ⟨RingEquiv.ofRingHom f g hfg hgf, ?_, ?_⟩
  · have h := congrArg (fun h : Polynomial k →+* Polynomial k => h Polynomial.X) hfg
    simpa [f, g, quotientFromPolynomial, baseMap] using h
  · intro a
    have h := congrArg (fun h : Polynomial k →+* Polynomial k => h (Polynomial.C a)) hfg
    rw [← quotientFromPolynomial_C k a]
    simpa [f, g, quotientFromPolynomial] using h

/-- The quotient `B / xB` is flat over `k[t]`. -/
@[stacks 062X "quotient by x flat"]
theorem quotientByX_flat :
    RingHom.Flat
      ((Ideal.Quotient.mk (Ideal.span {x k})).comp (baseMap k)) := by
  obtain ⟨e, ht, ha⟩ := quotientByX_equiv_polynomial k
  let f : Polynomial k →+* ambientRing k ⧸ Ideal.span {x k} :=
    (Ideal.Quotient.mk (Ideal.span {x k})).comp (baseMap k)
  have he : e.toRingHom.comp f = RingHom.id (Polynomial k) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
      rw [show f (Polynomial.C a) = Ideal.Quotient.mk (Ideal.span {x k})
        (algebraMap k (ambientRing k) a) by simp [f, baseMap, Polynomial.aeval_def]]
      exact ha a
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
      rw [show f Polynomial.X = Ideal.Quotient.mk (Ideal.span {x k}) (t k) by simp [f, baseMap]]
      exact ht
  have hid : RingHom.Flat (e.toRingHom.comp f) := by
    rw [he]
    exact RingHom.Flat.id (Polynomial k)
  exact (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mp hid

/-- The element `x` is a nonzerodivisor of `B`. -/
@[stacks 062X "x nonzerodivisor"]
theorem x_isRegular : IsRegular (x k) := by
  rw [isRegular_iff_eq_zero_of_mul]
  exact ⟨x_mul_eq_zero k, fun b hb => x_mul_eq_zero k b (by simpa [mul_comm] using hb)⟩

/-- A closed subscheme of an affine scheme cut out on the whole space by a single
nonzerodivisor is an effective Cartier divisor. -/
private lemma effectiveCartier_of_principal {X : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (f : Γ(X, ⊤)) (hf : IsRegular f)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {f}) :
    Stacks.Divisors.IsEffectiveCartierDivisor I :=
  Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen I
    fun _ => ⟨⊤, isAffineOpen_top X, trivial, f, hf, hI⟩

private lemma divisor_flat :
    Flat ((divisor k).subschemeι ≫ Spec.map (CommRingCat.ofHom (baseMap k))) := by
  let X := Spec (.of (ambientRing k))
  let e := (Scheme.ΓSpecIso (.of (ambientRing k))).commRingCatIsoToRingEquiv
  let ι := (Scheme.ΓSpecIso (.of (Polynomial k))).commRingCatIsoToRingEquiv
  have : IsAffine (divisor k).subscheme :=
    isAffine_of_isAffineHom (divisor k).subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  set χ := ((Spec.map (CommRingCat.ofHom (baseMap k))).appTop).hom with hχ
  have hsurj : Function.Surjective ((divisor k).subschemeι.appTop).hom :=
    (divisor k).subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩
  set K := RingHom.ker ((divisor k).subschemeι.appTop).hom with hK
  let q := RingHom.quotientKerEquivOfSurjective hsurj
  have hψ : ((divisor k).subschemeι.appTop).hom.comp χ =
      q.toRingHom.comp ((Ideal.Quotient.mk K).comp χ) := by
    refine RingHom.ext fun a => ?_
    exact (RingHom.kerLift_mk ((divisor k).subschemeι.appTop).hom (χ a)).symm
  rw [hψ]
  refine (RingHom.Flat.comp_iff_of_bijective_left (f := (Ideal.Quotient.mk K).comp χ)
    (g := q.toRingHom) q.bijective).mpr ?_
  have hKideal : K = (divisor k).ideal ⟨⊤, isAffineOpen_top X⟩ :=
    (divisor k).ker_subschemeι_app ⟨⊤, isAffineOpen_top X⟩
  have hJ : Ideal.span {x k} = K.map (e : _ →+* ambientRing k) := by
    rw [hKideal]
    simp only [divisor, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_leOfHom,
      Ideal.map_span, Set.image_singleton]
    exact congrArg (fun b : ambientRing k => Ideal.span {b}) (e.apply_symm_apply (x k)).symm
  let eQ := Ideal.quotientEquiv K (Ideal.span {x k}) e hJ
  refine (RingHom.Flat.comp_iff_of_bijective_left (f := (Ideal.Quotient.mk K).comp χ)
    (g := eQ.toRingHom) eQ.bijective).mp ?_
  have hnat : (e : _ →+* ambientRing k).comp χ = (baseMap k).comp ι.toRingHom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (baseMap k)))
  have hcomp : eQ.toRingHom.comp ((Ideal.Quotient.mk K).comp χ) =
      ((Ideal.Quotient.mk (Ideal.span {x k})).comp (baseMap k)).comp
        ι.toRingHom := by
    refine RingHom.ext fun a => ?_
    show Ideal.quotientEquiv K (Ideal.span {x k}) e hJ (Ideal.Quotient.mk K (χ a)) = _
    rw [Ideal.quotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk (Ideal.span {x k}))
      (congrArg (fun h : _ →+* ambientRing k => h a) hnat)
  rw [hcomp]
  exact (RingHom.Flat.comp_iff_of_bijective_right
    (f := (Ideal.Quotient.mk (Ideal.span {x k})).comp (baseMap k))
    (g := ι.toRingHom) ι.bijective).mpr (quotientByX_flat k)

/-- The closed subscheme of `Spec B` cut out by `x` is a relative effective Cartier divisor over
`Spec k[t]`. -/
@[stacks 062X "relative effective Cartier divisor"]
theorem divisor_isRelativeEffectiveCartierDivisor :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor
      (Spec.map (CommRingCat.ofHom (baseMap k))) (divisor k) := by
  refine ⟨?_, divisor_flat k⟩
  apply effectiveCartier_of_principal (divisor k)
    ((Scheme.ΓSpecIso (.of (ambientRing k))).inv (x k))
  · let e := (Scheme.ΓSpecIso (.of (ambientRing k))).commRingCatIsoToRingEquiv
    rw [isRegular_iff_eq_zero_of_mul]
    have h (a : Γ(Spec (.of (ambientRing k)), ⊤))
        (ha : (Scheme.ΓSpecIso (.of (ambientRing k))).inv (x k) * a = 0) : a = 0 := by
      apply e.injective
      have hm := congrArg e ha
      simp only [map_mul, map_zero] at hm
      rw [show e ((Scheme.ΓSpecIso (.of (ambientRing k))).inv (x k)) = x k from
        e.apply_symm_apply _] at hm
      simpa using x_mul_eq_zero k (e a) hm
    exact ⟨h, fun a ha => h a (by simpa [mul_comm] using ha)⟩
  · simp [divisor]

/-- Evaluation into `k(x)[T]` with each `yₙ` sent to `x⁻ⁿ T`; its kernel is the generic point of
the component of `Spec B` on which `y` does not vanish. -/
private def genericEvaluation : Presentation k →+* Polynomial (RatFunc k) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k (RatFunc k)))
    (fun v => Polynomial.X ^ yWeight v *
      Polynomial.C (witnessEvaluation k (MvPolynomial.X v)))

private lemma genericEvaluation_homogeneous (p : Presentation k) (n : ℕ)
    (hp : p.IsWeightedHomogeneous yWeight n) :
    genericEvaluation k p = Polynomial.X ^ n * Polynomial.C (witnessEvaluation k p) := by
  apply weighted_hom_eq yWeight (genericEvaluation k)
    (Polynomial.C.comp (witnessEvaluation k)) Polynomial.X ?_ ?_ hp
  · intro a
    simp [genericEvaluation, witnessEvaluation]
  · intro v
    simp [genericEvaluation]

private lemma relationsIdeal_le_ker_genericEvaluation :
    relationsIdeal k ≤ RingHom.ker (genericEvaluation k) := by
  have hw (p : Presentation k) (n : ℕ) (hp : p.IsWeightedHomogeneous yWeight n)
      (hm : p ∈ relationsIdeal k) : genericEvaluation k p = 0 := by
    have he : witnessEvaluation k p = 0 :=
      congrArg (witnessMap k) (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
    rw [genericEvaluation_homogeneous k p n hp, he, map_zero, mul_zero]
  have hT := tPoly_isWeightedHomogeneous k
  have hX := xPoly_isWeightedHomogeneous k
  have hY := yPoly_isWeightedHomogeneous k
  refine relationsIdeal_le_ker k _ (fun n => ?_) (fun n => ?_) (fun i j => ?_)
  · exact hw _ 1 (hT.mul (hY n)) (Ideal.subset_span (Or.inl (Or.inl ⟨n, rfl⟩)))
  · exact hw _ 1 ((hX.mul (hY (n + 1))).sub (hY n))
      (Ideal.subset_span (Or.inl (Or.inr ⟨n, rfl⟩)))
  · exact hw _ 2 (((hY i).mul (hY j)).sub ((hY 0).mul (hY (i + j))))
      (Ideal.subset_span (Or.inr ⟨(i, j), rfl⟩))

private def genericMap : ambientRing k →+* Polynomial (RatFunc k) :=
  Ideal.Quotient.lift _ (genericEvaluation k) (relationsIdeal_le_ker_genericEvaluation k)

/-- Evaluation killing every `yₙ` and `t`, with `x ↦ X`: the `x`-axis. -/
private def axisEvaluation : Presentation k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun v => match v with
    | some 0 => Polynomial.X
    | _ => 0)

private def axisMap : ambientRing k →+* Polynomial k :=
  Ideal.Quotient.lift _ (axisEvaluation k)
    (relationsIdeal_le_ker k _ (fun n => by simp [axisEvaluation, tPoly, yPoly])
      (fun n => by simp [axisEvaluation, xPoly, yPoly])
      (fun i j => by simp [axisEvaluation, yPoly]))

private lemma genericMap_constantCoeff :
    Polynomial.constantCoeff.comp (genericMap k) =
      (algebraMap (Polynomial k) (RatFunc k)).comp (axisMap k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [genericMap, genericEvaluation, witnessEvaluation, axisMap, axisEvaluation]
  · intro v
    cases v with
    | none =>
      simp [genericMap, genericEvaluation, witnessEvaluation, axisMap, axisEvaluation, yWeight]
    | some n =>
      cases n with
      | zero =>
        simp [genericMap, genericEvaluation, witnessEvaluation, axisMap, axisEvaluation,
          yWeight, RatFunc.algebraMap_X]
      | succ n =>
        simp [genericMap, genericEvaluation, witnessEvaluation, axisMap, axisEvaluation, yWeight]

private def originMap : ambientRing k →+* k :=
  (Polynomial.evalRingHom 0).comp (axisMap k)

private def genericPrime : PrimeSpectrum (ambientRing k) :=
  ⟨RingHom.ker (genericMap k), RingHom.ker_isPrime (genericMap k)⟩

private def originPrime : PrimeSpectrum (ambientRing k) :=
  ⟨RingHom.ker (originMap k), RingHom.ker_isPrime (originMap k)⟩

private lemma genericPrime_le_originPrime : genericPrime k ≤ originPrime k := by
  intro b hb
  change genericMap k b = 0 at hb
  show originMap k b = 0
  have h := congrArg (fun f : ambientRing k →+* RatFunc k => f b)
    (genericMap_constantCoeff k)
  simp only [RingHom.comp_apply, hb, map_zero] at h
  have haxis : axisMap k b = 0 := RatFunc.algebraMap_injective k (by simpa using h.symm)
  simp [originMap, haxis]

private lemma originPrime_mem_support :
    originPrime k ∈ (divisor k).supportSet := by
  show originPrime k ∈ (Spec (.of (ambientRing k))).zeroLocus (U := ⊤)
    ((Ideal.span {(Scheme.ΓSpecIso (.of (ambientRing k))).inv (x k)} : Ideal _) : Set _)
  rw [Scheme.zeroLocus_span,
    show ({(Scheme.ΓSpecIso (.of (ambientRing k))).inv (x k)} : Set _) =
      (Scheme.ΓSpecIso (.of (ambientRing k))).inv '' ({x k} : Set _) by simp,
    Spec_zeroLocus_eq_zeroLocus]
  rintro b (rfl : b = x k)
  show originMap k (x k) = 0
  simp [originMap, axisMap, axisEvaluation, x, xPoly]

private lemma yZero_notMem_genericPrime : yZero k ∉ (genericPrime k).asIdeal := by
  show genericMap k (yZero k) ≠ 0
  simp [genericMap, genericEvaluation, witnessEvaluation, yZero, yPoly, yWeight]

/-- No open subscheme of `Spec B` containing the divisor is flat over `Spec k[t]`. -/
@[stacks 062X "no flat neighbourhood"]
theorem no_flat_neighbourhood
    (U : (Spec (.of (ambientRing k))).Opens)
    (hU : (divisor k).supportSet ⊆ (U : Set (Spec (.of (ambientRing k))))) :
    ¬ Flat (U.ι ≫ Spec.map (CommRingCat.ofHom (baseMap k))) := by
  intro hf
  let _ := hf
  have hqU : genericPrime k ∈ U :=
    ((PrimeSpectrum.le_iff_specializes _ _).mp (genericPrime_le_originPrime k)).mem_open
      U.isOpen (hU (originPrime_mem_support k))
  let q : U := ⟨genericPrime k, hqU⟩
  let z : PrimeSpectrum (Polynomial k) := ⟨⊥, inferInstance⟩
  have hz : z ⤳ (U.ι ≫ Spec.map (CommRingCat.ofHom (baseMap k))) q :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨r, hr, he⟩ := Flat.generalizingMap
    (U.ι ≫ Spec.map (CommRingCat.ofHom (baseMap k))) hz
  have hle : (U.ι r : PrimeSpectrum (ambientRing k)).asIdeal ≤ (genericPrime k).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hr.map U.ι.continuous)
  have hy : yZero k ∉ (U.ι r : PrimeSpectrum (ambientRing k)).asIdeal :=
    fun h => yZero_notMem_genericPrime k (hle h)
  have ht : t k ∈ (U.ι r : PrimeSpectrum (ambientRing k)).asIdeal :=
    ((U.ι r : PrimeSpectrum (ambientRing k)).isPrime.mem_or_mem
      (by rw [t_mul_yZero]; exact Ideal.zero_mem _)).resolve_right hy
  have hx : Polynomial.X ∈ (PrimeSpectrum.comap (baseMap k) (U.ι r)).asIdeal := by
    show baseMap k Polynomial.X ∈ (U.ι r : PrimeSpectrum (ambientRing k)).asIdeal
    simpa [baseMap] using ht
  change PrimeSpectrum.comap (baseMap k) (U.ι r) = z at he
  rw [he] at hx
  exact Polynomial.X_ne_zero (show Polynomial.X = (0 : Polynomial k) from hx)

end AlgebraicGeometry.NonflatAmbient

end
