module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.RingTheory.Polynomial.BivariateWeightedDegree
public import StacksFrontier.RingTheory.Polynomial.PlaneCurveIntersection

/-!
# Normalizing an absolutely irreducible plane curve to be monic and separable in `Y`

Let `F` be a finite field and let `f ∈ F[x, y]` be irreducible over an algebraic closure of `F`,
of total degree `d`. If `F` has more than `d + 1` elements there is a shear
`(x, y) ↦ (x + a y, y)` of the plane after which `f`, rescaled by a constant, becomes a polynomial
`g ∈ F[X][Y]` which is monic of degree `d` in `Y`, has weighted degree at most `d` for the weights
`1, 1`, has nonzero `Y`-derivative, is still irreducible over the algebraic closure, and has as
many zeros in `F²` as `f`.

The leading coefficient of the sheared polynomial in `Y` is `f_d(a, 1)`, where `f_d` is the top
homogeneous component of `f`; it vanishes for at most `d` values of `a`. Its `Y`-derivative is the
shear of `a ∂f/∂x + ∂f/∂y`, which vanishes for at most one value of `a`: the two partial
derivatives cannot both vanish, since otherwise `f` would be a `p`-th power.

## Main definitions

* `MvPolynomial.shear`: the automorphism `(x, y) ↦ (x + a y, y)` of `R[x, y]`.

## Main results

* `MvPolynomial.exists_pow_eq_of_forall_pderiv_eq_zero`: over a perfect ring of characteristic
  `p`, a polynomial all of whose partial derivatives vanish is a `p`-th power.
* `MvPolynomial.irreducible_of_irreducible_map`: a polynomial over a field which is irreducible
  over an extension field is irreducible.
* `MvPolynomial.exists_monic_normalization`: the normalization.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace MvPolynomial

section PthPower

variable {σ R : Type*} [CommRing R] [NoZeroDivisors R] (p : ℕ) [CharP R p]

/-- In characteristic `p`, if every partial derivative of `f` vanishes then every exponent of
every monomial of `f` is divisible by `p`. -/
theorem dvd_of_forall_pderiv_eq_zero {f : MvPolynomial σ R} (h : ∀ i, pderiv i f = 0)
    {m : σ →₀ ℕ} (hm : m ∈ f.support) (i : σ) : p ∣ m i := by
  classical
  by_contra hp
  have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr fun h0 => hp (h0 ▸ dvd_zero p)
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hmi
  have hc := coeff_pderiv (i := i) f (m - Finsupp.single i 1)
  rw [h i, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, tsub_add_cancel_of_le hle,
    Finsupp.tsub_apply, Finsupp.single_eq_same,
    eq_comm, mul_eq_zero] at hc
  rcases hc with hc | hc
  · exact (mem_support_iff.mp hm) hc
  · rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hmi,
      CharP.cast_eq_zero_iff R p] at hc
    exact hp hc

/-- Over a perfect ring of characteristic `p`, a polynomial all of whose partial derivatives
vanish is a `p`-th power. -/
theorem exists_pow_eq_of_forall_pderiv_eq_zero [Fact p.Prime] [PerfectRing R p]
    {f : MvPolynomial σ R} (h : ∀ i, pderiv i f = 0) : ∃ g : MvPolynomial σ R, g ^ p = f := by
  classical
  set g' : MvPolynomial σ R := ∑ m ∈ f.support,
    monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) m) (f.coeff m)
  have hg' : expand p g' = f := by
    conv_rhs => rw [← support_sum_monomial_coeff f]
    simp only [g', map_sum, expand_monomial]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) m = m := by
      ext i
      simp [Nat.mul_div_cancel' (dvd_of_forall_pderiv_eq_zero p h hm i)]
    rw [hm']
  refine ⟨map ((frobeniusEquiv R p).symm : R →+* R) g', ?_⟩
  have : (frobenius R p).comp ((frobeniusEquiv R p).symm : R →+* R) = RingHom.id R := by
    ext x; exact frobenius_apply_frobeniusEquiv_symm R p x
  rw [← map_frobenius_expand p, ← map_expand, map_map, this, map_id, hg']

end PthPower

section Shear

variable {R : Type*} [CommRing R]

/-- The shear `(x, y) ↦ (x + a y, y)` of the plane, as an automorphism of `R[x, y]`. -/
noncomputable def shear (a : R) : MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (aeval ![X 0 + C a * X 1, X 1]) (aeval ![X 0 - C a * X 1, X 1])
    (by ext i : 1; fin_cases i <;> simp) (by ext i : 1; fin_cases i <;> simp)

/-- The shear substitutes `x + a y` for `x` and `y` for `y`. -/
theorem shear_apply (a : R) (f : MvPolynomial (Fin 2) R) :
    shear a f = aeval ![X 0 + C a * X 1, X 1] f := rfl

/-- Evaluating a sheared polynomial at `(x₀, x₁)` is evaluating the original polynomial at
`(x₀ + a x₁, x₁)`. -/
theorem eval_shear (a : R) (f : MvPolynomial (Fin 2) R) (x : Fin 2 → R) :
    eval x (shear a f) = eval ![x 0 + a * x 1, x 1] f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [shear_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, hp]; fin_cases n <;> simp [shear_apply]

/-- The shear commutes with mapping the coefficients along a ring homomorphism `φ`. -/
theorem map_shear {S : Type*} [CommRing S] (φ : R →+* S) (a : R) (f : MvPolynomial (Fin 2) R) :
    map φ (shear a f) = shear (φ a) (map φ f) := by
  rw [shear_apply, shear_apply, aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
  refine congrArg (fun s => bind₁ s (map φ f)) (funext fun i => ?_)
  fin_cases i <;> simp

/-- The chain rule for the shear: `∂/∂y (f (x + a y, y)) = (a ∂f/∂x + ∂f/∂y) (x + a y, y)`. -/
theorem pderiv_one_shear (a : R) (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (shear a f) = shear a (C a * pderiv 0 f + pderiv 1 f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [shear_apply]
  | add p q hp hq => simp only [map_add, mul_add, hp, hq]; abel
  | mul_X p n hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    fin_cases n <;> simp [shear_apply] <;> ring

/-- The shear is a linear change of variables, so it preserves homogeneity of every degree. -/
theorem isHomogeneous_shear (a : R) {f : MvPolynomial (Fin 2) R} {n : ℕ}
    (hf : f.IsHomogeneous n) : (shear a f).IsHomogeneous n := by
  have h := hf.aeval (![X 0 + C a * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (n := 1) fun i => by
    fin_cases i
    · simpa using (isHomogeneous_X R 0).add ((isHomogeneous_C _ a).mul (isHomogeneous_X R 1))
    · simpa using isHomogeneous_X R 1
  rw [shear_apply]
  simpa [one_mul] using h

/-- The shear does not increase the total degree: it sends each homogeneous component of `f` to a
homogeneous polynomial of the same degree. -/
theorem totalDegree_shear_le (a : R) (f : MvPolynomial (Fin 2) R) :
    (shear a f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
  exact (isHomogeneous_shear a (homogeneousComponent_isHomogeneous i f)).totalDegree_le.trans
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- The dehomogenization `G(t, 1)` of `G`, evaluated at `a`, is `G(a, 1)`. -/
theorem eval_aeval_X_one (a : R) (G : MvPolynomial (Fin 2) R) :
    (aeval ![Polynomial.X, 1] G).eval a = eval ![a, 1] G := by
  rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply,
    show (fun i => Polynomial.aeval a (![Polynomial.X, 1] i)) = ![a, 1] from by
      funext i; fin_cases i <;> simp]
  rfl

/-- The coefficient of `y ^ d` in a homogeneous polynomial of degree `d` in `x, y` is its value
at `(0, 1)`. -/
theorem IsHomogeneous.coeff_single_one_eq_eval {G : MvPolynomial (Fin 2) R} {d : ℕ}
    (hG : G.IsHomogeneous d) : G.coeff (Finsupp.single 1 d) = eval ![0, 1] G := by
  conv_lhs => rw [← Polynomial.homogenize_eq_of_isHomogeneous hG rfl]
  rw [Polynomial.coeff_homogenize]
  simp only [Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), Finsupp.single_eq_same,
    zero_add, ite_true, Polynomial.coeff_zero_eq_eval_zero, eval_aeval_X_one]

/-- The coefficient of `y ^ d` after the shear is the top homogeneous component evaluated at
`(a, 1)`. -/
theorem coeff_single_one_shear (a : R) (f : MvPolynomial (Fin 2) R) (d : ℕ) :
    (shear a f).coeff (Finsupp.single 1 d) = eval ![a, 1] (homogeneousComponent d f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, coeff_sum, Finset.sum_eq_single d]
  · rw [(isHomogeneous_shear a (homogeneousComponent_isHomogeneous d f)).coeff_single_one_eq_eval,
      eval_shear]
    simp
  · intro i _ hid
    refine (isHomogeneous_shear a (homogeneousComponent_isHomogeneous i f)).coeff_eq_zero ?_
    simpa using Ne.symm hid
  · intro hd'
    rw [homogeneousComponent_eq_zero d f (by simpa [Nat.lt_succ_iff] using hd'), map_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]

end Shear

end MvPolynomial

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- `equivMvPolynomial` commutes with change of coefficients. -/
theorem equivMvPolynomial_map {S : Type*} [CommRing S] (φ : R →+* S) (q : R[X][Y]) :
    equivMvPolynomial S (q.map (mapRingHom φ)) =
      MvPolynomial.map φ (equivMvPolynomial R q) := by
  ext m
  obtain ⟨i, j, rfl⟩ : ∃ i j, m = Finsupp.single 0 i + Finsupp.single 1 j :=
    ⟨m 0, m 1, by ext k; fin_cases k <;> simp⟩
  rw [coeff_equivMvPolynomial, MvPolynomial.coeff_map, coeff_equivMvPolynomial]
  simp [Polynomial.coeff_map]

end Polynomial.Bivariate

namespace MvPolynomial

open Polynomial.Bivariate

/-- A polynomial over a field which is irreducible over an extension is irreducible. -/
theorem irreducible_of_irreducible_map {σ K L : Type*} [Field K] [Field L] (φ : K →+* L)
    {f : MvPolynomial σ K} (hf : Irreducible (map φ f)) : Irreducible f := by
  classical
  have hunit : ∀ u : MvPolynomial σ K, IsUnit (map φ u) → IsUnit u := by
    intro u hu
    obtain ⟨c, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    have hu' : u = C (u.coeff 0) := by
      ext m
      by_cases hm : m = 0
      · simp [hm]
      · rw [coeff_C, ite_eq_right (Ne.symm hm)]
        have := congrArg (fun q : MvPolynomial _ _ => q.coeff m) hc.2
        rw [coeff_map, coeff_C, ite_eq_right (Ne.symm hm)] at this
        exact (map_eq_zero φ).mp this
    have h0 := congrArg (fun q : MvPolynomial _ _ => q.coeff 0) hc.2
    rw [coeff_map, coeff_C, ite_eq_left rfl] at h0
    rw [hu']
    refine (isUnit_iff_ne_zero.mpr fun h => ?_).map C
    rw [h, map_zero] at h0
    exact hc.1.ne_zero h0.symm
  refine ⟨fun h => hf.not_isUnit (h.map (map φ)), fun a b hab => ?_⟩
  rw [hab, map_mul] at hf
  exact (hf.isUnit_or_isUnit rfl).imp (hunit a) (hunit b)

/-- **Normalization of an absolutely irreducible plane curve.** Let `F` be a finite field and
let `f ∈ F[x, y]` be irreducible over an algebraic closure of `F`, with `deg f + 1 < #F`. Then
after a shear `(x, y) ↦ (x + a y, y)` and a rescaling, `f` becomes `g ∈ F[X][Y]`, monic in `Y`
of degree `deg f > 0`, of weighted degree at most `deg f` for the weights `1, 1`, with nonzero
`Y`-derivative, still irreducible over the algebraic closure, and with as many zeros in `F²`. -/
theorem exists_monic_normalization {F : Type*} [Field F] [Fintype F]
    (f : MvPolynomial (Fin 2) F)
    (hf : Irreducible (f.map (algebraMap F (AlgebraicClosure F))))
    (hq : f.totalDegree + 1 < Fintype.card F) :
    ∃ g : F[X][X], g.Monic ∧ 0 < g.natDegree ∧ g.natDegree = f.totalDegree ∧
      Polynomial.Bivariate.WeightedDegreeLE 1 g.natDegree g ∧ derivative g ≠ 0 ∧
      Irreducible (g.map (mapRingHom (algebraMap F (AlgebraicClosure F)))) ∧
      {p : Fin 2 → F | MvPolynomial.eval p f = 0}.ncard =
        {P : F × F | g.evalEval P.1 P.2 = 0}.ncard := by
  classical
  set φ := algebraMap F (AlgebraicClosure F)
  -- The two partial derivatives of `f` do not both vanish: otherwise `f` is a `p`-th power.
  have hpd : pderiv 0 f ≠ 0 ∨ pderiv 1 f ≠ 0 := by
    by_contra! h
    obtain ⟨p, _⟩ := CharP.exists F
    have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    obtain ⟨g, hg⟩ := exists_pow_eq_of_forall_pderiv_eq_zero p (f := f)
      (fun i => by fin_cases i; exacts [h.1, h.2])
    rw [← hg, map_pow] at hf
    exact not_irreducible_pow (Fact.out : p.Prime).ne_one hf
  -- Hence `a ∂f/∂x + ∂f/∂y ≠ 0` for all but at most one `a`.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, ∀ a, a ≠ a₀ → C a * pderiv 0 f + pderiv 1 f ≠ 0 := by
    by_cases hex : ∃ a₀ : F, C a₀ * pderiv 0 f + pderiv 1 f = 0
    · obtain ⟨a₀, h₀⟩ := hex
      refine ⟨a₀, fun a ha h => ?_⟩
      have h₁ : C (a - a₀) * pderiv 0 f = 0 := by
        rw [map_sub]; linear_combination h - h₀
      rcases mul_eq_zero.mp h₁ with h₂ | h₂
      · exact ha (sub_eq_zero.mp (C_eq_zero.mp h₂))
      · rw [h₂, mul_zero, zero_add] at h₀
        exact hpd.elim (· h₂) (· h₀)
    · exact ⟨0, fun a _ h => hex ⟨a, h⟩⟩
  set d := f.totalDegree with hd
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by rw [h, map_zero])
  -- `f` is not constant.
  have hd0 : d ≠ 0 := by
    intro h0
    rw [totalDegree_eq_zero_iff_eq_C.mp h0, map_C] at hf
    by_cases hb : φ (f.coeff 0) = 0
    · exact hf.ne_zero (by rw [hb, map_zero])
    · exact hf.not_isUnit ((isUnit_iff_ne_zero.mpr hb).map C)
  -- The top homogeneous component `H` of `f`, and its dehomogenization `P(t) = H(t, 1)`.
  set H := homogeneousComponent d f
  have hH : H.IsHomogeneous d := homogeneousComponent_isHomogeneous d f
  have hH0 : H ≠ 0 := by
    obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf0)
      fun s => s.sum fun _ e => e
    intro h
    have := congrArg (fun q : MvPolynomial _ _ => q.coeff m) h
    rw [coeff_homogeneousComponent, ite_eq_left (show m.degree = d from hmd.symm),
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact mem_support_iff.mp hm this
  set P : Polynomial F := aeval ![Polynomial.X, 1] H
  have hP0 : P ≠ 0 := fun h => hH0 <| by
    rw [← Polynomial.homogenize_eq_of_isHomogeneous hH h, Polynomial.homogenize_zero]
  have hPd : P.natDegree ≤ d :=
    (aeval_natDegree_le (n := 1) H hH.totalDegree_le _ fun i => by fin_cases i <;> simp).trans
      (by rw [mul_one])
  -- Choose `a` with `P(a) ≠ 0` and `a ≠ a₀`.
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert a₀ P.roots.toFinset) (t := Finset.univ) <| by
      rw [Finset.card_univ]
      refine lt_of_le_of_lt ((Finset.card_insert_le _ _).trans ?_) hq
      exact Nat.add_le_add_right ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' P).trans hPd)) 1
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot.def, eval_aeval_X_one] at ha
  obtain ⟨haa₀, hc⟩ := ha
  set c := eval ![a, 1] H
  -- The sheared polynomial, as a polynomial in `Y` over `F[X]`.
  set f' := shear a f
  set E := equivMvPolynomial F
  set g' : F[X][X] := E.symm f'
  have hEg' : E g' = f' := E.apply_symm_apply f'
  have htd : (E g').totalDegree ≤ d := hEg' ▸ totalDegree_shear_le a f
  have hcoeff : ∀ j, g'.coeff j ≠ 0 → (g'.coeff j).natDegree + j ≤ d := fun j hj =>
    (natDegree_coeff_add_le_totalDegree g' j hj).trans htd
  have hlead : g'.coeff d = Polynomial.C c := by
    ext i
    rw [← coeff_equivMvPolynomial g' i d, Polynomial.coeff_C]
    split_ifs with hi
    · rw [hi, Finsupp.single_zero, zero_add, hEg', coeff_single_one_shear]
    · by_contra hne
      have := (le_totalDegree (mem_support_iff.mpr hne)).trans htd
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl] at this
      omega
  have hnat' : g'.natDegree = d := by
    exact le_antisymm ((natDegree_le_totalDegree g').trans htd)
      (le_natDegree_of_ne_zero (by rw [hlead]; exact Polynomial.C_ne_zero.mpr hc))
  have hder' : derivative g' ≠ 0 := by
    intro h
    have := pderiv_one_equivMvPolynomial g'
    rw [h, map_zero, hEg', pderiv_one_shear] at this
    exact ha₀ a haa₀ ((shear a).injective (this.trans (map_zero _).symm))
  -- Rescale to make it monic.
  have hu : (Polynomial.C c⁻¹ : F[X]) ≠ 0 := Polynomial.C_ne_zero.mpr (inv_ne_zero hc)
  set g : F[X][X] := Polynomial.C (Polynomial.C c⁻¹) * g'
  have hnat : g.natDegree = d := by rw [Polynomial.natDegree_C_mul hu, hnat']
  have hEg : E g = C c⁻¹ * f' := by
    rw [map_mul, hEg', equivMvPolynomial_C_C]
  have hev : ∀ x y : F, g.evalEval x y = c⁻¹ * eval ![x + a * y, y] f := by
    intro x y
    have := eval_equivMvPolynomial g ![x, y]
    rw [hEg, map_mul, eval_C, eval_shear] at this
    simpa using this.symm
  refine ⟨g, ?_, by omega, hnat, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, Polynomial.coeff_C_mul, hlead,
      ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]
  · intro j hj
    rw [Polynomial.coeff_C_mul] at hj ⊢
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hc), hnat, one_mul]
    exact hcoeff j (right_ne_zero_of_mul hj)
  · rw [Polynomial.derivative_C_mul]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hu) hder'
  · have hmap : equivMvPolynomial (AlgebraicClosure F) (g.map (mapRingHom φ)) =
        C (φ c⁻¹) * shear (φ a) (map φ f) := by
      rw [equivMvPolynomial_map, hEg, map_mul, map_C, map_shear]
    rw [← (equivMvPolynomial (AlgebraicClosure F)).symm_apply_apply (g.map (mapRingHom φ)), hmap,
      MulEquiv.irreducible_iff, irreducible_isUnit_mul
        ((isUnit_iff_ne_zero.mpr ((map_ne_zero φ).mpr (inv_ne_zero hc))).map C),
      MulEquiv.irreducible_iff]
    exact hf
  · have hinj : Function.Injective fun P : F × F => ![P.1 + a * P.2, P.2] := by
      intro P Q h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      exact Prod.ext (by simpa [h1] using h0) h1
    have hset : {p : Fin 2 → F | eval p f = 0} =
        (fun P : F × F => ![P.1 + a * P.2, P.2]) '' {P : F × F | g.evalEval P.1 P.2 = 0} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_image, hev, mul_eq_zero, inv_eq_zero, hc, false_or]
      have hp : ![p 0, p 1] = p := by ext i; fin_cases i <;> rfl
      constructor
      · intro h
        exact ⟨(p 0 - a * p 1, p 1), by simpa [hp] using h, by simpa using hp⟩
      · rintro ⟨P, hP, rfl⟩
        exact hP
    rw [hset, Set.ncard_image_of_injective _ hinj]

end MvPolynomial
