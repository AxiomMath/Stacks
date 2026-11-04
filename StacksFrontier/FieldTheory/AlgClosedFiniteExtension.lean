module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Ring.Archimedean
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Basic.Real.Embedding
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Fields with a finite algebraically closed extension

Let `F` be a field of characteristic zero admitting a finite extension `E` which is
algebraically closed. The Artin–Schreier theorem says that `E` is either `F` itself or a
quadratic extension of it, and in the quadratic case `F` is real closed. This file proves
the degree bound and, for a field algebraic over `ℚ`, identifies the quadratic case: such
an `F` is isomorphic to the field of real algebraic numbers.

## Main results

* `IsAlgClosed.finrank_eq_one_or_two`: a finite algebraically closed extension of a field of
  characteristic zero has degree one or two.
* `IsAlgClosed.isSquare_neg_of_not_isSquare_of_finrank_two` and
  `IsAlgClosed.isSquare_add_sq_of_finrank_two`: in the quadratic case the squares of `F` are
  closed under addition and every element or its negative is a square, so they are the
  nonnegative cone of an order.
* `IsAlgClosed.nonempty_linearOrder_of_finrank_two`: that order, exhibited as a strict
  ordered ring structure on `F`.
* `archimedean_of_isAlgebraic_rat`: an ordered field algebraic over `ℚ` is archimedean.
* `IsAlgClosed.nonempty_algEquiv_realAlgebraicClosure_of_finrank_two`: a field algebraic over
  `ℚ` with a quadratic algebraically closed extension is isomorphic over `ℚ` to the field
  `algebraicClosure ℚ ℝ` of real algebraic numbers.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField Module

universe u v

/-- An ordered field algebraic over `ℚ` is archimedean. -/
theorem archimedean_of_isAlgebraic_rat (F : Type u) [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] : Archimedean F := by
  let v := (ArchimedeanClass.addValuation F).toValuation
  let q : ℚ →+* v.integer := (algebraMap ℚ F).codRestrict v.integer fun a => by
    show 0 ≤ ArchimedeanClass.mk (algebraMap ℚ F a)
    simpa using ArchimedeanClass.mk_ratCast_nonneg (R := F) a
  let : Algebra ℚ v.integer := q.toAlgebra
  have : IsScalarTower ℚ v.integer F := .of_algebraMap_eq fun _ => rfl
  refine archimedean_iff_nat_le.mpr fun x => ArchimedeanClass.exists_nat_ge_of_mk_nonneg ?_
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp
    ((Algebra.IsIntegral.isIntegral x : IsIntegral ℚ x).tower_top (A := v.integer))

/-- The norm of a root of a monic irreducible quadratic polynomial over the base of a
quadratic extension is the constant coefficient of that polynomial. -/
theorem Algebra.norm_eq_coeff_zero_of_irreducible_quadratic (F : Type u) (E : Type v) [Field F]
    [Field E] [Algebra F E] [FiniteDimensional F E] (hd : finrank F E = 2) {f : F[X]}
    (hm : f.Monic) (hi : Irreducible f) (hf : f.natDegree = 2) {z : E} (hz : aeval z f = 0) :
    Algebra.norm F z = f.coeff 0 := by
  have hmin : minpoly F z = f := (minpoly.eq_of_irreducible_of_monic hi hz hm).symm
  have hgen : F⟮z⟯ = ⊤ := by
    apply IntermediateField.finrank_eq_one_iff_eq_top.mp
    have hmul := finrank_mul_finrank F F⟮z⟯ E
    rw [adjoin.finrank (_root_.IsIntegral.of_finite F z), hmin, hf, hd] at hmul
    omega
  simpa [hmin, hf] using Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (PowerBasis.ofAdjoinSimpleEqTop (_root_.IsIntegral.of_finite F z) hgen)

namespace IsAlgClosed

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- If an algebraically closed field of characteristic zero is a finite extension of prime
degree `p` of a subfield, then that subfield already contains a primitive `p`-th root of
unity. -/
theorem primitiveRoot_of_prime_finrank [FiniteDimensional F E] [IsAlgClosed E] [CharZero E]
    {p : ℕ} (hp : p.Prime) (hd : finrank F E = p) : (primitiveRoots p F).Nonempty := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E p
  have hi : IsIntegral F ζ := IsIntegral.of_finite F ζ
  have hdvd : (minpoly F ζ).natDegree ∣ p := hd ▸ minpoly.degree_dvd hi
  have hbound : (minpoly F ζ).natDegree < p := by
    have hc : aeval ζ (cyclotomic p F) = 0 := by
      simpa only [aeval_def, eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using
        (hζ.isRoot_cyclotomic hp.pos : (cyclotomic p E).eval ζ = 0)
    have hle := natDegree_le_of_dvd (minpoly.dvd F ζ hc) (cyclotomic_ne_zero p F)
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at hle
    exact lt_of_le_of_lt hle (Nat.sub_one_lt hp.ne_zero)
  have hd1 : (minpoly F ζ).natDegree = 1 :=
    (hp.eq_one_or_self_of_dvd _ hdvd).resolve_right (by omega)
  obtain ⟨z, hz⟩ := minpoly.natDegree_eq_one_iff.mp hd1
  exact ⟨z, (mem_primitiveRoots hp.pos).mpr
    ((hz ▸ hζ).of_map_of_injective (algebraMap F E).injective)⟩

/-- A field containing a square root of `-1` has no Galois extension of prime degree which is
algebraically closed. -/
theorem not_prime_finrank_of_sq_eq_neg_one [FiniteDimensional F E] [IsAlgClosed E] [CharZero E]
    [IsGalois F E] {p : ℕ} (hp : p.Prime) (hd : finrank F E = p) (i : F) (hi : i ^ 2 = -1) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = p := (IsGalois.card_aut_eq_finrank F E).trans hd
  have : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card hcard
  have hroots : (primitiveRoots (finrank F E) F).Nonempty :=
    hd.symm ▸ primitiveRoot_of_prime_finrank F E hp hd
  obtain ⟨α, ⟨a, ha⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hroots
  have hirr : Irreducible (X ^ p - C a) := by
    simpa only [hd] using irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hgen
  have hmin : minpoly F α = X ^ p - C a := by
    symm
    apply minpoly.eq_of_irreducible_of_monic hirr
    · simp only [aeval_sub, map_pow, aeval_X, aeval_C, ← hd, ha, sub_self]
    · exact monic_X_pow_sub_C a hp.ne_zero
  have hnorm : Algebra.norm F α = (-1 : F) ^ p * -a := by
    simpa [hmin, hp.ne_zero, Ne.symm hp.ne_zero] using
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite F α) hgen)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq α hp.pos
  have hnβ : (Algebra.norm F β) ^ p = (-1 : F) ^ p * -a := by
    rw [← map_pow, hβ, hnorm]
  have hnot := pow_ne_of_irreducible_X_pow_sub_C hirr (dvd_refl p) hp.ne_one
  rcases hp.eq_two_or_odd' with rfl | ho
  · apply hnot (i * Algebra.norm F β)
    rw [mul_pow, hi]
    norm_num at hnβ
    rw [hnβ]
    ring
  · apply hnot (Algebra.norm F β)
    simpa [ho.neg_one_pow] using hnβ

/-- A field of characteristic zero containing a square root of `-1` has no proper finite
algebraically closed extension. -/
theorem finrank_eq_one_of_sq_eq_neg_one [FiniteDimensional F E] [IsAlgClosed E] [CharZero F]
    (i : F) (hi : i ^ 2 = -1) : finrank F E = 1 := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have : IsAlgClosure F E := ⟨inferInstance, inferInstance⟩
  have : IsGalois F E := {}
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := E ≃ₐ[F] E) p
    (by rwa [IsGalois.card_aut_eq_finrank])
  have hdim : finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) E = p := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hσ]
  exact not_prime_finrank_of_sq_eq_neg_one _ E hp hdim
    (algebraMap F (IntermediateField.fixedField (Subgroup.zpowers σ)) i)
    (by simp only [← map_pow, hi, map_neg, map_one])

/-- **The Artin–Schreier degree bound in characteristic zero.** A finite algebraically closed
extension of a field of characteristic zero has degree one or two. -/
theorem finrank_eq_one_or_two [FiniteDimensional F E] [IsAlgClosed E] [CharZero F] :
    finrank F E = 1 ∨ finrank F E = 2 := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : E) (by decide : 0 < 2)
  have hdim : finrank F⟮i⟯ E = 1 :=
    finrank_eq_one_of_sq_eq_neg_one F⟮i⟯ E (AdjoinSimple.gen F i)
      (by apply Subtype.val_injective; exact hi)
  have hdeg : (minpoly F i).natDegree ≤ 2 := by
    have hv : aeval i (X ^ 2 + 1 : F[X]) = 0 := by simp [hi]
    simpa using natDegree_le_of_dvd (minpoly.dvd F i hv)
      (show (X ^ 2 + 1 : F[X]) ≠ 0 from (monic_X_pow_add_C (1 : F) (by decide : 2 ≠ 0)).ne_zero)
  have hb : finrank F E ≤ 2 := by
    rw [← finrank_mul_finrank F F⟮i⟯ E, hdim, mul_one,
      adjoin.finrank (IsIntegral.of_finite F i)]
    exact hdeg
  have hp := finrank_pos (R := F) (M := E)
  omega

/-- Over an algebraically closed field, the norm of any element is a square. -/
private theorem isSquare_norm [IsAlgClosed E] (z : E) : IsSquare (Algebra.norm F z) := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
  exact ⟨Algebra.norm F w, by rw [← pow_two, ← map_pow, hw]⟩

/-- In the quadratic case of the Artin–Schreier bound, the negative of an element of the base
which is not a square is a square. -/
theorem isSquare_neg_of_not_isSquare_of_finrank_two [FiniteDimensional F E] [IsAlgClosed E]
    (hd : finrank F E = 2) (a : F) (ha : ¬ IsSquare a) : IsSquare (-a) := by
  have hirr : Irreducible (X ^ 2 - C a) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two
      (fun b hb => ha ⟨b, by simpa [pow_two] using hb.symm⟩)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F E a) (by decide : 0 < 2)
  have hn : Algebra.norm F z = -a := by
    simpa using Algebra.norm_eq_coeff_zero_of_irreducible_quadratic F E hd
      (monic_X_pow_sub_C a (by decide : 2 ≠ 0)) hirr (by simp)
      (show aeval z (X ^ 2 - C a) = 0 by simp [hz])
  exact hn ▸ isSquare_norm F E z

/-- In the quadratic case of the Artin–Schreier bound, a sum of two squares of the base is a
square. -/
theorem isSquare_add_sq_of_finrank_two [FiniteDimensional F E] [IsAlgClosed E] [CharZero F]
    (hd : finrank F E = 2) (a b : F) : IsSquare (a ^ 2 + b ^ 2) := by
  have hno (r : F) : r ^ 2 ≠ -1 := fun hr => by
    have := finrank_eq_one_of_sq_eq_neg_one F E r hr
    omega
  by_cases hb : b = 0
  · exact ⟨a, by simp [hb, pow_two]⟩
  set f : F[X] := (X - C a) ^ 2 + C (b ^ 2) with hfdef
  have hm : f.Monic := by rw [hfdef]; monicity; norm_num
  have hf : f.natDegree = 2 := by rw [hfdef]; compute_degree!
  have hirr : Irreducible f := by
    rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
      roots_eq_zero_iff_isRoot_eq_bot hm.ne_zero]
    ext x
    show f.IsRoot x ↔ False
    rw [iff_false]
    intro hx
    have hx' : (x - a) ^ 2 + b ^ 2 = 0 := by simpa [hfdef, IsRoot.def] using hx
    apply hno ((x - a) / b)
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hb)).mpr
    simpa [div_pow] using (eq_neg_iff_add_eq_zero.mpr hx')
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : E) (by decide : 0 < 2)
  have hz : aeval (algebraMap F E a + algebraMap F E b * i) f = 0 := by
    rw [hfdef]
    simp only [map_add, map_pow, map_sub, aeval_X, aeval_C, add_sub_cancel_left,
      mul_pow, hi, mul_neg_one, neg_add_cancel]
  have hn : Algebra.norm F (algebraMap F E a + algebraMap F E b * i) = a ^ 2 + b ^ 2 := by
    simpa [hfdef, coeff_add, coeff_sub, coeff_mul, pow_two] using
      Algebra.norm_eq_coeff_zero_of_irreducible_quadratic F E hd hm hirr hf hz
  exact hn ▸ isSquare_norm F E _

/-- In the quadratic case of the Artin–Schreier bound the base field is orderable: its squares
form the nonnegative cone of a strict ordered ring structure. -/
theorem nonempty_linearOrder_of_finrank_two [FiniteDimensional F E] [IsAlgClosed E] [CharZero F]
    (hd : finrank F E = 2) : ∃ _ : LinearOrder F, IsStrictOrderedRing F := by
  classical
  have hno : ¬ IsSquare (-1 : F) := by
    rintro ⟨r, hr⟩
    have := finrank_eq_one_of_sq_eq_neg_one F E r (by simpa [pow_two] using hr.symm)
    omega
  let C : RingCone F :=
    { carrier := {x | IsSquare x}
      zero_mem' := ⟨0, by simp⟩
      one_mem' := ⟨1, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        simpa [pow_two] using isSquare_add_sq_of_finrank_two F E hd a b
      mul_mem' := fun ha hb => ha.mul hb
      eq_zero_of_mem_of_neg_mem' := by
        intro a ha hna
        by_contra h
        exact hno (by simpa [h] using hna.div ha) }
  have : HasMemOrNegMem C := ⟨fun x => by
    show IsSquare x ∨ IsSquare (-x)
    exact (em (IsSquare x)).imp_right (isSquare_neg_of_not_isSquare_of_finrank_two F E hd x)⟩
  let : LinearOrder F := .mkOfAddGroupCone C
  have : IsOrderedRing F := .mkOfCone C
  exact ⟨inferInstance, inferInstance⟩

/-- A field algebraic over `ℚ` with a quadratic algebraically closed extension is isomorphic
over `ℚ` to the field `algebraicClosure ℚ ℝ` of real algebraic numbers. -/
theorem nonempty_algEquiv_realAlgebraicClosure_of_finrank_two [FiniteDimensional F E]
    [IsAlgClosed E] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] (hd : finrank F E = 2) :
    Nonempty (F ≃ₐ[ℚ] algebraicClosure ℚ ℝ) := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  obtain ⟨lo, ho⟩ := nonempty_linearOrder_of_finrank_two F E hd
  let : LinearOrder F := lo
  have : IsStrictOrderedRing F := ho
  have : Archimedean F := archimedean_of_isAlgebraic_rat F
  let φ : F →+* ℝ := (Classical.choice (Real.nonemptyOrderRingHom F)).toRingHom
  let ψ : F →ₐ[ℚ] ℝ := { φ with commutes' := φ.map_rat_algebraMap }
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℝ) := algebraicClosure.isAlgebraic ℚ ℝ
  let j : F →ₐ[ℚ] algebraicClosure ℚ ℝ :=
    ψ.codRestrict (algebraicClosure ℚ ℝ).toSubalgebra fun x =>
      mem_algebraicClosure_iff'.mpr ((Algebra.IsIntegral.isIntegral x : IsIntegral ℚ x).map ψ)
  let : Algebra F (algebraicClosure ℚ ℝ) := j.toAlgebra
  have : IsScalarTower ℚ F (algebraicClosure ℚ ℝ) := .of_algebraMap_eq fun x => (j.commutes x).symm
  have : Algebra.IsAlgebraic F (algebraicClosure ℚ ℝ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (A := algebraicClosure ℚ ℝ) F
  rcases IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two (F := F) (F' := E)
    (algebraicClosure ℚ ℝ) hd with h | h <;> obtain ⟨e⟩ := h
  · exact ⟨e.symm.restrictScalars ℚ⟩
  · obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : E) (by decide : 0 < 2)
    have hsq : ((e.symm i : algebraicClosure ℚ ℝ) : ℝ) ^ 2 = -1 := by
      have h' : (e.symm i) ^ 2 = -1 := by simpa using congrArg e.symm hi
      exact congrArg (fun x : algebraicClosure ℚ ℝ => (x : ℝ)) h'
    linarith [sq_nonneg ((e.symm i : algebraicClosure ℚ ℝ) : ℝ)]

end IsAlgClosed

/-- A field `L` algebraic over `ℚ` receiving an algebra map `j` from an algebraic closure of `ℚ`
is isomorphic to it, by the inverse of `j`. -/
def algEquivOfAlgebraicClosureHom (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (j : AlgebraicClosure ℚ →ₐ[ℚ] L) : L ≃ₐ[ℚ] AlgebraicClosure ℚ := by
  let : Algebra (AlgebraicClosure ℚ) L := j.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) L :=
    .of_algebraMap_eq fun x => (j.commutes x).symm
  have : Algebra.IsAlgebraic (AlgebraicClosure ℚ) L :=
    Algebra.IsAlgebraic.extendScalars (FaithfulSMul.algebraMap_injective ℚ (AlgebraicClosure ℚ))
  exact (AlgEquiv.ofBijective j IsAlgClosed.algebraMap_bijective_of_isIntegral).symm

end
