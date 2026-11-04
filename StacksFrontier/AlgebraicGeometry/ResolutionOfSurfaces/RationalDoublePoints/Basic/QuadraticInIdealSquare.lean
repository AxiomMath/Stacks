module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic.CoefficientsAndColength
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic.AffineFormsAndDerivations
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Basic.CoefficientsAndColength
public import StacksCore.Tactic.StacksAttribute

/-!
# Quadratic elements in the square of an ideal of a polynomial ring

Over a field, a nonzero polynomial of degree at most two in two variables that belongs to the
square of an ideal of colength greater than one is a scalar multiple of the square of an affine
linear polynomial.

## Main results

* `MvPolynomial.eq_smul_sq_affineLinear_of_mem_ideal_sq`: the quadratic polynomial is a scalar
  multiple of the square of an affine linear polynomial.

## Implementation notes

The polynomial ring `κ[x, y]` is represented by `MvPolynomial (Fin 2) κ`, with variables `X 0`
and `X 1`. Colength greater than one is expressed using `Module.rank`, so the statement also
covers ideals whose quotient has infinite dimension.

The characteristic-two case is separated out: there the two partial derivatives no longer
determine the quadratic, and the argument instead translates the variables and uses a
derivation of `κ` over `ZMod 2` to detect non-squares.

## References

* [Stacks Project, Tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD)
-/

@[expose] public section

open MvPolynomial

namespace MvPolynomial

/-- If a nonzero constant multiple of a polynomial lies in an ideal, so does the polynomial. -/
private theorem mem_of_C_mul_mem {k : Type*} [Field k] {I : Ideal (MvPolynomial (Fin 2) k)}
    {s : k} (hs : s ≠ 0) {p : MvPolynomial (Fin 2) k} (h : C s * p ∈ I) : p ∈ I :=
  (Ideal.unit_mul_mem_iff_mem I ((isUnit_iff_ne_zero.2 hs).map C)).1 h

/-- The partial derivatives of a quadratic in `I ^ 2` are affine forms in `I` whose linear parts
have vanishing determinant. -/
private theorem pderiv_forms_of_mem_sq {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin 2) k)) (a b c d e f : k)
    (hmem : C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
      C e * X 0 * X 1 + C f * X 1 ^ 2 ∈ I ^ 2)
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I)) :
    affineForm b (2 * d) e ∈ I ∧ affineForm c e (2 * f) ∈ I ∧ 2 * d * (2 * f) - e * e = 0 := by
  have hpx := pderiv_mem_of_mem_sq I hmem (0 : Fin 2)
  rw [pderiv_quad_x_affine] at hpx
  have hpy := pderiv_mem_of_mem_sq I hmem (1 : Fin 2)
  rw [pderiv_quad_y_affine] at hpy
  exact ⟨hpx, hpy, affine_forms_det_eq_zero I b (2 * d) e c e (2 * f) hpx hpy hcolength⟩

/-- If `p - m * L ^ 2` is a constant `z`, where `p ∈ I ^ 2` and `L ∈ I` for a proper ideal `I`,
then `z = 0`. -/
private theorem const_eq_zero_of_sub_mul_sq {k : Type*} [Field k]
    {I : Ideal (MvPolynomial (Fin 2) k)} (hI : I ≠ ⊤) {p L : MvPolynomial (Fin 2) k} {m z : k}
    (hp : p ∈ I ^ 2) (hL : L ∈ I) (h : p - C m * L ^ 2 = C z) : z = 0 := by
  have hmem := (I ^ 2).sub_mem hp ((I ^ 2).mul_mem_left (C m) (Ideal.pow_mem_pow hL 2))
  rw [h] at hmem
  exact constant_eq_zero_of_mem_of_ne_top I (Ideal.pow_le_self (by decide : 2 ≠ 0) hmem) hI

/-- In characteristic two, after translating the variables so that both `x ^ 2` and `y ^ 2`
become constants modulo `I`, a non-square leading coefficient is impossible. -/
private theorem char_two_translated_impossible {k : Type*} [Field k] [CharP k 2]
    (I : Ideal (MvPolynomial (Fin 2) k)) (a d α β r s : k)
    (hproper : I ≠ ⊤)
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I))
    (hr : r ^ 2 = α) (hs : s ^ 2 = β) (hβ : β = a + α * d)
    (hX : C α + X (0 : Fin 2) ^ 2 ∈ I)
    (hY : C β + X (1 : Fin 2) ^ 2 ∈ I)
    (hp : C a + C d * X (0 : Fin 2) ^ 2 + X (1 : Fin 2) ^ 2 ∈ I ^ 2)
    (hnsq : ¬ ∃ v : k, v ^ 2 = d) : False := by
  classical
  let e := translateRingHom r s
  have hinv : Function.Involutive e := translateRingHom_involutive r s
  have hinj : Function.Injective e := hinv.injective
  have esurj : Function.Surjective e := hinv.surjective
  let I' : Ideal (MvPolynomial (Fin 2) k) := I.map e
  have hproper' : I' ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin 2) k) ∈ I' := by rw [htop]; simp
    change (1 : MvPolynomial (Fin 2) k) ∈ Ideal.map e I at h1
    obtain ⟨w, hw, hew⟩ := (Ideal.mem_map_iff_of_surjective e esurj).mp h1
    have hw1 : w = 1 := by apply hinj; simpa using hew
    exact hproper (I.eq_top_of_isUnit_mem (hw1 ▸ hw) isUnit_one)
  have heX : e (X (0 : Fin 2)) = X (0 : Fin 2) + C r := by
    simp [e, translateRingHom]
  have heY : e (X (1 : Fin 2)) = X (1 : Fin 2) + C s := by
    simp [e, translateRingHom]
  have heC (z : k) : e (C z) = C z := by
    simp [e, translateRingHom]
  have h2p : (2 : MvPolynomial (Fin 2) k) = 0 :=
    CharP.cast_eq_zero (MvPolynomial (Fin 2) k) 2
  have hshift (x : Fin 2) (t : k) : (X x + C t) ^ 2 = C (t ^ 2) + X x ^ 2 := by
    rw [add_sq, h2p, map_pow]
    ring
  have hsq (x : Fin 2) (t α : k) (hx : e (X x) = X x + C t) (ht : t ^ 2 = α)
      (h : C α + X x ^ 2 ∈ I) : X x ^ 2 ∈ I' := by
    have hc : e (C α + X x ^ 2) = X x ^ 2 := by
      rw [map_add, heC, map_pow, hx, hshift, ht]
      linear_combination h2p * C α
    have hm : e (C α + X x ^ 2) ∈ I' := Ideal.mem_map_of_mem e h
    rwa [hc] at hm
  have hX2 : X (0 : Fin 2) ^ 2 ∈ I' := hsq 0 r α heX hr hX
  have hY2 : X (1 : Fin 2) ^ 2 ∈ I' := hsq 1 s β heY hs hY
  have hIvar : I' ≤ variableIdeal (k := k) :=
    ideal_le_variableIdeal_of_var_squares I' hproper' hX2 hY2
  have hconst : ∀ q ∈ I', q.coeff 0 = 0 := by
    intro q hq
    have hz := RingHom.mem_ker.mp
      ((variableIdeal_eq_ker_constantCoeff (k := k)).le (hIvar hq))
    simpa [constantCoeff] using hz
  have hsqle : Ideal.span {X (0 : Fin 2) ^ 2, X (1 : Fin 2) ^ 2} ≤ I' :=
    Ideal.span_le.2 (by rintro _ (rfl | rfl) <;> [exact hX2; exact hY2])
  have hpt : e (C a + C d * X 0 ^ 2 + X 1 ^ 2) = C d * X 0 ^ 2 + X 1 ^ 2 := by
    simp only [map_add, map_mul, map_pow, heC, heX, heY, hshift, hr, hs, hβ]
    linear_combination (C a + C d * C α) * h2p
  have hp' : C d * X 0 ^ 2 + X 1 ^ 2 ∈ I' ^ 2 := by
    have hm := Ideal.mem_map_of_mem e hp
    rwa [Ideal.map_pow, hpt] at hm
  have hremform (q : MvPolynomial (Fin 2) k) (hq : q ∈ I') :
      ∃ b c t : k, q.coeff (Finsupp.single (0 : Fin 2) 1) = b ∧
        q.coeff (Finsupp.single (1 : Fin 2) 1) = c ∧
        (C b * X 0 + C c * X 1 + C t * X 0 * X 1) ∈ I' := by
    obtain ⟨a₀, b, c, t, hrem⟩ := reduce_mod_var_squares q
    let red : MvPolynomial (Fin 2) k :=
      C a₀ + C b * X (0 : Fin 2) + C c * X (1 : Fin 2) + C t * X (0 : Fin 2) * X (1 : Fin 2)
    have hrem' : q - red ∈ Ideal.span {X (0 : Fin 2) ^ 2, X (1 : Fin 2) ^ 2} := hrem
    have hlow := coeff_low_of_mem_var_squares hrem'
    have hq_eq (m : Fin 2 →₀ ℕ) (h : (q - red).coeff m = 0) : q.coeff m = red.coeff m :=
      sub_eq_zero.mp (by rwa [coeff_sub] at h)
    have hcross : ∀ m ∈ ({0, Finsupp.single 0 1, Finsupp.single 1 1} :
        Set (Fin 2 →₀ ℕ)), (C t * X (0 : Fin 2) * X (1 : Fin 2)).coeff m = 0 := by
      intro m hm
      rw [mul_assoc, coeff_C_mul, coeff_X_mul']
      rcases hm with rfl | rfl | rfl <;> simp
    have hred0 : red.coeff 0 = a₀ := by
      simp [red, coeff_C_mul, hcross 0 (by simp)]
    have hz (i : Fin 2) : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 :=
      (Finsupp.single_ne_zero.2 one_ne_zero).symm
    have hredx : red.coeff (Finsupp.single (0 : Fin 2) 1) = b := by
      simp [red, coeff_C_mul, hcross _ (by simp : Finsupp.single (0 : Fin 2) 1 ∈ _), hz]
    have hredy : red.coeff (Finsupp.single (1 : Fin 2) 1) = c := by
      simp [red, coeff_C_mul, hcross _ (by simp : Finsupp.single (1 : Fin 2) 1 ∈ _), hz]
    have ha₀ : a₀ = 0 := by
      rw [← (hq_eq 0 hlow.1).trans hred0]
      exact hconst q hq
    have hqrem : C a₀ + C b * X 0 + C c * X 1 + C t * X 0 * X 1 ∈ I' := by
      have hh := I'.sub_mem hq (hsqle hrem')
      convert hh using 1
      ring
    exact ⟨b, c, t, (hq_eq _ hlow.2.1).trans hredx, (hq_eq _ hlow.2.2).trans hredy,
      by simpa [ha₀] using hqrem⟩
  have hdiag (u v : k) (hl : ∀ q ∈ I', v * linCoeffX q = u * linCoeffY q) :
      d * v ^ 2 = u ^ 2 := by
    have h := diagonal_coeff_relation_of_mem_sq I' _ hp' hconst u v hl
    simpa [coeff_C_mul, coeff_X_pow, Finsupp.single_left_inj] using h
  have hlin_exists : ∃ q ∈ I', linCoeffX q ≠ 0 ∨ linCoeffY q ≠ 0 := by
    by_contra hn
    push Not at hn
    have h := hdiag 1 0 (fun q hq => by rw [(hn q hq).2]; simp)
    norm_num at h
  obtain ⟨q₀, hq₀, hnonzero⟩ := hlin_exists
  obtain ⟨b₀, c₀, t₀, hb₀, hc₀, hq₀rem⟩ := hremform q₀ hq₀
  have hxy : X 0 * X 1 ∈ I' := by
    rcases hnonzero.imp (fun hb hz => hb (hb₀.trans hz)) (fun hc hz => hc (hc₀.trans hz))
      with hb | hc
    · refine mem_of_C_mul_mem hb ?_
      have hh := I'.sub_mem (I'.mul_mem_left (X 1) hq₀rem)
        (I'.add_mem (I'.mul_mem_left (C c₀) hY2) (I'.mul_mem_left (C t₀ * X 0) hY2))
      convert hh using 1
      ring
    · refine mem_of_C_mul_mem hc ?_
      have hh := I'.sub_mem (I'.mul_mem_left (X 0) hq₀rem)
        (I'.add_mem (I'.mul_mem_left (C b₀) hX2) (I'.mul_mem_left (C t₀ * X 1) hX2))
      convert hh using 1
      ring
  have haff (b c t : k) (h : C b * X 0 + C c * X 1 + C t * X 0 * X 1 ∈ I') :
      affineForm (r * b + s * c) b c ∈ I := by
    have hz : C b * X 0 + C c * X 1 ∈ I' := by
      have hh := I'.sub_mem h (I'.mul_mem_left (C t) hxy)
      convert hh using 1
      ring
    have htr : e (C b * X 0 + C c * X 1) = affineForm (r * b + s * c) b c := by
      rw [map_add, map_mul, map_mul, heC, heC, heX, heY]
      simp only [affineForm, map_add, map_mul]
      ring
    rw [← htr]
    change _ ∈ Ideal.map e I at hz
    obtain ⟨w, hw, hew⟩ := (Ideal.mem_map_iff_of_surjective e esurj).mp hz
    rwa [← hew, hinv w]
  have hline : ∀ q ∈ I', c₀ * linCoeffX q = b₀ * linCoeffY q := by
    intro q hq
    obtain ⟨b, c, t, hb, hc, hqrem⟩ := hremform q hq
    have hdet := affine_forms_det_eq_zero I (r * b₀ + s * c₀) b₀ c₀
      (r * b + s * c) b c (haff b₀ c₀ t₀ hq₀rem) (haff b c t hqrem) hcolength
    simp only [linCoeffX, linCoeffY, hb, hc]
    exact (sub_eq_zero.mp hdet).symm
  have hrule := hdiag b₀ c₀ hline
  have hc₀ne : c₀ ≠ 0 := by
    intro hz
    have hbzero : b₀ = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by simpa [hz] using hrule.symm)
    exact hnonzero.elim (fun hb => hb (hb₀.trans hbzero)) (fun hc => hc (hc₀.trans hz))
  exact hnsq ⟨b₀ / c₀, by rw [div_pow, div_eq_iff (pow_ne_zero 2 hc₀ne)]; exact hrule.symm⟩



/-- Away from characteristic two, a quadratic in `I ^ 2` with nonzero `x ^ 2` coefficient is a
scalar multiple of the square of an affine form. -/
private theorem factor_quad_of_two_ne_zero_d_ne_zero {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin 2) k)) (a b c d e f : k)
    (h2 : (2 : k) ≠ 0) (hd : d ≠ 0)
    (hmem : MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 +
      MvPolynomial.C c * MvPolynomial.X 1 + MvPolynomial.C d * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C e * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C f * MvPolynomial.X 1 ^ 2 ∈ I ^ 2)
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I)) :
    ∃ j g h i : k,
      MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X (0 : ℕ) +
        MvPolynomial.C c * MvPolynomial.X (1 : ℕ) + MvPolynomial.C d * MvPolynomial.X (0 : ℕ) ^ 2 +
        MvPolynomial.C e * MvPolynomial.X (0 : ℕ) * MvPolynomial.X (1 : ℕ) +
        MvPolynomial.C f * MvPolynomial.X (1 : ℕ) ^ 2 =
      MvPolynomial.C j * (MvPolynomial.C g + MvPolynomial.C h * MvPolynomial.X (0 : ℕ) +
        MvPolynomial.C i * MvPolynomial.X (1 : ℕ)) ^ 2 := by
  have hproper := ideal_ne_top_of_rank_gt_one I hcolength
  obtain ⟨hpx, hpy, hdet⟩ := pderiv_forms_of_mem_sq I a b c d e f hmem hcolength
  let s : k := 2 * d
  let u : k := b / s
  let v : k := e / s
  have hs : s ≠ 0 := mul_ne_zero h2 hd
  have he : e = s * v := by dsimp [v, s]; field_simp
  have hdet' : s * (2 * f) = e * e := by dsimp only [s]; linear_combination hdet
  have h2f : 2 * f = v * e := mul_left_cancel₀ hs <| by rw [hdet', he]; ring
  have heV : e = v * (2 * d) := by rw [he]; dsimp [s]; ring
  have hb : b = s * u := by dsimp [u]; field_simp
  have hc0 : c - v * b = 0 := by
    have hdiffmem := I.sub_mem hpy (I.mul_mem_left (MvPolynomial.C v) hpx)
    rw [affineForm_sub_scaled_eq_const c e (2 * f) b (2 * d) e v heV h2f] at hdiffmem
    exact constant_eq_zero_of_mem_of_ne_top I hdiffmem hproper
  have hc : c = 2 * d * u * v := by
    rw [sub_eq_zero.mp hc0, hb]
    dsimp [s]
    ring
  have hf : f = d * v ^ 2 := mul_left_cancel₀ h2 <| by rw [h2f, he]; dsimp [s]; ring
  have hL : affineForm u 1 v ∈ I := by
    have hrel : affineForm b s e = MvPolynomial.C s * affineForm u 1 v := by
      simpa [affineForm] using affineForm_eq_scaled_gen b s e s u 1 v hb (by simp) he
    exact mem_of_C_mul_mem hs (hrel ▸ hpx)
  have hrem := quad_sub_square_eq_const a b c d e f d u 1 v
    (by simpa [s] using hb) (by simpa using hc) (by simp)
    (by simpa [s] using he) (by simpa using hf)
  have hrem' :
      (MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 +
        MvPolynomial.C c * MvPolynomial.X 1 + MvPolynomial.C d * MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C e * MvPolynomial.X 0 * MvPolynomial.X 1 +
        MvPolynomial.C f * MvPolynomial.X 1 ^ 2) -
      MvPolynomial.C d * (affineForm u 1 v) ^ 2 = MvPolynomial.C (a - d * u ^ 2) := by
    simpa [affineForm] using hrem
  have hconstant : a - d * u ^ 2 = 0 := const_eq_zero_of_sub_mul_sq hproper hmem hL hrem'
  refine ⟨d, u, 1, v, ?_⟩
  exact quad_eq_affine_square (0 : ℕ) (1 : ℕ) a b c d e f d u 1 v
    (sub_eq_zero.mp hconstant)
    (by simpa using hb) (by simpa using hc) (by simp) (by simpa using he) (by simpa using hf)

/-- Away from characteristic two, a quadratic in `I ^ 2` with nonzero `y ^ 2` coefficient is a
scalar multiple of the square of an affine form. -/
private theorem factor_quad_of_two_ne_zero_f_ne_zero {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin 2) k)) (a b c d e f : k)
    (h2 : (2 : k) ≠ 0) (hf0 : f ≠ 0)
    (hmem : MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X 0 +
      MvPolynomial.C c * MvPolynomial.X 1 + MvPolynomial.C d * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C e * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C f * MvPolynomial.X 1 ^ 2 ∈ I ^ 2)
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I)) :
    ∃ j g h i : k,
      MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X (0 : ℕ) +
        MvPolynomial.C c * MvPolynomial.X (1 : ℕ) +
        MvPolynomial.C d * MvPolynomial.X (0 : ℕ) ^ 2 +
        MvPolynomial.C e * MvPolynomial.X (0 : ℕ) * MvPolynomial.X (1 : ℕ) +
        MvPolynomial.C f * MvPolynomial.X (1 : ℕ) ^ 2 =
      MvPolynomial.C j * (MvPolynomial.C g + MvPolynomial.C h * MvPolynomial.X (0 : ℕ) +
        MvPolynomial.C i * MvPolynomial.X (1 : ℕ)) ^ 2 := by
  have hproper := ideal_ne_top_of_rank_gt_one I hcolength
  obtain ⟨hpx, hpy, hdet⟩ := pderiv_forms_of_mem_sq I a b c d e f hmem hcolength
  let s : k := 2 * f
  let u : k := c / s
  let v : k := e / s
  have hs : s ≠ 0 := mul_ne_zero h2 hf0
  have he : e = s * v := by dsimp [v, s]; field_simp
  have hdet' : s * (2 * d) = e * e := by dsimp only [s]; linear_combination hdet
  have h2d : 2 * d = v * e := mul_left_cancel₀ hs <| by rw [hdet', he]; ring
  have heV : e = v * s := by rw [he]; ring
  have hc : c = s * u := by dsimp [u]; field_simp
  have hb0 : b - v * c = 0 := by
    have hdiffmem := I.sub_mem hpx (I.mul_mem_left (MvPolynomial.C v) hpy)
    rw [affineForm_sub_scaled_eq_const b (2 * d) e c e (2 * f) v h2d heV] at hdiffmem
    exact constant_eq_zero_of_mem_of_ne_top I hdiffmem hproper
  have hb : b = 2 * f * u * v := by
    rw [sub_eq_zero.mp hb0, hc]
    dsimp [s]
    ring
  have hd : d = f * v ^ 2 := mul_left_cancel₀ h2 <| by rw [h2d, he]; dsimp [s]; ring
  have hL : affineForm u v 1 ∈ I := by
    have hrel : affineForm c e s = MvPolynomial.C s * affineForm u v 1 := by
      simpa [affineForm] using affineForm_eq_scaled_gen c e s s u v 1 hc he (by simp)
    exact mem_of_C_mul_mem hs (hrel ▸ hpy)
  have hrem := quad_sub_square_eq_const a b c d e f f u v 1
    (by simpa using hb) (by simpa [s] using hc) (by simpa using hd)
    (by simpa [s] using he) (by simp)
  have hrem' :
      (MvPolynomial.C a + MvPolynomial.C b * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) +
        MvPolynomial.C d * MvPolynomial.X (0 : Fin 2) ^ 2 +
        MvPolynomial.C e * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) +
        MvPolynomial.C f * MvPolynomial.X (1 : Fin 2) ^ 2) -
      MvPolynomial.C f * (affineForm u v 1) ^ 2 = MvPolynomial.C (a - f * u ^ 2) := by
    simpa [affineForm] using hrem
  have hconstant : a - f * u ^ 2 = 0 := const_eq_zero_of_sub_mul_sq hproper hmem hL hrem'
  refine ⟨f, u, v, 1, ?_⟩
  exact quad_eq_affine_square (0 : ℕ) (1 : ℕ) a b c d e f f u v 1
    (sub_eq_zero.mp hconstant) (by simpa using hb) (by simpa [s] using hc)
    (by simpa using hd) (by simpa [s] using he) (by simp)

/-- A nonzero quadratic polynomial in the square of an ideal `I ⊆ κ[x, y]`, where `I`
has colength greater than one, is a scalar multiple of the square of an affine linear
polynomial. -/
@[stacks 0BGD]
theorem eq_smul_sq_affineLinear_of_mem_ideal_sq
    {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 2) k))
    (a b c d e f : k)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0)
    (hmem : C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
      C e * X 0 * X 1 + C f * X 1 ^ 2 ∈ I ^ 2)
    (hcolength : 1 < Module.rank k (MvPolynomial (Fin 2) k ⧸ I)) :
    ∃ j g h i : k,
      C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
          C e * X 0 * X 1 + C f * X 1 ^ 2 =
        C j * (C g + C h * X 0 + C i * X 1) ^ 2 := by
  have hproper := ideal_ne_top_of_rank_gt_one I hcolength
  obtain ⟨hpx, hpy, hdet⟩ := pderiv_forms_of_mem_sq I a b c d e f hmem hcolength
  have hbc : e = 0 → 2 * d = 0 → 2 * f = 0 → b = 0 ∧ c = 0 := fun he hd2 hf2 =>
    ⟨constant_eq_zero_of_mem_of_ne_top I (by simpa [affineForm, he, hd2] using hpx) hproper,
      constant_eq_zero_of_mem_of_ne_top I (by simpa [affineForm, he, hf2] using hpy) hproper⟩
  have hdf : d = 0 → f = 0 → False := by
    intro hd0 hfzero
    have hezero : e = 0 := by simpa [hd0, hfzero] using hdet
    obtain ⟨hbzero, hczero⟩ := hbc hezero (by simp [hd0]) (by simp [hfzero])
    have hamem : C a ∈ I := by
      have hqI := Ideal.pow_le_self (by decide : 2 ≠ 0) hmem
      simpa [hbzero, hczero, hd0, hezero, hfzero] using hqI
    have hazero := constant_eq_zero_of_mem_of_ne_top I hamem hproper
    simp [hazero, hbzero, hczero, hd0, hezero, hfzero] at hnonzero
  have hsqdiv (x z u : k) (hz : z ≠ 0) (hu : u ^ 2 = x / z) : x = z * u ^ 2 := by
    rw [hu]
    field_simp
  by_cases htwo : (2 : k) = 0
  · let : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo
    let : Algebra (ZMod 2) k := ZMod.algebra k 2
    have hezero : e = 0 := by simpa [htwo] using hdet
    obtain ⟨hbzero, hczero⟩ := hbc hezero (by simp [htwo]) (by simp [htwo])
    have hraw : MvPolynomial.C a + MvPolynomial.C d * MvPolynomial.X (0 : Fin 2) ^ 2 +
        MvPolynomial.C f * MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I ^ 2 := by
      simpa [hbzero, hczero, hezero] using hmem
    by_cases hf : f ≠ 0
    · have hscaled := scale_quad_mem I a d f f hf hraw
      have hnorm : MvPolynomial.C (a / f) + MvPolynomial.C (d / f) *
          MvPolynomial.X (0 : Fin 2) ^ 2 + MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I ^ 2 := by
        simpa [div_self hf] using hscaled
      by_cases hdsq : ∃ v : k, v ^ 2 = d / f
      · obtain ⟨v, hv⟩ := hdsq
        by_cases hasq : ∃ u : k, u ^ 2 = a / f
        · obtain ⟨u, hu⟩ := hasq
          exact ⟨f, u, v, 1, quad_eq_affine_square_char_two (0 : ℕ) (1 : ℕ)
            a b c d e f f u v 1 htwo hbzero hczero hezero (hsqdiv a f u hf hu)
            (hsqdiv d f v hf hv) (by simp)⟩
        · obtain ⟨D, hDa⟩ := exists_derivation_detecting_nonsquare (a / f) hasq
          have hDd : D (d / f) = 0 := by
            rw [← hv]
            exact derivation_sq_eq_zero_char_two D v
          exact False.elim (char_two_derivation_constant_contradiction
            I (a / f) (d / f) 1 D hDa hDd (by simp) hproper (by simpa using hnorm))
      · obtain ⟨D, hDd0⟩ := exists_derivation_detecting_nonsquare (d / f) hdsq
        have hDmem := derivation_mem_of_mem_sq I (mvPolynomialCoeffDerivation D) hnorm
        have hnorm' : MvPolynomial.C (a / f) + MvPolynomial.C (d / f) *
            MvPolynomial.X (0 : Fin 2) ^ 2 +
            MvPolynomial.C 1 * MvPolynomial.X (1 : Fin 2) ^ 2 =
            MvPolynomial.C (a / f) + MvPolynomial.C (d / f) *
            MvPolynomial.X (0 : Fin 2) ^ 2 + MvPolynomial.X (1 : Fin 2) ^ 2 := by simp
        rw [hnorm'.symm, mvPolynomialCoeffDerivation_quad] at hDmem
        have hD1 : D 1 = 0 := by simp
        have hlin : MvPolynomial.C (D (a / f)) + MvPolynomial.C (D (d / f)) *
            MvPolynomial.X (0 : Fin 2) ^ 2 ∈ I := by
          simpa [hD1] using hDmem
        let α : k := D (a / f) / D (d / f)
        have hq1 : MvPolynomial.C α + MvPolynomial.X (0 : Fin 2) ^ 2 ∈ I := by
          refine mem_of_C_mul_mem hDd0 ?_
          have hα : D (d / f) * α = D (a / f) := by
            dsimp [α]
            field_simp
          rw [mul_add, ← map_mul, hα]
          exact hlin
        have hpI : MvPolynomial.C (a / f) + MvPolynomial.C (d / f) *
            MvPolynomial.X (0 : Fin 2) ^ 2 + MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I :=
          Ideal.pow_le_self (by decide : 2 ≠ 0) hnorm
        let β : k := a / f + α * (d / f)
        have hq2 : MvPolynomial.C β + MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I := by
          have hsum := I.add_mem hpI (I.mul_mem_left (MvPolynomial.C (d / f)) hq1)
          have heq : MvPolynomial.C β + MvPolynomial.X (1 : Fin 2) ^ 2 =
              (MvPolynomial.C (a / f) + MvPolynomial.C (d / f) *
                MvPolynomial.X (0 : Fin 2) ^ 2 + MvPolynomial.X (1 : Fin 2) ^ 2) +
                  MvPolynomial.C (d / f) *
                  (MvPolynomial.C α + MvPolynomial.X (0 : Fin 2) ^ 2) := by
            dsimp [β]
            simp only [map_add, map_mul]
            ring_nf
            have htwoP : (2 : MvPolynomial (Fin 2) k) = 0 := by
              show MvPolynomial.C (2 : k) = 0
              rw [htwo]
              simp
            rw [htwoP]
            ring
          rwa [heq]
        have hbridge := char_two_derivation_bridge_squares I (a / f) (d / f) α D
          hDd0 (by rfl) hproper hnorm hq1
        obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := hbridge
        have hβ : β = a / f + α * (d / f) := rfl
        exact False.elim (char_two_translated_impossible I (a / f) (d / f) α β r s
          hproper hcolength hr hs hβ hq1 hq2 hnorm hdsq)
    · by_cases hd : d ≠ 0
      · have hfzero : f = 0 := not_ne_iff.mp hf
        have hraw0 : MvPolynomial.C a + MvPolynomial.C d * MvPolynomial.X (0 : Fin 2) ^ 2 +
            MvPolynomial.C 0 * MvPolynomial.X (1 : Fin 2) ^ 2 ∈ I ^ 2 := by
          simpa [hfzero] using hraw
        have hscaled := scale_quad_mem I a d 0 d hd hraw0
        have hnorm : MvPolynomial.C (a / d) + MvPolynomial.X (0 : Fin 2) ^ 2 ∈ I ^ 2 := by
          simpa [div_self hd] using hscaled
        by_cases hasq : ∃ u : k, u ^ 2 = a / d
        · obtain ⟨u, hu⟩ := hasq
          refine ⟨d, u, 1, 0, ?_⟩
          simpa [hfzero] using quad_eq_affine_square_char_two (0 : ℕ) (1 : ℕ)
            a b c d e 0 d u 1 0 htwo hbzero hczero hezero (hsqdiv a d u hd hu)
            (by simp) (by simp)
        · obtain ⟨D, hDa⟩ := exists_derivation_detecting_nonsquare (a / d) hasq
          have hDmem := derivation_mem_of_mem_sq I (mvPolynomialCoeffDerivation D) hnorm
          have hDarg : MvPolynomial.C (a / d) + MvPolynomial.X (0 : Fin 2) ^ 2 =
              MvPolynomial.C (a / d) + MvPolynomial.C 1 * MvPolynomial.X (0 : Fin 2) ^ 2 +
              MvPolynomial.C 0 * MvPolynomial.X (1 : Fin 2) ^ 2 := by simp
          rw [hDarg, mvPolynomialCoeffDerivation_quad] at hDmem
          have hconst : MvPolynomial.C (D (a / d)) ∈ I := by
            simpa using hDmem
          have hzero := constant_eq_zero_of_mem_of_ne_top I hconst hproper
          exact False.elim (hDa hzero)
      · exact (hdf (not_ne_iff.mp hd) (not_ne_iff.mp hf)).elim
  · by_cases hd : d ≠ 0
    · exact factor_quad_of_two_ne_zero_d_ne_zero I a b c d e f htwo hd hmem hcolength
    · by_cases hf0 : f ≠ 0
      · exact factor_quad_of_two_ne_zero_f_ne_zero I a b c d e f htwo hf0 hmem hcolength
      · exact (hdf (not_ne_iff.mp hd) (not_ne_iff.mp hf0)).elim

end MvPolynomial
