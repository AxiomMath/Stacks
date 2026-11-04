module

public import StacksFrontier.Examples.Flatness.OrdinaryCone.EllipticCocycle
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Segre
public import StacksFrontier.RingTheory.Cech.PuncturedVanishing

/-!
# The Artin–Schreier–Witt cocycle on the Segre product

Let `k` be a field, `G` the cone over the ordinary elliptic curve `E` and `Γ ⊆ G[s, t]` its Segre
product with `k[s, t]`. A degree-zero fraction `g / uⁿ` of `G`, with `g` of degree `n`, is also
the fraction `(g vⁿ) / (u v)ⁿ` of `Γ` for `v ∈ {s, t}`: both fraction fields embed in that of
`G[s, t]`, and there the two agree. We record the subring of the fraction field of `G` of the
fractions that come from `Γ` in this way, and the ring map `toSegreFrac` from it into the fraction
field of `Γ`.

Transporting along this map the Witt vector cocycle `a_x, a_y, c` of the covering of `E` by
`D₊(x)` and `D₊(y)` gives a Witt vector cocycle for the covering of the punctured spectrum of
`Γ` by the `D(w)`, `w ∈ {xs, xt, ys, yt}`: `a_j` is the image of `a_x` for `w_j ∈ {xs, xt}` and of
`a_y` for `w_j ∈ {ys, yt}`, and `b_{ij}` is `0`, `c` or `-c` according to the sides of `w_i` and
`w_j`.

## Main definitions

* `Stacks.Examples.OrdinaryCone.coneFracToPolyFrac`, `segreFracToPolyFrac`: the embeddings of
  the fraction fields of `G` and of `Γ` in that of `G[s, t]`.
* `Stacks.Examples.OrdinaryCone.segreLiftable`: the fractions of `G` that are fractions of `Γ`.
* `Stacks.Examples.OrdinaryCone.toSegreFrac`: the map from them to the fraction field of `Γ`.

## Main results

* `Stacks.Examples.OrdinaryCone.mem_segreComponent_iff`: `Γ_d = G_d ⊗ k[s, t]_d`, the
  polynomials homogeneous of degree `d` in `s, t` with coefficients in `G_d`.
* `Stacks.Examples.OrdinaryCone.exists_toSegreFrac_mem_awaySubring`: the image of `g / uⁿ` lies
  in the image of `Γ[1 / (u v)]`.
* `Stacks.Examples.OrdinaryCone.exists_segre_wittVector_cocycle`: the Witt vector cocycle on the
  covering of the punctured spectrum of `Γ` by `D(xs), D(xt), D(ys), D(yt)`.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open MvPolynomial Stacks.RingTheory.PuncturedVanishing

section Monomial

variable {k : Type*} [CommRing k]

/-- A nonzero exponent vector of degree `d + 1` is `e' + single i 1` with `e'` of degree `d`. -/
private theorem exists_eq_sub_single_add_single {ι : Type*} {e : ι →₀ ℕ} {d : ℕ}
    (he : e.degree = d + 1) :
    ∃ i, e = (e - Finsupp.single i 1) + Finsupp.single i 1 ∧
      (e - Finsupp.single i 1).degree = d := by
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! h
    simp [show e = 0 from Finsupp.ext h] at he
  have he' : e = (e - Finsupp.single i 1) + Finsupp.single i 1 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))).symm
  refine ⟨i, he', ?_⟩
  have := congrArg Finsupp.degree he'
  rw [map_add, Finsupp.degree_single, he] at this
  omega

/-- A monomial `x^a y^b z^c s^p t^q` with `a + b + c = p + q = d` lies in `Γ_d`. -/
theorem C_mk_monomial_mul_monomial_mem_segreComponent {d : ℕ} {e : Fin 3 →₀ ℕ}
    {f : Fin 2 →₀ ℕ} (he : e.degree = d) (hf : f.degree = d) :
    C (Ideal.Quotient.mk (Ideal.span {equation k}) (monomial e 1)) * monomial f 1 ∈
      segreComponent k d := by
  induction d generalizing e f with
  | zero =>
    rw [Finsupp.degree_eq_zero_iff] at he hf
    subst he hf
    suffices ∃ y, C (algebraMap k (Cone k) y) = 1 by
      simpa [segreComponent, Submodule.mem_one] using this
    exact ⟨1, by simp⟩
  | succ d ih =>
    obtain ⟨i, he', hdeg_e⟩ := exists_eq_sub_single_add_single he
    obtain ⟨j, hf', hdeg_f⟩ := exists_eq_sub_single_add_single hf
    rw [he', hf', monomial_add_single, monomial_add_single, pow_one, pow_one, map_mul, map_mul,
      show C (Ideal.Quotient.mk (Ideal.span {equation k}) (monomial (e - Finsupp.single i 1) 1)) *
          C (Ideal.Quotient.mk (Ideal.span {equation k}) (X i)) *
          (monomial (f - Finsupp.single j 1) 1 * X j) =
        (C (Ideal.Quotient.mk (Ideal.span {equation k}) (monomial (e - Finsupp.single i 1) 1)) *
          monomial (f - Finsupp.single j 1) 1) * segreGen k i j by rw [segreGen]; ring,
      segreComponent, pow_succ]
    exact Submodule.mul_mem_mul (ih hdeg_e hdeg_f) (segreGen_mem_segreSpan k i j)

/-- For `g ∈ G_d` and a monomial `sᵖ tᵠ` with `p + q = d`, the product `g sᵖ tᵠ` lies in `Γ_d`. -/
theorem C_mul_monomial_mem_segreComponent {d : ℕ} {g : Cone k} (hg : g ∈ Cone.component k d)
    {f : Fin 2 →₀ ℕ} (hf : f.degree = d) : C g * monomial f 1 ∈ segreComponent k d := by
  obtain ⟨p, hp, rfl⟩ := Cone.mem_component.1 hg
  rw [p.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun e he ↦ ?_
  have hdeg : e.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.1 he)
  have key : C (Ideal.Quotient.mk (Ideal.span {equation k}) (monomial e (coeff e p))) *
      monomial f 1 = coeff e p •
        (C (Ideal.Quotient.mk (Ideal.span {equation k}) (monomial e 1)) * monomial f 1) := by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, ← mul_assoc, ← map_mul,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 3) k) (Cone k),
      Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
    simp only [← map_mul, C_mul_monomial, mul_one]
  rw [key]
  exact Submodule.smul_mem _ _ (C_mk_monomial_mul_monomial_mem_segreComponent hdeg hf)

/-- The coefficients in `G` of an element of `Γ_d` lie in `G_d`. -/
theorem coeff_mem_component_of_mem_segreComponent {d : ℕ} {p : MvPolynomial (Fin 2) (Cone k)}
    (hp : p ∈ segreComponent k d) (b : Fin 2 →₀ ℕ) : p.coeff b ∈ Cone.component k d := by
  classical
  induction d generalizing p b with
  | zero =>
    rw [segreComponent, pow_zero, Submodule.mem_one] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs
    exacts [Cone.algebraMap_mem_component_zero c, zero_mem _]
  | succ d ih =>
    rw [segreComponent, pow_succ] at hp
    have key : segreComponent k d * segreSpan k ≤
        ⨅ b, (Cone.component k (d + 1)).comap ((lcoeff (Cone k) b).restrictScalars k) := by
      refine Submodule.mul_le.mpr fun q hq r hr ↦ ?_
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hr
        refine Submodule.mem_iInf _ |>.mpr fun b ↦ ?_
        show coeff b (q * segreGen k i j) ∈ Cone.component k (d + 1)
        rw [segreGen, mul_left_comm, coeff_C_mul, coeff_mul_X']
        split_ifs
        · rw [add_comm]
          exact Cone.mul_mem_component (Cone.mem_component.2 ⟨X i, isHomogeneous_X _ _, rfl⟩)
            (ih hq _)
        · rw [mul_zero]
          exact zero_mem _
      | zero => rw [mul_zero]; exact zero_mem _
      | add r r' _ _ h h' => rw [mul_add]; exact add_mem h h'
      | smul c r _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    exact (Submodule.mem_iInf _).mp (key hp) b

/-- **The degree `d` part of the Segre product is `G_d ⊗ k[s, t]_d`**: the polynomials in
`s, t` over `G` that are homogeneous of degree `d` in `s, t` with coefficients in `G_d`. -/
theorem mem_segreComponent_iff {d : ℕ} {p : MvPolynomial (Fin 2) (Cone k)} :
    p ∈ segreComponent k d ↔ p.IsHomogeneous d ∧ ∀ b, p.coeff b ∈ Cone.component k d := by
  refine ⟨fun hp ↦ ⟨segreComponent_le_homogeneous k d hp,
    coeff_mem_component_of_mem_segreComponent hp⟩, fun ⟨hp, hc⟩ ↦ ?_⟩
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun b hb ↦ ?_
  rw [← mul_one (coeff b p), ← C_mul_monomial]
  refine C_mul_monomial_mem_segreComponent (hc b) ?_
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.1 hb)

/-- The degree `d` part of the Segre product is contained in the Segre product `Γ`. -/
theorem segreComponent_le_segre (d : ℕ) :
    segreComponent k d ≤ Subalgebra.toSubmodule (segre k) := by
  rw [toSubmodule_segre]
  exact le_iSup (segreComponent k) d

end Monomial

section Transport

variable (k : Type*) [Field k]

local notation "Λ" => FractionRing (MvPolynomial (Fin 2) (Cone k))

/-- The embedding of the fraction field of the cone `G` in that of `G[s, t]`. -/
noncomputable def coneFracToPolyFrac : FractionRing (Cone k) →+* Λ :=
  IsFractionRing.lift (A := Cone k) (K := FractionRing (Cone k))
    (g := (algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ).comp
      (C : Cone k →+* MvPolynomial (Fin 2) (Cone k)))
    (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective _ Λ).comp (C_injective _ _))

/-- The embedding of the fraction field of the Segre product `Γ` in that of `G[s, t]`. -/
noncomputable def segreFracToPolyFrac : FractionRing (segre k) →+* Λ :=
  IsFractionRing.lift (A := segre k) (K := FractionRing (segre k))
    (g := (algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ).comp (segre k).val.toRingHom)
    (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective _ Λ).comp Subtype.val_injective)

/-- A nonzero polynomial in `G[s, t]` has nonzero image in its fraction field. -/
private theorem algebraMap_ne_zero_of_ne_zero {p : MvPolynomial (Fin 2) (Cone k)} (hp : p ≠ 0) :
    algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ p ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hp

/-- The embedding `coneFracToPolyFrac` sends an element `g` of `G` to the constant polynomial
`C g`. -/
@[simp]
theorem coneFracToPolyFrac_algebraMap (g : Cone k) :
    coneFracToPolyFrac k (algebraMap (Cone k) (FractionRing (Cone k)) g) =
      algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (C g) :=
  IsFractionRing.lift_algebraMap (K := FractionRing (Cone k)) _ _

/-- The embedding `segreFracToPolyFrac` sends an element `w` of `Γ` to `w` viewed in `G[s, t]`. -/
@[simp]
theorem segreFracToPolyFrac_algebraMap (w : segre k) :
    segreFracToPolyFrac k (algebraMap (segre k) (FractionRing (segre k)) w) =
      algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (w : MvPolynomial (Fin 2) (Cone k)) :=
  IsFractionRing.lift_algebraMap (K := FractionRing (segre k)) _ _

/-- The fractions of the cone that are fractions of the Segre product, compared in the fraction
field of `G[s, t]`. -/
noncomputable def segreLiftable : Subring (FractionRing (Cone k)) :=
  (segreFracToPolyFrac k).range.comap (coneFracToPolyFrac k)

/-- A fraction `t` of the cone lies in `segreLiftable` if and only if its image in the fraction
field of `G[s, t]` is the image of a fraction of the Segre product. -/
theorem mem_segreLiftable_iff {t : FractionRing (Cone k)} :
    t ∈ segreLiftable k ↔ ∃ u, segreFracToPolyFrac k u = coneFracToPolyFrac k t := by
  rw [segreLiftable, Subring.mem_comap, RingHom.mem_range]

/-- The fraction field of the Segre product is isomorphic to its image in that of `G[s, t]`. -/
noncomputable def segreFracRangeEquiv :
    FractionRing (segre k) ≃+* (segreFracToPolyFrac k).range :=
  RingEquiv.ofBijective (segreFracToPolyFrac k).rangeRestrict
    ⟨fun _ _ h ↦ (segreFracToPolyFrac k).injective (congrArg Subtype.val h),
      (segreFracToPolyFrac k).rangeRestrict_surjective⟩

/-- The map from the fractions of the cone that are fractions of the Segre product to the fraction
field of the Segre product; it sends `g / uⁿ`, with `g` of degree `n`, to `(g vⁿ) / (u v)ⁿ`. -/
noncomputable def toSegreFrac : segreLiftable k →+* FractionRing (segre k) :=
  (segreFracRangeEquiv k).symm.toRingHom.comp ((coneFracToPolyFrac k).restrict _ _ fun _ h ↦ h)

/-- The image of `toSegreFrac t` in the fraction field of `G[s, t]` is the image of `t`. -/
theorem segreFracToPolyFrac_toSegreFrac (t : segreLiftable k) :
    segreFracToPolyFrac k (toSegreFrac k t) = coneFracToPolyFrac k t :=
  congrArg Subtype.val ((segreFracRangeEquiv k).apply_symm_apply ⟨coneFracToPolyFrac k t, t.2⟩)

/-- `toSegreFrac t = u` if and only if `u` and `t` have the same image in the fraction field of
`G[s, t]`. -/
theorem toSegreFrac_eq_iff {t : segreLiftable k} {u : FractionRing (segre k)} :
    toSegreFrac k t = u ↔ segreFracToPolyFrac k u = coneFracToPolyFrac k t :=
  ⟨fun h ↦ h ▸ segreFracToPolyFrac_toSegreFrac k t,
    fun h ↦ (segreFracToPolyFrac k).injective (by rw [h, segreFracToPolyFrac_toSegreFrac])⟩

/-- If `sⁿ t = g` in the fraction field of `G` and `w = s · m` in `Γ` for a monomial `m` in
`s, t` with `g mⁿ ∈ Γ`, then `t` is a fraction of `Γ` and its image in the fraction field of `Γ`
is `g mⁿ / wⁿ`. -/
theorem exists_toSegreFrac_mul_pow_eq {t : FractionRing (Cone k)} {s g : Cone k} {n : ℕ}
    (hs : s ≠ 0)
    (h : algebraMap (Cone k) (FractionRing (Cone k)) s ^ n * t =
      algebraMap (Cone k) (FractionRing (Cone k)) g)
    {w : segre k} {f : Fin 2 →₀ ℕ} (hw : (w : MvPolynomial (Fin 2) (Cone k)) = C s * monomial f 1)
    (v : segre k) (hv : (v : MvPolynomial (Fin 2) (Cone k)) = C g * monomial (n • f) 1) :
    ∃ ht : t ∈ segreLiftable k,
      toSegreFrac k ⟨t, ht⟩ * algebraMap (segre k) (FractionRing (segre k)) w ^ n =
        algebraMap (segre k) (FractionRing (segre k)) v := by
  have hw0 : (w : MvPolynomial (Fin 2) (Cone k)) ≠ 0 :=
    hw ▸ mul_ne_zero (by simpa using hs) (by simp [monomial_eq_zero])
  have hPw : algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ w ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero k hw0
  have hw0' : algebraMap (segre k) (FractionRing (segre k)) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr fun h0 ↦
      hw0 (by rw [h0, ZeroMemClass.coe_zero])
  have key : algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (w : MvPolynomial (Fin 2) (Cone k)) ^ n *
      coneFracToPolyFrac k t = algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ v := by
    have := congrArg (coneFracToPolyFrac k) h
    rw [map_mul, map_pow, coneFracToPolyFrac_algebraMap, coneFracToPolyFrac_algebraMap] at this
    rw [hw, hv, show (monomial (n • f) (1 : Cone k)) = monomial f 1 ^ n by
      rw [monomial_pow, one_pow], map_mul, map_mul, map_pow, mul_pow, ← this]
    ring
  obtain ⟨u, hu_def⟩ : ∃ u, u = algebraMap (segre k) (FractionRing (segre k)) v /
    algebraMap (segre k) (FractionRing (segre k)) w ^ n := ⟨_, rfl⟩
  have hu : segreFracToPolyFrac k u = coneFracToPolyFrac k t := by
    rw [hu_def, map_div₀, map_pow, segreFracToPolyFrac_algebraMap, segreFracToPolyFrac_algebraMap,
      div_eq_iff (pow_ne_zero _ hPw), ← key, mul_comm]
  have ht : t ∈ segreLiftable k := (mem_segreLiftable_iff k).mpr ⟨u, hu⟩
  refine ⟨ht, ?_⟩
  rw [(toSegreFrac_eq_iff k (t := ⟨t, ht⟩)).mpr hu, hu_def, div_mul_cancel₀ _ (pow_ne_zero _ hw0')]

/-- A function on the basic open `D₊(s)` of `E`, with `s` of degree `m`, is a fraction of `Γ`
whose image lies in the image of `Γ[1 / w]` for `w = s · m'` with `m'` a monomial of degree `m`
in `s, t`. -/
theorem exists_toSegreFrac_mem_awaySubring {s : Cone k} {m : ℕ} {hs : s ∈ Cone.component k m}
    (hs0 : s ≠ 0) {t : FractionRing (Cone k)} (ht : t ∈ Cone.away k s m hs) {w : segre k}
    {f : Fin 2 →₀ ℕ} (hw : (w : MvPolynomial (Fin 2) (Cone k)) = C s * monomial f 1)
    (hf : f.degree = m) :
    ∃ h : t ∈ segreLiftable k, toSegreFrac k ⟨t, h⟩ ∈ awaySubring (FractionRing (segre k)) w := by
  obtain ⟨n, g, hg, hgt⟩ := (Cone.mem_away k).mp ht
  have hdeg : (n • f).degree = m * n := by rw [map_nsmul, hf, smul_eq_mul, mul_comm]
  let v : segre k := ⟨_, segreComponent_le_segre _ (C_mul_monomial_mem_segreComponent hg hdeg)⟩
  obtain ⟨h, e⟩ := exists_toSegreFrac_mul_pow_eq k hs0 hgt hw v rfl
  exact ⟨h, n, v, by rw [map_pow, ← e, mul_comm]⟩

/-- A function on `D₊(x)` maps into the images of `Γ[1 / (xs)]` and `Γ[1 / (xt)]`. -/
theorem exists_toSegreFrac_mem_awaySubring_of_mem_awayX {t : FractionRing (Cone k)}
    (ht : t ∈ Cone.awayX k) (j : Fin 2) :
    ∃ h : t ∈ segreLiftable k,
      toSegreFrac k ⟨t, h⟩ ∈ awaySubring (FractionRing (segre k)) (segreElem k 0 j) :=
  exists_toSegreFrac_mem_awaySubring k (Cone.x_ne_zero k) ht rfl (by simp)

/-- A function on `D₊(y)` maps into the images of `Γ[1 / (ys)]` and `Γ[1 / (yt)]`. -/
theorem exists_toSegreFrac_mem_awaySubring_of_mem_awayY {t : FractionRing (Cone k)}
    (ht : t ∈ Cone.awayY k) (j : Fin 2) :
    ∃ h : t ∈ segreLiftable k,
      toSegreFrac k ⟨t, h⟩ ∈ awaySubring (FractionRing (segre k)) (segreElem k 1 j) :=
  exists_toSegreFrac_mem_awaySubring k (Cone.y_ne_zero k) ht rfl (by simp)

/-- A function on `D₊(x) ∩ D₊(y)` maps into the images of `Γ[1 / (xu · yv)]` for
`u, v ∈ {s, t}`. -/
theorem exists_toSegreFrac_mem_awaySubring_of_mem_awayXY {t : FractionRing (Cone k)}
    (ht : t ∈ Cone.awayXY k) (u v : Fin 2) :
    ∃ h : t ∈ segreLiftable k, toSegreFrac k ⟨t, h⟩ ∈
      awaySubring (FractionRing (segre k)) (segreElem k 0 u * segreElem k 1 v) := by
  refine exists_toSegreFrac_mem_awaySubring k (mul_ne_zero (Cone.x_ne_zero k) (Cone.y_ne_zero k))
    ht (f := Finsupp.single u 1 + Finsupp.single v 1) ?_ (by simp)
  rw [Subalgebra.coe_mul, coe_segreElem, coe_segreElem, segreGen, segreGen,
    show (monomial (Finsupp.single u 1 + Finsupp.single v 1) (1 : Cone k)) = X u * X v by
      rw [X, X, monomial_mul_monomial, one_mul], Cone.x, Cone.y, map_mul]
  ring

/-- The image of `(z / x)²` is `(zs)² / (xs)²`. -/
theorem toSegreFrac_eq_sq_z_div_x {t : segreLiftable k}
    (ht : (t : FractionRing (Cone k)) = (algebraMap (Cone k) (FractionRing (Cone k)) (Cone.z k) /
      algebraMap (Cone k) (FractionRing (Cone k)) (Cone.x k)) ^ 2) :
    toSegreFrac k t = algebraMap (segre k) (FractionRing (segre k)) (segreElem k 2 0 ^ 2) /
      algebraMap (segre k) (FractionRing (segre k)) (segreElem k 0 0 ^ 2) := by
  have hx : algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (C (Cone.x k)) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero k (by simpa using Cone.x_ne_zero k)
  have hX : algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (X 0) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero k (X_ne_zero 0)
  refine (toSegreFrac_eq_iff k).mpr ?_
  rw [ht, map_div₀, segreFracToPolyFrac_algebraMap, segreFracToPolyFrac_algebraMap, map_pow,
    map_div₀, coneFracToPolyFrac_algebraMap, coneFracToPolyFrac_algebraMap, Subalgebra.coe_pow,
    Subalgebra.coe_pow, coe_segreElem, coe_segreElem, segreGen, segreGen, map_pow, map_pow,
    map_mul, map_mul]
  show _ = (algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (C (Cone.z k)) /
    algebraMap (MvPolynomial (Fin 2) (Cone k)) Λ (C (Cone.x k))) ^ 2
  simp only [Cone.x, Cone.z] at hx ⊢
  field_simp

/-- If the coefficients of a Witt vector over `segreLiftable` lie in `S` and every element of `S`
maps into the image of `Γ[1 / w]`, then so do the coefficients of its image over `Frac Γ`. -/
private theorem map_toSegreFrac_mem_coeffSubring {S : Subalgebra k (FractionRing (Cone k))}
    {v : WittVector 2 (segreLiftable k)}
    (hv : WittVector.map (segreLiftable k).subtype v ∈ WittVector.coeffSubring 2 S.toSubring)
    {w : segre k} (hS : ∀ t ∈ S, ∃ h : t ∈ segreLiftable k,
      toSegreFrac k ⟨t, h⟩ ∈ awaySubring (FractionRing (segre k)) w) :
    WittVector.map (toSegreFrac k) v ∈
      WittVector.coeffSubring 2 (awaySubring (FractionRing (segre k)) w) :=
  WittVector.mem_coeffSubring_iff.2 fun n ↦ by
    have := WittVector.mem_coeffSubring_iff.1 hv n
    rw [WittVector.map_coeff] at this ⊢
    exact (hS _ this).2

end Transport

section Cocycle

variable (k : Type*) [Field k] [CharP k 2]

open WittVector in
/-- **The Artin–Schreier–Witt cocycle on the Segre product.** For a field `k` of characteristic
two in which every element has the form `μ² + μ`, there are Witt vectors `a j` and `b i j` over
the fraction field of `Γ`, for `w = (xs, xt, ys, yt)`, with the coefficients of `a j` in the image
of `Γ[1 / w j]` and those of `b i j` in the image of `Γ[1 / (w i * w j)]`, forming a Čech cocycle
`b i j + b j l = b i l` with `F (b i j) - b i j = a i - a j`, and with
`(a 0).coeff 0 = (zs)² / (xs)²`. -/
theorem exists_segre_wittVector_cocycle (hk : ∀ l : k, ∃ μ : k, μ ^ 2 + μ = l) :
    ∃ (a : Fin 4 → WittVector 2 (FractionRing (segre k)))
      (b : Fin 4 → Fin 4 → WittVector 2 (FractionRing (segre k))),
      (∀ j n, (a j).coeff n ∈ awaySubring (FractionRing (segre k)) (segreCover k j)) ∧
      (∀ i j n, (b i j).coeff n ∈
        awaySubring (FractionRing (segre k)) (segreCover k i * segreCover k j)) ∧
      (∀ i j l, b i j + b j l = b i l) ∧ (∀ i, b i i = 0) ∧
      (∀ i j, frobenius (b i j) - b i j = a i - a j) ∧
      (a 0).coeff 0 = algebraMap (segre k) (FractionRing (segre k)) (segreElem k 2 0 ^ 2) /
        algebraMap (segre k) (FractionRing (segre k)) (segreElem k 0 0 ^ 2) := by
  obtain ⟨aX, haX, aY, haY, c, hc, h0, -, -, hcoc⟩ := Cone.exists_wittVector_cocycle k hk
  have hXl : (Cone.awayX k).toSubring ≤ segreLiftable k := fun t ht ↦
    (exists_toSegreFrac_mem_awaySubring_of_mem_awayX k ht 0).1
  have hYl : (Cone.awayY k).toSubring ≤ segreLiftable k := fun t ht ↦
    (exists_toSegreFrac_mem_awaySubring_of_mem_awayY k ht 0).1
  have hXYl : (Cone.awayXY k).toSubring ≤ segreLiftable k := fun t ht ↦
    (exists_toSegreFrac_mem_awaySubring_of_mem_awayXY k ht 0 0).1
  obtain ⟨aX', rfl⟩ := coeffSubring_mono hXl haX
  obtain ⟨aY', rfl⟩ := coeffSubring_mono hYl haY
  obtain ⟨c', rfl⟩ := coeffSubring_mono hXYl hc
  have hcoc' : aY' - aX' = frobenius c' - c' :=
    map_injective (segreLiftable k).subtype Subtype.val_injective (by
      rw [map_sub, map_sub, hcoc, (frobenius_isPoly 2).map])
  obtain ⟨AX, hAXd⟩ : ∃ AX, AX = map (toSegreFrac k) aX' := ⟨_, rfl⟩
  obtain ⟨AY, hAYd⟩ : ∃ AY, AY = map (toSegreFrac k) aY' := ⟨_, rfl⟩
  obtain ⟨C', hCd⟩ : ∃ C', C' = map (toSegreFrac k) c' := ⟨_, rfl⟩
  have hcoc'' : AY - AX = frobenius C' - C' := by
    rw [hAXd, hAYd, hCd, ← map_sub, hcoc', map_sub, (frobenius_isPoly 2).map]
  have hAX (j : Fin 2) : AX ∈ coeffSubring 2 (awaySubring (FractionRing (segre k))
      (segreElem k 0 j)) := by
    rw [hAXd]
    exact map_toSegreFrac_mem_coeffSubring k haX fun t ht ↦
      exists_toSegreFrac_mem_awaySubring_of_mem_awayX k ht j
  have hAY (j : Fin 2) : AY ∈ coeffSubring 2 (awaySubring (FractionRing (segre k))
      (segreElem k 1 j)) := by
    rw [hAYd]
    exact map_toSegreFrac_mem_coeffSubring k haY fun t ht ↦
      exists_toSegreFrac_mem_awaySubring_of_mem_awayY k ht j
  have hC (u v : Fin 2) : C' ∈ coeffSubring 2 (awaySubring (FractionRing (segre k))
      (segreElem k 0 u * segreElem k 1 v)) := by
    rw [hCd]
    exact map_toSegreFrac_mem_coeffSubring k hc fun t ht ↦
      exists_toSegreFrac_mem_awaySubring_of_mem_awayXY k ht u v
  have hC' (u v : Fin 2) : C' ∈ coeffSubring 2 (awaySubring (FractionRing (segre k))
      (segreElem k 1 v * segreElem k 0 u)) := mul_comm (segreElem k 0 u) _ ▸ hC u v
  let β (p q : Bool) : WittVector 2 (FractionRing (segre k)) :=
    cond p (cond q 0 C') (cond q (-C') 0)
  have hβ (p q r : Bool) : β p q + β q r = β p r := by
    cases p <;> cases q <;> cases r <;> simp [β]
  have hβ' (p : Bool) : β p p = 0 := by cases p <;> rfl
  have hβF (p q : Bool) : frobenius (β p q) - β p q = cond p AY AX - cond q AY AX := by
    cases p <;> cases q
    · simp [β]
    · rw [show β false true = -C' from rfl, map_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub,
        ← hcoc'', neg_sub]
      rfl
    · exact hcoc''.symm
    · simp [β]
  let σ : Fin 4 → Bool := ![false, false, true, true]
  refine ⟨fun i ↦ cond (σ i) AY AX, fun i j ↦ β (σ i) (σ j), fun j ↦ ?_, fun i j ↦ ?_,
    fun i j l ↦ hβ _ _ _, fun i ↦ hβ' _, fun i j ↦ hβF _ _, ?_⟩
  · refine mem_coeffSubring_iff.1 ?_
    fin_cases j
    exacts [hAX 0, hAX 1, hAY 0, hAY 1]
  · refine mem_coeffSubring_iff.1 ?_
    fin_cases i <;> fin_cases j <;> simp [σ, β, segreCover, hC, hC']
  · show (cond (σ 0) AY AX).coeff 0 = _
    rw [show cond (σ 0) AY AX = AX from rfl, hAXd, map_coeff]
    exact toSegreFrac_eq_sq_z_div_x k (by rw [← h0, map_coeff]; rfl)

end Cocycle

end Stacks.Examples.OrdinaryCone
