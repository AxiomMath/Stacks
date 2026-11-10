module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.RingTheory.CompleteLocalRing.IdealsUnderCompletion
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace
public import StacksFrontier.RingTheory.MvPowerSeries.LowDegree
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian

/-!
# The cotangent space of a power-series ring is computed by polynomials

Let `k` be a field and `A = k[[x_1, …, x_n]]`. The inclusion of `k[x_1, …, x_n]` into `A`
carries the ideal of variables to the maximal ideal of `A` and reflects every power of it. In
consequence an ideal of the polynomial ring generates the maximal ideal of `A` modulo its square
exactly when it generates the ideal of variables modulo its square: the cotangent space of `A`
is computed in the polynomial ring.

## Main results

* `Stacks.MvPowerSeries.map_idealOfVars_eq_maximalIdeal` — the extension of the ideal of
  variables is the maximal ideal.
* `Stacks.MvPowerSeries.comap_coe_pow_maximalIdeal` — a polynomial lies in the `t`-th power of
  the maximal ideal of `A` exactly when it lies in the `t`-th power of the ideal of variables.
* `Stacks.MvPowerSeries.map_coe_sup_sq_eq_maximalIdeal_iff` — an ideal inside the ideal of
  variables generates the maximal ideal of `A` modulo its square exactly when it generates the
  ideal of variables modulo its square.
* `Stacks.MvPowerSeries.map_quotient_coe_eq_maximalIdeal_iff` — an ideal of the polynomial ring
  generates the maximal ideal of `A ⧸ J A` exactly when, together with `J`, it generates the
  ideal of variables modulo its square.
* `Stacks.MvPowerSeries.exists_polynomial_sub_mem_pow_span_range_X` — polynomials are dense for
  the adic filtration: every power series agrees with a polynomial modulo any power of the ideal
  of variables.
* `Stacks.MvPowerSeries.quotientSupPowEquiv` — hence the quotient of `A` by an ideal of the
  polynomial ring together with a power of the maximal ideal is computed in the polynomial
  ring.

## Implementation notes

Both powers are described by the vanishing of coefficients in low total degree, in the
polynomial ring by `MvPolynomial.mem_pow_idealOfVars_iff'` and in `A` by
`Stacks.MvPowerSeries.RegularParameters.coeff_eq_zero_of_mem_pow_maximalIdeal`, which is the
only direction needed since the reverse inclusion comes from extending the ideal.

The descent of the generating condition replaces each power-series coefficient of a relation by
a polynomial approximation of it modulo `𝔪 ^ t`: the error lies in `𝔪 ^ t` times the ideal,
hence in `𝔪 ^ (t + 1)`, so a power-series combination of elements of the ideal agrees modulo
`𝔪 ^ (t + 1)` with a polynomial combination. That is
`Stacks.MvPowerSeries.exists_polynomial_sub_mem_pow_of_mem_map_coe`, proved by induction over
the span; the approximation it uses comes from writing a power series with zero constant term as
`∑ x_i g_i` and recurring on the `g_i`.

## References

* [Stacks Project, Tag 0C4C](https://stacks.math.columbia.edu/tag/0C4C)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open MvPolynomial IsLocalRing

universe u

namespace Stacks.MvPowerSeries

variable {k : Type u} [Field k] {n : ℕ}

/-- The ideal of variables of `k[x_1, …, x_n]` extends to the maximal ideal of
`k[[x_1, …, x_n]]`. -/
theorem map_idealOfVars_eq_maximalIdeal :
    (MvPolynomial.idealOfVars (Fin n) k).map
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) =
      maximalIdeal (_root_.MvPowerSeries (Fin n) k) := by
  rw [_root_.MvPowerSeries.maximalIdeal_eq_span_range_X k n, MvPolynomial.idealOfVars,
    Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  simp [MvPolynomial.coe_X]

/-- A polynomial lies in the `t`-th power of the maximal ideal of `k[[x_1, …, x_n]]` exactly
when it lies in the `t`-th power of the ideal of variables. -/
theorem comap_coe_pow_maximalIdeal (t : ℕ) :
    ((maximalIdeal (_root_.MvPowerSeries (Fin n) k)) ^ t).comap
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) =
      MvPolynomial.idealOfVars (Fin n) k ^ t := by
  apply le_antisymm
  · intro p hp
    rw [Ideal.mem_comap] at hp
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    have hsum : ∑ i, x i < t := by rwa [← Finsupp.degree_eq_sum]
    have h0 := Stacks.MvPowerSeries.RegularParameters.coeff_eq_zero_of_mem_pow_maximalIdeal hp x
      hsum
    rwa [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe] at h0
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_idealOfVars_eq_maximalIdeal]

section Approximation

variable {R : Type*} [CommRing R]

/-- **Polynomials are dense for the adic filtration.** Every power series agrees with a
polynomial modulo any power of the ideal of variables. -/
theorem exists_polynomial_sub_mem_pow_span_range_X (t : ℕ) (f : _root_.MvPowerSeries (Fin n) R) :
    ∃ p : MvPolynomial (Fin n) R,
      f - MvPolynomial.coeToMvPowerSeries.ringHom p ∈
        Ideal.span (Set.range
          (_root_.MvPowerSeries.X : Fin n → _root_.MvPowerSeries (Fin n) R)) ^ t := by
  induction t generalizing f with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
      have h0 : _root_.MvPowerSeries.constantCoeff
          (f - _root_.MvPowerSeries.C (_root_.MvPowerSeries.constantCoeff f)) = (0 : R) := by
        simp
      obtain ⟨g, -, hg⟩ :=
        RegularParameters.exists_sum_X_mul_of_constantCoeff_eq_zero _ h0
      choose q hq using fun i => ih (g i)
      refine ⟨MvPolynomial.C (_root_.MvPowerSeries.constantCoeff f) +
        ∑ i, MvPolynomial.X i * q i, ?_⟩
      have hcoe : MvPolynomial.coeToMvPowerSeries.ringHom
            (MvPolynomial.C (_root_.MvPowerSeries.constantCoeff f) +
              ∑ i, MvPolynomial.X i * q i) =
          _root_.MvPowerSeries.C (_root_.MvPowerSeries.constantCoeff f) +
            ∑ i, _root_.MvPowerSeries.X i *
              MvPolynomial.coeToMvPowerSeries.ringHom (q i) := by
        rw [map_add, map_sum]
        congr 1
        · rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul]
          congr 1
          rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]
      have hsplit : f - MvPolynomial.coeToMvPowerSeries.ringHom
            (MvPolynomial.C (_root_.MvPowerSeries.constantCoeff f) +
              ∑ i, MvPolynomial.X i * q i) =
          ∑ i, _root_.MvPowerSeries.X i *
            (g i - MvPolynomial.coeToMvPowerSeries.ringHom (q i)) := by
        rw [hcoe, ← sub_sub, hg, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
      rw [hsplit, pow_succ']
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (hq i)

end Approximation

/-- Every power series over a field agrees with a polynomial modulo any power of the maximal
ideal. -/
theorem exists_polynomial_sub_mem_pow_maximalIdeal (t : ℕ)
    (f : _root_.MvPowerSeries (Fin n) k) :
    ∃ p : MvPolynomial (Fin n) k, f - MvPolynomial.coeToMvPowerSeries.ringHom p ∈
      maximalIdeal (_root_.MvPowerSeries (Fin n) k) ^ t := by
  rw [_root_.MvPowerSeries.maximalIdeal_eq_span_range_X k n]
  exact exists_polynomial_sub_mem_pow_span_range_X t f

/-- A power-series combination of elements of an ideal of `k[x_1, …, x_n]` inside the ideal of
variables agrees, modulo any power of the maximal ideal, with a polynomial element of that
ideal. -/
theorem exists_polynomial_sub_mem_pow_of_mem_map_coe {M : Ideal (MvPolynomial (Fin n) k)}
    (hM : M ≤ MvPolynomial.idealOfVars (Fin n) k) (t : ℕ)
    {u : _root_.MvPowerSeries (Fin n) k}
    (hu : u ∈ M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) :
    ∃ p ∈ M, u - MvPolynomial.coeToMvPowerSeries.ringHom p ∈
      (maximalIdeal (_root_.MvPowerSeries (Fin n) k)) ^ (t + 1) := by
  have hmemA : ∀ q ∈ M, MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k) q ∈
      maximalIdeal (_root_.MvPowerSeries (Fin n) k) := by
    intro q hq
    rw [← map_idealOfVars_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hM hq)
  rw [Ideal.map, Ideal.span] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, hq, by simp⟩
  | zero => exact ⟨0, M.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨q, hq, hqy⟩ := hy
      refine ⟨p + q, M.add_mem hp hq, ?_⟩
      have he : x + y - MvPolynomial.coeToMvPowerSeries.ringHom (p + q) =
          (x - MvPolynomial.coeToMvPowerSeries.ringHom p) +
            (y - MvPolynomial.coeToMvPowerSeries.ringHom q) := by
        rw [map_add]
        ring
      rw [he]
      exact Ideal.add_mem _ hpx hqy
  | smul a x _ hx =>
      obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨a₀, ha₀⟩ := exists_polynomial_sub_mem_pow_maximalIdeal t a
      refine ⟨a₀ * p, Ideal.mul_mem_left _ _ hp, ?_⟩
      have hsplit : a * x - MvPolynomial.coeToMvPowerSeries.ringHom (a₀ * p) =
          a * (x - MvPolynomial.coeToMvPowerSeries.ringHom p) +
            (a - MvPolynomial.coeToMvPowerSeries.ringHom a₀) *
              MvPolynomial.coeToMvPowerSeries.ringHom p := by
        rw [map_mul]
        ring
      rw [smul_eq_mul, hsplit]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpx) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul ha₀ (hmemA p hp)

/-- A power-series combination of elements of an ideal of `k[x_1, …, x_n]` inside the ideal of
variables agrees, modulo the square of the maximal ideal, with a polynomial element of that
ideal. -/
theorem exists_polynomial_sub_mem_sq_of_mem_map_coe {M : Ideal (MvPolynomial (Fin n) k)}
    (hM : M ≤ MvPolynomial.idealOfVars (Fin n) k) {u : _root_.MvPowerSeries (Fin n) k}
    (hu : u ∈ M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) :
    ∃ p ∈ M, u - MvPolynomial.coeToMvPowerSeries.ringHom p ∈
      (maximalIdeal (_root_.MvPowerSeries (Fin n) k)) ^ 2 :=
  exists_polynomial_sub_mem_pow_of_mem_map_coe hM 1 hu

/-- A polynomial whose image lies in `M k[[x_1, …, x_n]] + 𝔪 ^ (t + 1)` lies in
`M + (x_1, …, x_n) ^ (t + 1)`, for an ideal `M` inside the ideal of variables. -/
private theorem mem_sup_pow_of_coe_mem_map_sup {M : Ideal (MvPolynomial (Fin n) k)}
    (hM : M ≤ MvPolynomial.idealOfVars (Fin n) k) (t : ℕ) {q : MvPolynomial (Fin n) k}
    (hq : MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k) q ∈
      M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ⊔
        maximalIdeal (_root_.MvPowerSeries (Fin n) k) ^ (t + 1)) :
    q ∈ M ⊔ MvPolynomial.idealOfVars (Fin n) k ^ (t + 1) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hq
  obtain ⟨p, hp, hpu⟩ := exists_polynomial_sub_mem_pow_of_mem_map_coe hM t hu
  have he : MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k) (q - p) =
      (u - MvPolynomial.coeToMvPowerSeries.ringHom p) + v := by
    rw [map_sub, ← huv]
    ring
  have hpoly : q - p ∈ MvPolynomial.idealOfVars (Fin n) k ^ (t + 1) := by
    rw [← comap_coe_pow_maximalIdeal (t + 1), Ideal.mem_comap, he]
    exact Ideal.add_mem _ hpu hv
  exact Submodule.mem_sup.2 ⟨p, hp, q - p, hpoly, by ring⟩

/-- **The cotangent space of `k[[x_1, …, x_n]]` is computed in the polynomial ring.** An ideal
inside the ideal of variables generates the maximal ideal of `k[[x_1, …, x_n]]` modulo its
square exactly when it generates the ideal of variables modulo its square. -/
theorem map_coe_sup_sq_eq_maximalIdeal_iff {M : Ideal (MvPolynomial (Fin n) k)}
    (hM : M ≤ MvPolynomial.idealOfVars (Fin n) k) :
    M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ⊔
          (maximalIdeal (_root_.MvPowerSeries (Fin n) k)) ^ 2 =
        maximalIdeal (_root_.MvPowerSeries (Fin n) k) ↔
      M ⊔ MvPolynomial.idealOfVars (Fin n) k ^ 2 = MvPolynomial.idealOfVars (Fin n) k := by
  constructor
  · intro h
    refine le_antisymm (sup_le hM (Ideal.pow_le_self (by norm_num))) ?_
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)
        (MvPolynomial.X i) ∈
        M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ⊔
          (maximalIdeal (_root_.MvPowerSeries (Fin n) k)) ^ 2 := by
      rw [h, ← map_idealOfVars_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    exact SetLike.mem_coe.2 (mem_sup_pow_of_coe_mem_map_sup hM 1 hmem)
  · intro h
    have hmapped := congrArg
      (fun I : Ideal (MvPolynomial (Fin n) k) =>
        I.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) h
    simpa [Ideal.map_sup, Ideal.map_pow, map_idealOfVars_eq_maximalIdeal] using hmapped

/-- An ideal of the polynomial ring inside the ideal of variables extends into the maximal ideal
of the power-series ring. -/
theorem map_le_maximalIdeal_of_le_idealOfVars {M : Ideal (MvPolynomial (Fin n) k)}
    (hM : M ≤ MvPolynomial.idealOfVars (Fin n) k) :
    M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ≤
      maximalIdeal (_root_.MvPowerSeries (Fin n) k) := by
  rw [← map_idealOfVars_eq_maximalIdeal]
  exact Ideal.map_mono hM

/-- An ideal of the polynomial ring inside the ideal of variables extends to a proper ideal of
the power-series ring. -/
theorem map_ne_top_of_le_idealOfVars {M : Ideal (MvPolynomial (Fin n) k)}
    (hM : M ≤ MvPolynomial.idealOfVars (Fin n) k) :
    M.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal (_root_.MvPowerSeries (Fin n) k)).ne_top
    (map_le_maximalIdeal_of_le_idealOfVars hM)

/-- **The Jacobian condition of Tag 0C4C, read in the polynomial ring.** For an ideal `J` of
`k[x_1, …, x_n]` inside the ideal of variables and an arbitrary ideal `N`, the ideal `N`
generates the maximal ideal of `k[[x_1, …, x_n]] / J k[[x_1, …, x_n]]` exactly when `N` together
with `J` generates the ideal of variables modulo its square.

No containment is assumed of `N`: a polynomial of `N` with a nonzero constant term is a unit in
the power-series ring, so `N` then extends to the unit ideal and fails both conditions at
once. -/
theorem map_quotient_coe_eq_maximalIdeal_iff {J N : Ideal (MvPolynomial (Fin n) k)}
    (hJ : J ≤ MvPolynomial.idealOfVars (Fin n) k) :
    letI : Nontrivial (_root_.MvPowerSeries (Fin n) k ⧸
        J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) :=
      Ideal.Quotient.nontrivial_iff.mpr (map_ne_top_of_le_idealOfVars hJ)
    letI : IsLocalRing (_root_.MvPowerSeries (Fin n) k ⧸
        J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    (N.map ((Ideal.Quotient.mk
            (J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)))).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) =
        maximalIdeal (_root_.MvPowerSeries (Fin n) k ⧸
          J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) ↔
      N ⊔ J ⊔ MvPolynomial.idealOfVars (Fin n) k ^ 2 =
        MvPolynomial.idealOfVars (Fin n) k) := by
  let : Nontrivial (_root_.MvPowerSeries (Fin n) k ⧸
      J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_ne_top_of_le_idealOfVars hJ)
  let : IsLocalRing (_root_.MvPowerSeries (Fin n) k ⧸
      J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  by_cases hN : N ≤ MvPolynomial.idealOfVars (Fin n) k
  case neg =>
    obtain ⟨a, haN, havars⟩ := IsConcreteLE.not_le_iff_exists.1 hN
    have hacoe : MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k) a ∉
        maximalIdeal (_root_.MvPowerSeries (Fin n) k) := by
      intro hmem
      refine havars ?_
      have hcomap := comap_coe_pow_maximalIdeal (k := k) (n := n) 1
      rw [pow_one, pow_one] at hcomap
      exact hcomap ▸ Ideal.mem_comap.2 hmem
    have htop : N.map ((Ideal.Quotient.mk
          (J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)))).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haN)
        (RingHom.isUnit_map (Ideal.Quotient.mk
            (J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))))
          (IsLocalRing.notMem_maximalIdeal.1 hacoe))
    refine iff_of_false (fun h => ?_) fun h =>
      hN (le_sup_left.trans (le_sup_left.trans h.le))
    rw [htop] at h
    exact (maximalIdeal.isMaximal _).ne_top h.symm
  have hJA := map_le_maximalIdeal_of_le_idealOfVars hJ
  have hNA := map_le_maximalIdeal_of_le_idealOfVars hN
  rw [← Ideal.map_map, IsLocalRing.map_quotient_eq_maximalIdeal_iff hJA hNA, ← Ideal.map_sup,
    map_coe_sup_sq_eq_maximalIdeal_iff (sup_le hN hJ)]

/-! ### The quotient by a power of the maximal ideal -/

/-- The composite `k[x_1, …, x_n] → k[[x_1, …, x_n]] ⧸ (I + 𝔪 ^ t)` is surjective for every
ideal `I`, because polynomials are dense for the adic filtration. -/
theorem surjective_quotient_mk_comp_coe (I : Ideal (_root_.MvPowerSeries (Fin n) k)) (t : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mk (I ⊔ maximalIdeal (_root_.MvPowerSeries (Fin n) k) ^ t)).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) := by
  intro z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, hp⟩ := exists_polynomial_sub_mem_pow_maximalIdeal t f
  refine ⟨p, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq]
  exact Submodule.mem_sup_right (by simpa using (Ideal.neg_mem_iff _).2 hp)

/-- **The quotient of `k[[x_1, …, x_n]]` by an ideal and a power of the maximal ideal is computed
in the polynomial ring.** For an ideal `J` of `k[x_1, …, x_n]` inside the ideal of variables, the
composite `k[x_1, …, x_n] → k[[x_1, …, x_n]] ⧸ (J k[[x_1, …, x_n]] + 𝔪 ^ (t + 1))` has kernel
`J + (x_1, …, x_n) ^ (t + 1)`. -/
theorem ker_quotient_mk_comp_coe {J : Ideal (MvPolynomial (Fin n) k)}
    (hJ : J ≤ MvPolynomial.idealOfVars (Fin n) k) {t : ℕ} (ht : 1 ≤ t) :
    RingHom.ker ((Ideal.Quotient.mk
          (J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ⊔
            maximalIdeal (_root_.MvPowerSeries (Fin n) k) ^ t)).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) =
      J ⊔ MvPolynomial.idealOfVars (Fin n) k ^ t := by
  obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  refine le_antisymm (fun q hq => ?_) (sup_le (fun q hq => ?_) (fun q hq => ?_))
  · exact SetLike.mem_coe.2 (mem_sup_pow_of_coe_mem_map_sup hJ t (Ideal.mem_comap.1 hq))
  · exact Ideal.mem_comap.2 (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  · refine Ideal.mem_comap.2 (Submodule.mem_sup_right ?_)
    rwa [← comap_coe_pow_maximalIdeal (t + 1)] at hq

/-- **The quotient of `k[[x_1, …, x_n]]` by an ideal and a power of the maximal ideal is computed
in the polynomial ring.** Killing an ideal `J` inside the ideal of variables together with the
`(t+1)`-st power of the maximal ideal gives the same ring in the polynomial ring and in the
power-series ring. -/
noncomputable def quotientSupPowEquiv {J : Ideal (MvPolynomial (Fin n) k)}
    (hJ : J ≤ MvPolynomial.idealOfVars (Fin n) k) {t : ℕ} (ht : 1 ≤ t) :
    (MvPolynomial (Fin n) k ⧸ (J ⊔ MvPolynomial.idealOfVars (Fin n) k ^ t)) ≃+*
      (_root_.MvPowerSeries (Fin n) k ⧸
        (J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)) ⊔
          maximalIdeal (_root_.MvPowerSeries (Fin n) k) ^ t)) :=
  (Ideal.quotEquivOfEq (ker_quotient_mk_comp_coe hJ ht).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_quotient_mk_comp_coe _ _))

/-! ### The quotient of a power-series model by a power of its maximal ideal -/

section Model

variable {T : Type u} [CommRing T] [IsLocalRing T]

/-- A surjection of local rings carries a power of the maximal ideal onto the same power. -/
private theorem map_pow_maximalIdeal_of_surjective {T : Type u} [CommRing T] [IsLocalRing T]
    (π : _root_.MvPowerSeries (Fin n) k →+* T) (hπ : Function.Surjective π) (t : ℕ) :
    (maximalIdeal (_root_.MvPowerSeries (Fin n) k) ^ t).map π = maximalIdeal T ^ t := by
  rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective π hπ]

/-- For a local quotient `T` of `k[[x_1, …, x_n]]`, the polynomial ring surjects onto
`T ⧸ 𝔪_T ^ t`. -/
theorem surjective_mk_pow_comp_coe (π : _root_.MvPowerSeries (Fin n) k →+* T)
    (hπ : Function.Surjective π) (t : ℕ) :
    Function.Surjective (((Ideal.Quotient.mk (maximalIdeal T ^ t)).comp π).comp
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨s, rfl⟩ := hπ y
  obtain ⟨q, hq⟩ := exists_polynomial_sub_mem_pow_maximalIdeal t s
  refine ⟨q, ?_⟩
  have hmap := map_pow_maximalIdeal_of_surjective π hπ t
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq, ← map_sub, ← hmap]
  exact Ideal.mem_map_of_mem _ (by simpa using (Ideal.neg_mem_iff _).2 hq)

/-- **The quotient of a power-series model by a power of its maximal ideal is computed in the
polynomial ring.** If `T` is a local quotient of `k[[x_1, …, x_n]]` by the extension of an ideal
`J` of the polynomial ring inside the ideal of variables, then the kernel of
`k[x_1, …, x_n] → T ⧸ 𝔪_T ^ t` is `J + (x_1, …, x_n) ^ t`. -/
theorem ker_mk_pow_comp_coe {J : Ideal (MvPolynomial (Fin n) k)}
    (hJ : J ≤ MvPolynomial.idealOfVars (Fin n) k)
    (π : _root_.MvPowerSeries (Fin n) k →+* T) (hπ : Function.Surjective π)
    (hker : RingHom.ker π =
      J.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k)))
    {t : ℕ} (ht : 1 ≤ t) :
    RingHom.ker (((Ideal.Quotient.mk (maximalIdeal T ^ t)).comp π).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := k))) =
      J ⊔ MvPolynomial.idealOfVars (Fin n) k ^ t := by
  have hmap := map_pow_maximalIdeal_of_surjective π hπ t
  rw [← ker_quotient_mk_comp_coe hJ ht, ← RingHom.comap_ker, ← RingHom.comap_ker,
    ← RingHom.comap_ker, Ideal.mk_ker, Ideal.mk_ker, ← hmap,
    Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_comm]

end Model

end Stacks.MvPowerSeries

end
