module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodUnconditional
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhood

/-!
# Leading coefficients on a chart, and the formal neighbourhood of an integral curve is a domain

Let `D` be an effective Cartier divisor on a scheme `X` with subscheme `C`, and let
`A = lim Γ(Cₙ, 𝒪)` be the ring of compatible functions on its thickenings, filtered by
`Fₙ₊₁ = ker (A ⟶ Γ(Cₙ₊₁, 𝒪))`. Fix an affine open `V = Spec B` of `X` on which `D` is cut out by a
nonzerodivisor `t`. The part of the `N`-th thickening over `V` is `Spec B / t^{N+1}`, and an element
`a ∈ Fₘ` restricts there to the class of `t^m h`; the class of `h` in `B / t = Γ(C ∩ V, 𝒪)` is the
*leading coefficient* of `a` in degree `m`
(`AlgebraicGeometry.Scheme.IdealSheafData.chartLeadingCoeff`).

The leading coefficient is additive and multiplicative across degrees, because restriction to the
chart is a ring map, and it vanishes exactly on `Fₘ₊₁` when `C` is integral and meets `V`: a
function on a thickening vanishing on a dense open of `C` vanishes. As `Γ(C ∩ V, 𝒪)` is then a
domain, the associated graded ring of `A` has no zero divisors, and so neither has `A`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.chartLeadingCoeff`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.chartLeadingCoeff_mul`,
  `chartLeadingCoeff_add`: the leading coefficient is multiplicative and additive.
* `AlgebraicGeometry.Scheme.IdealSheafData.chartLeadingCoeff_eq_zero_iff`: it vanishes exactly on
  the next step of the filtration.
* `AlgebraicGeometry.Scheme.IdealSheafData.mul_notMem_formalNeighborhoodFiltration`: the
  associated graded ring has no zero divisors.
* `AlgebraicGeometry.Scheme.IdealSheafData.isDomain_formalNeighborhoodRing`: **for `C` integral,
  `A` is a domain.**
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (V : X.affineOpens) (t : Γ(X, V.1))

/-! ### Restriction to a chart at different levels -/

/-- The restriction of a compatible function to the chart at level `N` determines it at every
lower level. -/
public theorem formalNeighborhoodChart_eq_mk_of_le {M N : ℕ} (h : M ≤ N)
    {a : formalNeighborhoodRing D} {b : Γ(X, V.1)}
    (hb : formalNeighborhoodChart D V N a = Ideal.Quotient.mk _ b) :
    formalNeighborhoodChart D V M a = Ideal.Quotient.mk _ b := by
  rw [formalNeighborhoodChart_eq_mk_iff] at hb ⊢
  have := thickeningChartSection_eq_of_le D V h _ b hb
  rwa [thickeningRestrictionLE_formalNeighborhoodProjection] at this

/-- A representative over the chart of an element of `Fₘ` lies in `D(V)ᵐ`, at every level
`N ≥ m - 1`. -/
public theorem mem_ideal_pow_of_formalNeighborhoodChart_eq_mk {m N : ℕ} (hmN : m ≤ N + 1)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D m) {b : Γ(X, V.1)}
    (hb : formalNeighborhoodChart D V N a = Ideal.Quotient.mk _ b) : b ∈ D.ideal V ^ m := by
  cases m with
  | zero => simp
  | succ k =>
    have hk := formalNeighborhoodChart_eq_mk_of_le D V (show k ≤ N by omega) hb
    have h0 : formalNeighborhoodChart D V k a = 0 := by
      rw [formalNeighborhoodChart_eq_zero_iff, show formalNeighborhoodProjection D k a = 0 from ha,
        map_zero]
    rw [h0, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hk
    exact hk

variable {D V t}

/-- On a chart where `D` is cut out by `t`, an element of `Fₘ` restricts at level `N ≥ m - 1` to the
class of `tᵐ h` for some `h`. -/
public theorem exists_formalNeighborhoodChart_eq_mk_pow_mul
    (hVt : D.ideal V = Ideal.span {t}) {m N : ℕ} (hmN : m ≤ N + 1)
    {a : formalNeighborhoodRing D} (ha : a ∈ formalNeighborhoodFiltration D m) :
    ∃ h, formalNeighborhoodChart D V N a = Ideal.Quotient.mk _ (t ^ m * h) := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (formalNeighborhoodChart D V N a)
  have hmem := mem_ideal_pow_of_formalNeighborhoodChart_eq_mk D V hmN ha hb.symm
  rw [hVt, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨h, rfl⟩ := hmem
  exact ⟨h, by rw [← hb, mul_comm]⟩

variable (D V t)

open Classical in
/-- **The leading coefficient in degree `m`** over the chart `V` with local equation `t`: for
`a ∈ Fₘ` restricting to the class of `tᵐ h` on `Spec B / t^{m+1}`, the class of `h` in
`B / D(V)`. It is `0` off `Fₘ`. -/
public def chartLeadingCoeff (m : ℕ) (a : formalNeighborhoodRing D) : Γ(X, V.1) ⧸ D.ideal V :=
  if h : ∃ h, formalNeighborhoodChart D V m a = Ideal.Quotient.mk _ (t ^ m * h) then
    Ideal.Quotient.mk _ h.choose
  else 0

variable {D V t}

/-- **The leading coefficient can be read at any higher level.** If `a` restricts at level
`N ≥ m` to the class of `tᵐ h`, its leading coefficient in degree `m` is the class of `h`. -/
public theorem chartLeadingCoeff_eq (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m N : ℕ} (hmN : m ≤ N)
    {a : formalNeighborhoodRing D} {h : Γ(X, V.1)}
    (hh : formalNeighborhoodChart D V N a = Ideal.Quotient.mk _ (t ^ m * h)) :
    chartLeadingCoeff D V t m a = Ideal.Quotient.mk _ h := by
  have hm := formalNeighborhoodChart_eq_mk_of_le D V hmN hh
  have hex : ∃ h, formalNeighborhoodChart D V m a = Ideal.Quotient.mk _ (t ^ m * h) := ⟨h, hm⟩
  rw [chartLeadingCoeff, dite_eq_left_of_eq_true (eq_true hex), Ideal.Quotient.eq]
  have h2 := Ideal.Quotient.eq.1 (hex.choose_spec.symm.trans hm)
  generalize hex.choose = h₀ at h2 ⊢
  rw [hVt, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  rw [hVt, Ideal.mem_span_singleton']
  refine ⟨c, ?_⟩
  have hc' : t ^ m * (c * t) = t ^ m * (h₀ - h) := by
    rw [mul_sub, ← hc]; ring
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem ht m)).1 hc'

/-- **The leading coefficient is multiplicative**: the leading coefficient of a product of an
element of `Fₘ` and one of `Fₙ` in degree `m + n` is the product of the leading coefficients. -/
public theorem chartLeadingCoeff_mul (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m n : ℕ} {a b : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D m) (hb : b ∈ formalNeighborhoodFiltration D n) :
    chartLeadingCoeff D V t (m + n) (a * b) =
      chartLeadingCoeff D V t m a * chartLeadingCoeff D V t n b := by
  obtain ⟨h₁, h₁e⟩ := exists_formalNeighborhoodChart_eq_mk_pow_mul hVt
    (N := m + n) (by omega) ha
  obtain ⟨h₂, h₂e⟩ := exists_formalNeighborhoodChart_eq_mk_pow_mul hVt
    (N := m + n) (by omega) hb
  have hab : formalNeighborhoodChart D V (m + n) (a * b) =
      Ideal.Quotient.mk _ (t ^ (m + n) * (h₁ * h₂)) := by
    rw [map_mul, h₁e, h₂e, ← map_mul]
    congr 1
    ring
  rw [chartLeadingCoeff_eq ht hVt le_rfl hab, chartLeadingCoeff_eq ht hVt (by omega) h₁e,
    chartLeadingCoeff_eq ht hVt (by omega) h₂e, map_mul]

/-- **The leading coefficient is additive** on `Fₘ`. -/
public theorem chartLeadingCoeff_add (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m : ℕ} {a b : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D m) (hb : b ∈ formalNeighborhoodFiltration D m) :
    chartLeadingCoeff D V t m (a + b) =
      chartLeadingCoeff D V t m a + chartLeadingCoeff D V t m b := by
  obtain ⟨h₁, h₁e⟩ := exists_formalNeighborhoodChart_eq_mk_pow_mul hVt (N := m) (by omega) ha
  obtain ⟨h₂, h₂e⟩ := exists_formalNeighborhoodChart_eq_mk_pow_mul hVt (N := m) (by omega) hb
  have hab : formalNeighborhoodChart D V m (a + b) =
      Ideal.Quotient.mk _ (t ^ m * (h₁ + h₂)) := by
    rw [map_add, h₁e, h₂e, ← map_add, mul_add]
  rw [chartLeadingCoeff_eq ht hVt le_rfl hab, chartLeadingCoeff_eq ht hVt le_rfl h₁e,
    chartLeadingCoeff_eq ht hVt le_rfl h₂e, map_add]

/-- An element of `Fₘ₊₁` has leading coefficient `0` in degree `m`. -/
public theorem chartLeadingCoeff_eq_zero_of_mem (ht : t ∈ nonZeroDivisors Γ(X, V.1))
    (hVt : D.ideal V = Ideal.span {t}) {m : ℕ} {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D (m + 1)) : chartLeadingCoeff D V t m a = 0 := by
  obtain ⟨h, he⟩ := exists_formalNeighborhoodChart_eq_mk_pow_mul hVt (N := m) (by omega) ha
  rw [chartLeadingCoeff_eq ht hVt le_rfl (h := t * h) (by rw [he]; congr 1; ring),
    Ideal.Quotient.eq_zero_iff_mem, hVt]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)

/-- **The leading coefficient detects the filtration**: when `C` is integral and meets `V`, an
element of `Fₘ` has leading coefficient `0` in degree `m` exactly when it lies in `Fₘ₊₁`. -/
public theorem chartLeadingCoeff_eq_zero_iff [IsEffectiveCartierDivisor D] [IsIntegral D.subscheme]
    (ht : t ∈ nonZeroDivisors Γ(X, V.1)) (hVt : D.ideal V = Ideal.span {t})
    (hV : Nonempty (D.subschemeι ⁻¹ᵁ V.1)) {m : ℕ} {a : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D m) :
    chartLeadingCoeff D V t m a = 0 ↔ a ∈ formalNeighborhoodFiltration D (m + 1) := by
  refine ⟨fun h0 => ?_, chartLeadingCoeff_eq_zero_of_mem ht hVt⟩
  obtain ⟨h, he⟩ := exists_formalNeighborhoodChart_eq_mk_pow_mul hVt (N := m) (by omega) ha
  rw [chartLeadingCoeff_eq ht hVt le_rfl he, Ideal.Quotient.eq_zero_iff_mem, hVt,
    Ideal.mem_span_singleton'] at h0
  obtain ⟨c, rfl⟩ := h0
  have hz : formalNeighborhoodChart D V m a = 0 := by
    rw [he, Ideal.Quotient.eq_zero_iff_mem, hVt, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩
  rw [formalNeighborhoodChart_eq_zero_iff] at hz
  change formalNeighborhoodProjection D m a = 0
  cases m with
  | zero =>
    refine eq_zero_of_thickeningChartRestrict_eq_zero V inferInstance (fun V' b _ => ?_) hV hz
    simp
  | succ k =>
    exact eq_zero_of_thickeningRestriction_eq_zero V inferInstance
      (show thickeningRestriction D k (formalNeighborhoodProjection D (k + 1) a) = 0 by
        rw [thickeningRestriction_formalNeighborhoodProjection]; exact ha) hV hz

/-- When `C` is integral and meets `V`, the ring `B / D(V) = Γ(C ∩ V, 𝒪)` of leading coefficients
is a domain. -/
public theorem isDomain_quotient_ideal [IsIntegral D.subscheme]
    (hV : Nonempty (D.subschemeι ⁻¹ᵁ V.1)) : IsDomain (Γ(X, V.1) ⧸ D.ideal V) := by
  have e : Γ(X, V.1) ⧸ D.ideal V ≃+* Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1) :=
    (Ideal.quotEquivOfEq (D.ker_subschemeι_app V).symm).trans
      (RingHom.quotientKerEquivOfSurjective (D.subschemeι_app_surjective V))
  exact e.toMulEquiv.isDomain _

/-! ### The associated graded ring has no zero divisors -/

/-- A nonzero element of `A` lies in some step of the filtration but not in the next. -/
public theorem exists_mem_formalNeighborhoodFiltration_notMem_succ {a : formalNeighborhoodRing D}
    (ha : a ≠ 0) :
    ∃ m, a ∈ formalNeighborhoodFiltration D m ∧ a ∉ formalNeighborhoodFiltration D (m + 1) := by
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have hex : ∃ n, a ∉ formalNeighborhoodFiltration D n := by
    by_contra h
    push Not at h
    exact ha (hF.eq_zero_of_forall_mem h)
  classical
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, formalNeighborhoodFiltration_zero] at this
    exact this Submodule.mem_top
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · by_contra h
    exact Nat.find_min hex (by omega) h
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    exact Nat.find_spec hex

/-- **The associated graded ring of the formal neighbourhood of an integral curve has no zero
divisors**: if `a ∈ Fₘ \ Fₘ₊₁` and `b ∈ Fₙ \ Fₙ₊₁` then `a b ∉ Fₘ₊ₙ₊₁`. The leading coefficient
over a chart meeting `C` is multiplicative, with values in the domain `Γ(C ∩ V, 𝒪)`. -/
public theorem mul_notMem_formalNeighborhoodFiltration [IsEffectiveCartierDivisor D]
    [IsIntegral D.subscheme] {m n : ℕ} {a b : formalNeighborhoodRing D}
    (ha : a ∈ formalNeighborhoodFiltration D m) (ha' : a ∉ formalNeighborhoodFiltration D (m + 1))
    (hb : b ∈ formalNeighborhoodFiltration D n) (hb' : b ∉ formalNeighborhoodFiltration D (n + 1)) :
    a * b ∉ formalNeighborhoodFiltration D (m + n + 1) := by
  obtain ⟨V, hqV, t, ht, hVt⟩ := Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor D
    inferInstance (D.subschemeι (genericPoint D.subscheme))
  have hV : Nonempty (D.subschemeι ⁻¹ᵁ V.1) := ⟨⟨genericPoint D.subscheme, hqV⟩⟩
  have := isDomain_quotient_ideal hV
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  intro habF
  have hab := (chartLeadingCoeff_eq_zero_iff ht hVt hV
    (hF.mul_le m n (Ideal.mul_mem_mul ha hb))).2 habF
  rw [chartLeadingCoeff_mul ht hVt ha hb, mul_eq_zero] at hab
  rcases hab with h | h
  · exact ha' ((chartLeadingCoeff_eq_zero_iff ht hVt hV ha).1 h)
  · exact hb' ((chartLeadingCoeff_eq_zero_iff ht hVt hV hb).1 h)

/-- **The ring of compatible functions on the thickenings of an integral effective Cartier divisor
is a domain.** In particular this holds for the formal neighbourhood of a geometrically integral
curve with negative normal bundle. -/
public theorem isDomain_formalNeighborhoodRing [IsEffectiveCartierDivisor D]
    [IsIntegral D.subscheme] : IsDomain (formalNeighborhoodRing D) := by
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  have h1 : (1 : formalNeighborhoodRing D) ∉ formalNeighborhoodFiltration D (0 + 1) := by
    intro h
    obtain ⟨V, hqV, t, ht, hVt⟩ := Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor D
      inferInstance (D.subschemeι (genericPoint D.subscheme))
    have hV : Nonempty (D.subschemeι ⁻¹ᵁ V.1) := ⟨⟨genericPoint D.subscheme, hqV⟩⟩
    have := isDomain_quotient_ideal hV
    have h0 := (chartLeadingCoeff_eq_zero_iff ht hVt hV (m := 0) (a := 1)
      (by rw [formalNeighborhoodFiltration_zero]; exact Submodule.mem_top)).2 h
    rw [chartLeadingCoeff_eq ht hVt le_rfl (h := 1) (by rw [map_one, pow_zero, mul_one, map_one]),
      map_one] at h0
    exact one_ne_zero h0
  have : Nontrivial (formalNeighborhoodRing D) :=
    ⟨⟨1, 0, fun h => h1 (h ▸ zero_mem _)⟩⟩
  have : NoZeroDivisors (formalNeighborhoodRing D) := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨m, ha, ha'⟩ := exists_mem_formalNeighborhoodFiltration_notMem_succ h.1
    obtain ⟨n, hb, hb'⟩ := exists_mem_formalNeighborhoodFiltration_notMem_succ h.2
    exact mul_notMem_formalNeighborhoodFiltration ha ha' hb hb' (hab ▸ zero_mem _)⟩
  exact NoZeroDivisors.to_isDomain _

end AlgebraicGeometry.Scheme.IdealSheafData

end
