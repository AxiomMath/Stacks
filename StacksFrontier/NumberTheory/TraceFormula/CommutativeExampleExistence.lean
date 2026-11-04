module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ProcyclicCochainVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionDerivedVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicKoszulTrace
public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExampleIntegrality

/-!
# The commutative example has abstract trace formulas

Let `q ≥ 1` and `Γ = Ẑ^{(q)} ⋊ Ẑ`, where `1 ∈ Ẑ` acts on `G = Ẑ^{(q)}` by multiplication by a unit
`u`. We show that `Γ` *has an abstract trace formula* in the sense of [Stacks, Section 03VO] in the
two cases singled out by [Stacks, Tag 03VQ]:

* `u = 1`, with all the sets `S_d` empty: then `qu = q`, so the bound `|a| < q` asserted by the
  source fails, and the corrected statement `Stacks.TraceFormula.commutativeExample_integrality`
  is sharp;
* `u = q⁻¹` (`a = qu = 1`), with `S_d` the orbits of exact size `d` of multiplication by `q` on
  `ℤ/(q^d - 1)` (the closed points of degree `d` of `𝐆_m` over a field with `q` elements).

The first condition of an abstract trace formula, `cd_ℓ(G) < ∞`, holds for every `ℓ`: the
continuous cohomology of `Ẑ^{(q)}` with torsion coefficients vanishes in degrees `≥ 2`
(`Stacks.GroupCohomology.hasPrimeBase_of_procyclic`). The trace formula itself comes from the
computation `Tr(γ | LH₀(G, M)) = Tr(γ | M) - Σ_{j < v} Tr(σ^{-j} γ | M)` of
`Stacks.GroupHomology.Procyclic.perfectDerivedTrace_derivedCoinvariantsAction`.

## Main results

* `Stacks.TraceFormula.hasFiniteCohomologicalDimensionAt_of_continuousMulEquiv`: `cd_ℓ < ∞` for a
  group isomorphic to `Ẑ^{(q)}`.
* `Stacks.TraceFormula.commutativeExample_hasAbstractTraceFormula_one`: the case `u = 1`.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
* [Stacks Project, Section 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupHomology Stacks.GroupHomology.Procyclic
  CategoryTheory.FilteredDerived

universe u

namespace Stacks.TraceFormula

/-! ### `cd_ℓ(Ẑ^{(q)}) < ∞` -/

/-- If `n` is a unit in a semiring, then so is every divisor `p` of `n`. -/
private theorem isUnit_natCast_of_dvd {R : Type*} [Semiring R] {n p : ℕ} (hn : IsUnit (n : R))
    (hp : p ∣ n) : IsUnit (p : R) := by
  obtain ⟨m, rfl⟩ := hp
  rw [Nat.cast_mul] at hn
  exact ((Nat.cast_commute (α := R) p m).isUnit_mul_iff.1 hn).1

section CohomologicalDimension

variable {q : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* G)
include e

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- A group isomorphic to `Ẑ^{(q)}` is commutative. -/
public theorem mul_comm_of_continuousMulEquiv (a b : G) : a * b = b * a := by
  apply e.symm.injective
  rw [map_mul, map_mul, mul_comm]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- In a group isomorphic to `Ẑ^{(q)}`, the generator has order prime to every `p ∣ q` in every
finite quotient: it is a `p`-th power. -/
public theorem not_dvd_orderOf_generatorOf {p : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    (N : OpenNormalSubgroup G) :
    ¬ p ∣ orderOf ((generatorOf e : G) : G ⧸ (N : Subgroup G)) := by
  intro hdvd
  obtain ⟨w, hw⟩ := isUnit_natCast_of_dvd (isUnit_natCast_restrictedProfiniteIntegers q) hpq
  set y : G := e (Multiplicative.ofAdd ((w⁻¹ : (RestrictedProfiniteIntegers q)ˣ) :
    RestrictedProfiniteIntegers q))
  have hy : y ^ p = generatorOf e := by
    rw [generatorOf, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ← hw, Units.mul_inv]
  obtain ⟨j, hj⟩ := generatesQuotients_of_continuousMulEquiv e N y
  have h1 : ((generatorOf e : G) : G ⧸ (N : Subgroup G)) ^ (j * p) =
      ((generatorOf e : G) : G ⧸ (N : Subgroup G)) ^ 1 := by
    rw [pow_one, pow_mul, ← hj, ← QuotientGroup.mk_pow, hy]
  rw [pow_eq_pow_iff_modEq] at h1
  have h2 := h1.of_dvd hdvd
  have h3 : j * p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 (dvd_mul_left p j)
  have := h3.symm.trans h2
  rw [Nat.modEq_iff_dvd' (Nat.zero_le 1)] at this
  exact hp.not_dvd_one (by simpa using this)

/-- **`cd_ℓ(Ẑ^{(q)}) < ∞`**: the continuous cohomology of a group isomorphic to `Ẑ^{(q)}` with
`ℓ`-primary torsion coefficients vanishes in degrees `≥ 2`. -/
public theorem hasFiniteCohomologicalDimensionAt_of_continuousMulEquiv (ℓ : ℕ) (hℓ : ℓ.Prime) :
    HasFiniteCohomologicalDimensionAt G ℓ := by
  have hbase : GroupCohomology.HasPrimeBase G :=
    GroupCohomology.hasPrimeBase_of_procyclic (mul_comm_of_continuousMulEquiv e)
      (generatesQuotients_of_continuousMulEquiv e) fun p hp => by
        by_cases hpq : p ∣ q
        · exact Or.inr (not_dvd_orderOf_generatorOf e hp hpq)
        · exact Or.inl (hasPrimePowerQuotients_of_continuousMulEquiv e ⟨p, hp, hpq⟩)
  refine ⟨1, fun i hi A hA => ?_⟩
  refine GroupCohomology.isZero_continuousGroupCohomology_of_torsion.{0, 0} hbase i (by omega) A
    fun a => ?_
  obtain ⟨k, hk⟩ := hA a
  exact ⟨ℓ ^ k, pow_pos hℓ.pos k, hk⟩

end CohomologicalDimension

/-! ### The kernel of the degree -/

section Kernel

variable {q : ℕ} (χ : Multiplicative ProfiniteIntegers →* (RestrictedProfiniteIntegers q)ˣ)

/-- **The kernel of the degree is `Ẑ^{(q)}`**, as a topological group. -/
public def kerEquiv : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* (degree χ).ker where
  toFun x := ⟨incl χ x, by rw [← range_incl_eq_ker_degree]; exact ⟨x, rfl⟩⟩
  invFun g := (g : Gamma χ).left
  left_inv x := rfl
  right_inv g := Subtype.ext (SemidirectProduct.ext rfl (MonoidHom.mem_ker.1 g.2).symm)
  map_mul' x y := Subtype.ext (map_mul (incl χ) x y)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_induced_rng.mpr ?_
    exact continuous_id.prodMk continuous_const
  continuous_invFun := (continuous_left χ).comp continuous_subtype_val

/-- The isomorphism `kerEquiv χ` sends `x ∈ Ẑ^{(q)}` to the element `incl χ x` of `Γ`. -/
@[simp]
public theorem kerEquiv_apply_coe (x : Multiplicative (RestrictedProfiniteIntegers q)) :
    ((kerEquiv χ x : (degree χ).ker) : Gamma χ) = incl χ x :=
  rfl

/-- Conjugation in `Γ` acts on the kernel through `χ` of the degree:
`g x g⁻¹ = χ(deg g) x`. -/
public theorem conj_incl (g : Gamma χ) (x : RestrictedProfiniteIntegers q) :
    g * incl χ (Multiplicative.ofAdd x) * g⁻¹ =
      incl χ (Multiplicative.ofAdd ((χ (degree χ g) : RestrictedProfiniteIntegers q) * x)) := by
  have hg := SemidirectProduct.inl_left_mul_inr_right g
  set a := g.left
  set r := g.right
  have hr : degree χ g = r := rfl
  calc g * incl χ (Multiplicative.ofAdd x) * g⁻¹ =
      SemidirectProduct.inl a * (SemidirectProduct.inr r * incl χ (Multiplicative.ofAdd x) *
        SemidirectProduct.inr r⁻¹) * (SemidirectProduct.inl a)⁻¹ := by
        rw [← hg, map_inv]
        group
    _ = SemidirectProduct.inl a *
        SemidirectProduct.inl (frobeniusAut χ r (Multiplicative.ofAdd x)) *
        (SemidirectProduct.inl a)⁻¹ := by rw [SemidirectProduct.inl_aut]
    _ = incl χ (frobeniusAut χ r (Multiplicative.ofAdd x)) := by
        rw [← map_inv, ← map_mul, ← map_mul, mul_comm a, mul_inv_cancel_right]
    _ = _ := by rw [frobeniusAut_apply, hr]

end Kernel

/-! ### Coefficient rings -/

section Coefficients

variable (Λ : Type u) [Ring Λ] [Finite Λ] {q : ℕ} (hq : IsUnit (q : Λ))
include hq

/-- A prime dividing the characteristic of a finite ring in which `q` is invertible does not
divide `q`. -/
public theorem not_dvd_of_dvd_ringChar {p : ℕ} (hp : p.Prime) (hpc : p ∣ ringChar Λ) : ¬ p ∣ q := by
  intro hpq
  have hunit := isUnit_natCast_of_dvd hq hpq
  obtain ⟨k, hk⟩ := hpc
  have hc0 : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ (ringChar Λ)
  have hk0 : (k : Λ) = 0 := by
    have h : ((p * k : ℕ) : Λ) = 0 := by rw [← hk, ringChar.Nat.cast_ringChar]
    rw [Nat.cast_mul] at h
    exact (hunit.mul_right_eq_zero).1 h
  rw [ringChar.spec] at hk0
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun h => hc0 (by rw [hk, h, mul_zero])
  have := Nat.le_of_dvd hkpos hk0
  rw [hk] at this
  nlinarith [hp.two_le]

omit hq [Finite Λ] in
/-- The characteristic of a finite ring kills it. -/
public theorem ringChar_nsmul_eq_zero (a : Λ) : ringChar Λ • a = 0 := by
  rw [nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

end Coefficients

/-! ### The case `u = 1` -/

section One

variable {q : ℕ}

/-- The trivial character `Ẑ → (Ẑ^{(q)})^×`: `u = 1`. -/
public abbrev trivialCharacter :
    Multiplicative ProfiniteIntegers →* (RestrictedProfiniteIntegers q)ˣ :=
  1

/-- For the trivial character, `Γ = Ẑ^{(q)} × Ẑ` is a topological group. -/
public instance : IsTopologicalGroup (Gamma (trivialCharacter (q := q))) :=
  isTopologicalGroup_gamma _ continuous_const

attribute [local instance] compactSpace_gamma totallyDisconnectedSpace_gamma

/-- **Stacks Project, Tag 03VQ: the case `u = 1`.** The extension `Γ = Ẑ^{(q)} × Ẑ` (the unit `u`
is `1`) has an abstract trace formula with integer `q` and all the sets `S_d` empty. In
particular `qu = q`, so the bound `|a| < q` of the source fails here. -/
public def commutativeExample_abstractTraceFormula_one (hq : 1 ≤ q) :
    AbstractTraceFormula (Gamma (trivialCharacter (q := q))) (degree _) (continuous_degree _)
      (degree_surjective _) where
  q := q
  one_le_q := hq
  S _ := Empty
  F _ x := x.elim
  deg_F _ _ x := x.elim
  finite_cohomologicalDimension ℓ hℓ _ := by
    have := compactSpace_ker (degree (trivialCharacter (q := q))) (continuous_degree _)
    exact hasFiniteCohomologicalDimensionAt_of_continuousMulEquiv (kerEquiv _) ℓ hℓ
  trace_formula Λ _ _ hqΛ M _ _ _ _ _ _ hM n hn := by
    have := compactSpace_ker (degree (trivialCharacter (q := q))) (continuous_degree _)
    have : Finite M := Module.finite_of_finite Λ
    set e := kerEquiv (trivialCharacter (q := q))
    set σ := generatorOf e
    have hgen := generatesQuotients_of_continuousMulEquiv e
    have hc0 : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ (ringChar Λ)
    have hpow : ∀ p : ℕ, p.Prime → p ∣ ringChar Λ → HasPrimePowerQuotients σ p :=
      fun p hp hpc => hasPrimePowerQuotients_of_continuousMulEquiv e
        ⟨p, hp, not_dvd_of_dvd_ringChar Λ hqΛ hp hpc⟩
    set hV := isSmoothFor_ker (degree _) (continuous_degree _) M hM
    have hperf := isPerfect_derivedCoinvariants (Λ := Λ) hgen hc0 hpow
      (ringChar_nsmul_eq_zero Λ) hV
    refine ⟨hperf, fun g _ Φ _ => ?_⟩
    obtain ⟨W, hW⟩ := exists_isDeep (σ := σ) hc0 hpow (ringChar_nsmul_eq_zero Λ) hV.choose
    have hconj : conjContinuousMulEquiv _ (Φ ^ n) σ = σ := by
      refine Subtype.ext ?_
      rw [conjContinuousMulEquiv_apply]
      exact (conj_incl _ _ _).trans (by simp; rfl)
    rw [perfectDerivedTrace_derivedCoinvariantsAction (Φ ^ n) hgen hc0 hpow
      (ringChar_nsmul_eq_zero Λ) hV hperf hV.choose W hV.choose_spec hW (v := 1)
      (by rw [hconj, pow_one])]
    simp

end One

section OneRegistered

variable {q : ℕ}

attribute [local instance] compactSpace_gamma totallyDisconnectedSpace_gamma

/-- **Stacks Project, Tag 03VQ: the case `u = 1`, a counterexample to `|a| < q`.** For every
`q ≥ 1` the extension `1 → Ẑ^{(q)} → Γ → Ẑ → 1` with `F x F⁻¹ = x` (that is, `u = 1`,
`Γ = Ẑ^{(q)} × Ẑ`) has an abstract trace formula with integer `q` and all the sets `S_d` empty;
for it `qu = a = q`, so `|a| < q` fails, and the corrected integrality statement
`Stacks.TraceFormula.commutativeExample_integrality` (`|a| ≤ q`, with `|a| < q` exactly when
`u ≠ 1`) is sharp. -/
@[stacks 03VQ "the case u = 1: Γ = Ẑ^(q) × Ẑ has an abstract trace formula with integer q and all \
S_d empty, so qu = a = q and the source's bound |a| < q fails"]
public theorem commutativeExample_hasAbstractTraceFormula_one (hq : 1 ≤ q) :
    ∃ T : AbstractTraceFormula (Gamma (trivialCharacter (q := q))) (degree _)
        (continuous_degree _) (degree_surjective _),
      T.q = q ∧ (∀ d, IsEmpty (T.S d)) ∧
        frobenius (trivialCharacter (q := q)) * incl _ (Multiplicative.ofAdd 1) *
            (frobenius (trivialCharacter (q := q)))⁻¹ = incl _ (Multiplicative.ofAdd 1) ∧
        ¬ |((q : ℤ) * 1)| < q :=
  ⟨commutativeExample_abstractTraceFormula_one hq, rfl, fun _ => inferInstanceAs (IsEmpty Empty),
    by rw [frobenius_conj]; simp, by simp⟩

end OneRegistered

end Stacks.TraceFormula

end
