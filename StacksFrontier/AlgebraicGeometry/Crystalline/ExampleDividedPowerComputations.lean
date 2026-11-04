module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero

/-!
# Two explicit divided power computations

This module carries out the two computations that the examples of [Stacks, Tag 07LJ] and
[Stacks, Tag 07LK] perform by hand in their respective divided power rings.

For [Stacks, Tag 07LJ] the setting is the one built in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`: the base
`(A, I, γ) = (ℤ_[p], (p), γ)`, the ring `C = 𝐅_p[x, y]/(x², xy, y²)` presented as
`C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)`, the `p`-adically completed divided power envelope
`D = D_{P, γ}(J)^∧` with divided powers `γ̄`, and the element
`τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)²`.  The computation proved here is the last sentence of the
source: the image of `τ` under the Frobenius lift `σ(x) = x^p`, `σ(y) = y^p` vanishes.

For [Stacks, Tag 07LK] the setting is the one built in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRham`: the base `A = 𝐙_p`,
the ring `C = 𝐅_p[x_1, …, x_r]` presented as `C = P/J = P/pP` with `P = 𝐙_p[x_1, …, x_r]`, and
`D = P^∧`.  The computation proved here is the description of the first differential of the
displayed complex `D → Ω¹_D → ⋯ → Ω^r_D`: on the dense image of `P` it is
`d(f) = ∑_k (∂f/∂x_k) dx_k`, which for `r = 1` and `f = x^n` is the map the source records as
`diag(0, 1, 2, 3, …)`.

## Main definitions

* `Crystalline.TorsionExample.frobeniusTau` is the element
  `γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)²` of `D`, which is the value of `τ` under a divided
  power lift of Frobenius sending `x ↦ x^p` and `y ↦ y^p`.
* `Crystalline.AffineSpaceCrystallineSetup.coordinateImage` is the image in `D` of the `k`-th
  coordinate of `P = 𝐙_p[x_1, …, x_r]`.

## Main results

* `Crystalline.TorsionExample.frobeniusTau_eq_pow_mul_tau` — `frobeniusTau` is `(xy)^{2p(p-1)} τ`,
  by three applications of `γ̄_n(ab) = a^n γ̄_n(b)`.
* `Crystalline.TorsionExample.frobeniusTau_eq_zero` — `frobeniusTau = 0`, because the exponent
  `2p(p-1)` is at least `p`, so the factor `(xy)^{2p(p-1)}` contains `(xy)^p = p! γ̄_p(xy)`, and
  `p! τ = 0` already follows from `p τ = 0`.
* `Crystalline.TorsionExample.map_tau_eq_zero` — the same conclusion for an actual divided power
  endomorphism `σ` of `D` with `σ(x) = x^p` and `σ(y) = y^p`.
* `Crystalline.AffineSpaceCrystallineSetup.differential_algebraMap_eq_sum_pderiv` — the map of
  the displayed complex of [Stacks, Tag 07LK] on the dense image of `P`:
  `d(f) = ∑_k (∂f/∂x_k) dx_k`, with
  `Crystalline.AffineSpaceCrystallineSetup.differential_coordinateImage_pow` —
  `d(x_k^n) = n x_k^{n-1} dx_k` — as the special case the source displays for `r = 1`, and
  `Crystalline.AffineSpaceCrystallineSetup.differential_one` — `d(1) = 0`.

## What each covering set carries

Both tags are examples whose numbered conclusions are stated in the source for
`RΓ(Cris(X/S), 𝒪_{X/S})`, and the comparison that carries them there from the explicit divided
power rings is [Stacks, Tag 07LG].  Each tag's covering set therefore reads the example's
assertions in the explicit terms the example itself computes in — its divided power rings, and
for [Stacks, Tag 07LK] the complex it displays; every description string says which object its
statement is about, and this section records what the passage to crystalline cohomology would
add.

For [Stacks, Tag 07LJ] nothing here is a member of the covering set: `frobeniusTau_eq_zero` is
the explicit computation `γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)² = 0` in `D` behind the final
sentence of the example, and `map_tau_eq_zero` its transport through a divided power
endomorphism `σ` with `σ(x) = x^p`, `σ(y) = y^p`.  The covering set itself — including the two
numbered conclusions about `H⁰(Cris(X/S), 𝒪_{X/S})` and the Frobenius pullback `F^*` on it — is
tabulated in the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`.

For [Stacks, Tag 07LK] nothing here is a member of the covering set either: the covering set —
the comparison of `H^j(Cris(X/S), 𝒪_{X/S})` with the displayed complex and the four numbered
conclusions, all for crystalline cohomology itself — is in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceCrystallineCohomology`.
`differential_algebraMap_eq_sum_pderiv` is the explicit description of the map of the displayed
complex on the dense image of `P`, `d(f) = ∑_k (∂f/∂x_k) dx_k`, which for `r = 1` and `f = x^n` is
the source's `diag(0, 1, 2, 3, …)` (`differential_coordinateImage_pow`).

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public section

namespace Crystalline

/-- `p! = p · (p − 1)!` for a prime `p`, read in an arbitrary commutative ring. -/
private theorem natCast_factorial_eq_prime_mul {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] :
    (p.factorial : R) = (p : R) * ((p - 1).factorial : R) := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

/-! ### Tag 07LJ: the Frobenius lift kills `τ` -/

namespace TorsionExample

variable (p : ℕ) [Fact p.Prime]

/-- The element `γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)²` of `D`.

This is the value of `τ` under a divided power endomorphism `σ` of `D` over `A` induced by the
lift of Frobenius `x ↦ x^p`, `y ↦ y^p` of `P = ℤ_[p][x, y]`, as in the last sentence of
[Stacks, Tag 07LJ]: such a `σ` commutes with the divided powers, so it sends `γ̄_p(x²)` to
`γ̄_p(x^{2p})`, `γ̄_p(y²)` to `γ̄_p(y^{2p})` and `γ̄_p(xy)` to `γ̄_p(x^p y^p)`.  The element is
defined directly, without constructing `σ`. -/
noncomputable def frobeniusTau : completedEnvelope p :=
  (completedGamma p).dpow p (completedX p ^ (2 * p)) *
      (completedGamma p).dpow p (completedY p ^ (2 * p)) -
    (completedGamma p).dpow p (completedX p ^ p * completedY p ^ p) ^ 2

/-- `γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)² = (xy)^{2p(p−1)} τ`.

Each of the three divided powers is taken of a multiple of one of `x²`, `y²`, `xy`, so the rule
`γ̄_n(ab) = a^n γ̄_n(b)` pulls a power of `x` and `y` out of each; the three powers that come out
agree, and the remaining factor is exactly `τ`. -/
theorem frobeniusTau_eq_pow_mul_tau :
    frobeniusTau p = (completedX p * completedY p) ^ (2 * p * (p - 1)) * tau p := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h2 (a : completedEnvelope p) : a ^ (2 * p) = a ^ (2 * q) * a ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have h1 (a : completedEnvelope p) : a ^ p = a ^ q * a := by rw [← pow_succ, ← hq]
  have hZ : completedX p ^ p * completedY p ^ p =
      completedX p ^ q * completedY p ^ q * (completedX p * completedY p) := by
    rw [h1, h1]; ring
  have hE : 2 * p * (p - 1) = 2 * q * p := by rw [hq, Nat.add_sub_cancel]; ring
  rw [frobeniusTau, h2, h2, hZ, hE,
    (completedGamma p).dpow_mul (n := p) (a := completedX p ^ (2 * q)) (completedX_sq_mem p),
    (completedGamma p).dpow_mul (n := p) (a := completedY p ^ (2 * q)) (completedY_sq_mem p),
    (completedGamma p).dpow_mul (n := p) (a := completedX p ^ q * completedY p ^ q)
      (completedX_mul_completedY_mem p),
    tau]
  simp only [mul_pow, ← pow_mul]
  ring

/-- **The last sentence of [Stacks, Tag 07LJ].**  The Frobenius lift `x ↦ x^p`, `y ↦ y^p` kills
`τ`: `γ̄_p(x^{2p}) γ̄_p(y^{2p}) − γ̄_p(x^p y^p)² = 0` in `D`.

By `frobeniusTau_eq_pow_mul_tau` the element is `(xy)^{2p(p-1)} τ`.  Since `p ≥ 2` the exponent
`2p(p-1)` is at least `p`, so the factor splits off `(xy)^p = p! γ̄_p(xy)`; and `p! τ = 0`, since
`p! = p (p-1)!` and `p τ = 0`. -/
theorem frobeniusTau_eq_zero : frobeniusTau p = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hle : p ≤ 2 * p * (p - 1) := by
    rw [show 2 * p * (p - 1) = p * (2 * q) by rw [hq, Nat.add_sub_cancel]; ring]
    exact Nat.le_mul_of_pos_right p (by have := hp.two_le; omega)
  obtain ⟨m, hm⟩ : ∃ m, 2 * p * (p - 1) = m + p := ⟨_, (Nat.sub_add_cancel hle).symm⟩
  have hfac := (completedGamma p).factorial_mul_dpow_eq_pow (n := p)
    (completedX_mul_completedY_mem p)
  have hptau : (p.factorial : completedEnvelope p) * tau p = 0 := by
    rw [natCast_factorial_eq_prime_mul (R := completedEnvelope p) p, mul_right_comm,
      prime_mul_tau_eq_zero, zero_mul]
  rw [frobeniusTau_eq_pow_mul_tau, hm, pow_add, ← hfac]
  linear_combination (completedX p * completedY p) ^ m *
    (completedGamma p).dpow p (completedX p * completedY p) * hptau

/-- A divided power endomorphism `σ` of `(D, J̄, γ̄)` with `σ(x) = x^p` and `σ(y) = y^p` kills `τ`.

This is `frobeniusTau_eq_zero` transported through `σ`, using that `σ` commutes with `γ̄`.  Such a
`σ` is `Crystalline.TorsionExample.frobeniusLift` of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionFrobeniusLift`. -/
theorem map_tau_eq_zero {σ : completedEnvelope p →+* completedEnvelope p}
    (hσ : DividedPowers.IsDPMorphism (completedGamma p) (completedGamma p) σ)
    (hx : σ (completedX p) = completedX p ^ p)
    (hy : σ (completedY p) = completedY p ^ p) :
    σ (tau p) = 0 := by
  have h {a : completedEnvelope p} (ha : a ∈ completedIdeal p) :
      σ ((completedGamma p).dpow p a) = (completedGamma p).dpow p (σ a) :=
    (hσ.dpow_comp _ ha).symm
  rw [tau, map_sub, map_mul, map_pow, h (completedX_sq_mem p), h (completedY_sq_mem p),
    h (completedX_mul_completedY_mem p)]
  simp only [map_pow, map_mul, hx, hy, ← pow_mul, Nat.mul_comm p 2]
  exact frobeniusTau_eq_zero p

end TorsionExample

/-! ### Tag 07LK: the differential on powers of a coordinate -/

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-- The image in `D = P^∧` of the `k`-th coordinate `x_k` of `P = 𝐙_p[x_1, …, x_r]`. -/
noncomputable def coordinateImage (k : Fin T.r) : T.D := algebraMap T.P T.D (MvPolynomial.X k)

/-- `dx_k` is the divided power differential of the `k`-th coordinate. -/
theorem coordinateDifferential_eq (k : Fin T.r) :
    T.coordinateDifferential k = T.differential (T.coordinateImage k) := rfl

/-- The divided power differential of `D` kills `1`. -/
theorem differential_one : T.differential (1 : T.D) = 0 := by
  have h := T.differential_algebraMap 1
  rwa [map_one] at h

/-- `d(x_k^{n+1}) = (n + 1) x_k^n dx_k` in `Ω¹_{D/A, δ}`, by induction on `n` from the Leibniz
rule. -/
theorem differential_coordinateImage_pow_succ (k : Fin T.r) (n : ℕ) :
    T.differential (T.coordinateImage k ^ (n + 1)) =
      ((n + 1 : T.D) * T.coordinateImage k ^ n) • T.coordinateDifferential k := by
  induction n with
  | zero => simp [coordinateDifferential, coordinateImage]
  | succ n ih =>
    rw [pow_succ, T.differential_mul, ih, ← T.coordinateDifferential_eq, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- The divided power differential of `D = P^∧` on a power of a coordinate:
`d(x_k^n) = n x_k^{n-1} dx_k`.

For `r = 1` this is the description the source gives of the single differential
`d : D → Ω¹_D` of the displayed complex as `diag(0, 1, 2, 3, …)`: the `n`-th basis vector `x^n`
goes to `n` times the `(n-1)`-st, and the `n = 0` summand goes to zero, which is the sense in
which "the first summand is missing on the right hand side".  It is the special case
`f = x_k^n` of `differential_algebraMap_eq_sum_pderiv`, which carries the tag. -/
theorem differential_coordinateImage_pow (k : Fin T.r) (n : ℕ) :
    T.differential (T.coordinateImage k ^ n) =
      ((n : T.D) * T.coordinateImage k ^ (n - 1)) • T.coordinateDifferential k := by
  cases n with
  | zero => simp [pow_zero, T.differential_one]
  | succ n => simpa using T.differential_coordinateImage_pow_succ k n

/-- **The map of the displayed complex of [Stacks, Tag 07LK].**  On the image of
`P = 𝐙_p[x_1, …, x_r]`, which is dense in `D = P^∧`, the divided power differential of `D` is
given by the partial derivatives:

`d(f) = ∑_k (∂f/∂x_k) dx_k`.

Since the `d x_k` generate `Ω¹_{D/A, δ}` modulo every power of `p`
(`Crystalline.AffineSpaceCrystallineSetup.differentials_eq_span_sup`) and the image of `P` is
dense in `D`, this determines the differential of the complex completely.  For `r = 1` and
`f = x^n` it is the description the source gives of the single differential as
`diag(0, 1, 2, 3, …)`, which is `differential_coordinateImage_pow`. -/
theorem differential_algebraMap_eq_sum_pderiv (f : T.P) :
    T.differential (algebraMap T.P T.D f) =
      ∑ k : Fin T.r,
        algebraMap T.P T.D (MvPolynomial.pderiv k f) • T.coordinateDifferential k := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun f ↦ T.differential (algebraMap T.P T.D f) =
      ∑ k : Fin T.r,
        algebraMap T.P T.D (MvPolynomial.pderiv k f) • T.coordinateDifferential k) f
    (fun a ↦ ?_) (fun f g hf hg ↦ ?_) (fun f k hf ↦ ?_)
  · have hC : algebraMap T.P T.D (MvPolynomial.C a) = algebraMap T.A T.D a := by
      rw [show (MvPolynomial.C a : T.P) = algebraMap T.A T.P a from rfl]
      exact (IsScalarTower.algebraMap_apply T.A T.P T.D a).symm
    rw [hC, T.differential_algebraMap]
    simp
  · rw [map_add, T.differential_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_add, map_add, add_smul]
  · have hcd : T.differential (algebraMap T.P T.D (MvPolynomial.X k)) =
        T.coordinateDifferential k := rfl
    have hterm : ∀ j : Fin T.r,
        algebraMap T.P T.D (MvPolynomial.pderiv j (f * MvPolynomial.X k)) •
            T.coordinateDifferential j =
          algebraMap T.P T.D (MvPolynomial.X k) •
              (algebraMap T.P T.D (MvPolynomial.pderiv j f) • T.coordinateDifferential j) +
            (if j = k then algebraMap T.P T.D f • T.coordinateDifferential k else 0) := by
      intro j
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, add_smul, smul_smul]
      by_cases hjk : j = k
      · subst hjk
        rw [MvPolynomial.pderiv_X_self, ite_eq_left rfl, map_one, mul_one, mul_comm]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hjk), map_zero, mul_zero, zero_smul,
          ite_eq_right hjk, add_zero, mul_comm]
        exact (add_zero _).symm
    rw [map_mul, T.differential_mul, hf, hcd, Finset.smul_sum,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) ↦ hterm j), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ k
        (fun _ ↦ algebraMap T.P T.D f • T.coordinateDifferential k),
      ite_eq_left (Finset.mem_univ k)]
    exact add_comm _ _

end AffineSpaceCrystallineSetup

end Crystalline

end
