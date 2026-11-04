module

public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import StacksCore.Tactic.StacksAttribute

/-!
# The commutative example of an abstract trace formula

Fix an integer `q ≥ 1`. The example in question concerns an extension of profinite groups
`1 → G → Γ → Ẑ → 1` whose kernel is the group `G = Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ` of profinite
integers prime to `q`, in which a Frobenius element `F` has degree `1` and acts on the kernel
by `F x F⁻¹ = u x` for a unit `u` of `Ẑ^{(q)}`. Such an extension is exhibited as the
semidirect product `Ẑ^{(q)} ⋊ Ẑ` in which `z` acts as multiplication by `u^z`.

Evaluating an abstract trace formula for `Γ` on the trivial coefficient modules `ℤ/mℤ` gives
the congruence `q^n - (qu)^n ≡ ∑_{d ∣ n} d · #S_d` modulo every `m` prime to `q`. That
congruence forces `qu` to be an ordinary integer `a`, namely `a = q - #S_1`, and it pins down
`a` to the range `-q < a ≤ q`, with `a = q` exactly when every `S_d` is empty; so `|a| < q`
as soon as one `S_d` is nonempty.

## Main definitions

* `Stacks.TraceFormula.RestrictedProfiniteIntegers` — the ring `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ`, and
  `Stacks.TraceFormula.ProfiniteIntegers` the ring `Ẑ = ∏_ℓ ℤ_ℓ`, its value at `q = 1`.
* `Stacks.TraceFormula.frobeniusAut` — the action of `Ẑ` on `Ẑ^{(q)}` in which `z` acts as
  multiplication by `u^z`, and `Stacks.TraceFormula.Gamma` the resulting extension
  `Γ = Ẑ^{(q)} ⋊ Ẑ`, with `Stacks.TraceFormula.degree`, `Stacks.TraceFormula.incl` and
  `Stacks.TraceFormula.frobenius` its degree map, its kernel inclusion and its Frobenius.
* `Stacks.TraceFormula.pointCountSum` — the sum `∑_{d ∣ n} d · #S_d`.
* `Stacks.TraceFormula.IsTrivialModuleCongruence` — the congruence
  `q^n - b^n ≡ ∑_{d ∣ n} d · #S_d` modulo every prime power prime to `q`.
* `Stacks.TraceFormula.traceParameter` — the integer `a = q - #S_1`.
* `Stacks.TraceFormula.instTopologicalSpaceGamma` and `Stacks.TraceFormula.homeomorphProd` —
  the topology of `Γ`, which is that of the product of its two factors.

## Main statements

* `Stacks.TraceFormula.degree_surjective`, `Stacks.TraceFormula.range_incl_eq_ker_degree` and
  `Stacks.TraceFormula.incl_injective` — exactness of `1 → Ẑ^{(q)} → Γ → Ẑ → 1`.
* `Stacks.TraceFormula.degree_frobenius` and `Stacks.TraceFormula.frobenius_conj` — the
  Frobenius has degree `1` and conjugates `x` to `u x`.
* `Stacks.TraceFormula.isTopologicalGroup_gamma`, `Stacks.TraceFormula.compactSpace_gamma`
  and `Stacks.TraceFormula.totallyDisconnectedSpace_gamma` — `Γ` is a profinite group, and
  `Stacks.TraceFormula.continuous_degree` — its degree map is continuous.
* `Stacks.TraceFormula.eq_intCast_traceParameter` — the congruence forces `qu = a` for the
  integer `a = q - #S_1`.
* `Stacks.TraceFormula.neg_lt_traceParameter`, `Stacks.TraceFormula.traceParameter_le` and
  `Stacks.TraceFormula.traceParameter_eq_iff` — the range `-q < a ≤ q` and the characterisation
  of the extreme value `a = q`.
* `Stacks.TraceFormula.exists_intCast_eq_and_abs_lt` — the conclusion `qu = a ∈ ℤ`, `|a| < q`.

## Implementation notes

`Ẑ` is realised as `∏_ℓ ℤ_ℓ`, the special case `q = 1` of `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ`, which is
the profinite completion of `ℤ` and the same product the source writes for the kernel. Both are
compact and totally disconnected topological rings.

The congruence `q^n - (qu)^n ≡ ∑_{d ∣ n} d · #S_d` is required only modulo the prime powers
`ℓ^k` with `ℓ ∤ q`, through the reductions `PadicInt.toZModPow`; these are among the moduli `m`
prime to `q` of the source, so this is the weaker hypothesis of the two and the conclusions
drawn from it are correspondingly stronger. No trace is formed here: the congruence is taken as
a hypothesis, since the abstract trace formula itself — continuous derived coinvariants and
traces of perfect complexes — is not available.

The exhibited extension is a semidirect product for the action of `Ẑ` on `Ẑ^{(q)}` by the
powers `u^z` of the unit `u = χ 1`, and the homomorphism `χ : Ẑ → (Ẑ^{(q)})ˣ` recording those
powers is a parameter of the construction: the extension of `n ↦ u^n` from `ℤ` to `Ẑ`, which
produces `χ` from `u` alone, is exponentiation by profinite integers in a profinite group and
is not available.

The semidirect product carries the product topology of its two factors, which makes it compact
and totally disconnected outright, and a topological group as soon as `χ` is continuous; so a
continuous `χ` exhibits `Γ` as a profinite group.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
* [Stacks Project, Tag 03VO](https://stacks.math.columbia.edu/tag/03VO)
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

/-- The primes `ℓ` which do not divide `q`. -/
public abbrev CoprimePrimes (q : ℕ) : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ q}

/-- Every element of `CoprimePrimes q` is a prime number. -/
public instance (q : ℕ) (p : CoprimePrimes q) : Fact p.1.Prime := ⟨p.2.1⟩

/-- The ring `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ` of profinite integers prime to `q`. -/
public abbrev RestrictedProfiniteIntegers (q : ℕ) : Type := ∀ p : CoprimePrimes q, ℤ_[p.1]

/-- The ring `Ẑ = ∏_ℓ ℤ_ℓ` of profinite integers, the profinite completion of `ℤ`. -/
public abbrev ProfiniteIntegers : Type := RestrictedProfiniteIntegers 1

/-- Every prime factor of `q + 1` is a prime not dividing `q`, so there is at least one such
prime as soon as `q ≥ 1`. -/
public theorem nonempty_coprimePrimes {q : ℕ} (hq : 1 ≤ q) : Nonempty (CoprimePrimes q) := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := q + 1) (by omega)
  refine ⟨⟨p, hp, fun hpq => ?_⟩⟩
  have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hpd hpq
  exact hp.ne_one (Nat.dvd_one.mp h1)

/-- The `p`-adic integers form an ultrametric space. -/
local instance isUltrametricDist_padicInt (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℤ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun _ _ =>
    PadicInt.nonarchimedean _ _

/-- The diagonal map `ℤ → Ẑ^{(q)}` is injective for `q ≥ 1`: there is a prime `ℓ ∤ q`, and
`ℤ → ℤ_ℓ` is injective. -/
public theorem intCast_injective {q : ℕ} (hq : 1 ≤ q) :
    Function.Injective (Int.cast : ℤ → RestrictedProfiniteIntegers q) := by
  obtain ⟨p⟩ := nonempty_coprimePrimes hq
  exact fun _ _ hab => Int.cast_injective (α := ℤ_[p.1]) (congrFun hab p)

/-!
### The extension `1 → Ẑ^{(q)} → Γ → Ẑ → 1`
-/

section Extension

variable {q : ℕ}
  (χ : Multiplicative ProfiniteIntegers →* (RestrictedProfiniteIntegers q)ˣ)

/-- The action of `Ẑ` on `Ẑ^{(q)}` by the powers of a unit: `z` acts as multiplication by the
unit `u^z = χ z`, where `χ` records the profinite powers of `u = χ 1`. -/
public def frobeniusAut :
    Multiplicative ProfiniteIntegers →*
      MulAut (Multiplicative (RestrictedProfiniteIntegers q)) :=
  (MulAutMultiplicative (RestrictedProfiniteIntegers q)).symm.toMonoidHom.comp
    (AddAut.mulLeft.comp χ)

/-- The element `z` of `Ẑ` acts on `Ẑ^{(q)}` as multiplication by `χ z`. -/
@[simp]
public theorem frobeniusAut_apply (z : Multiplicative ProfiniteIntegers)
    (x : RestrictedProfiniteIntegers q) :
    frobeniusAut χ z (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd ((χ z : RestrictedProfiniteIntegers q) * x) := rfl

/-- The group `Γ = Ẑ^{(q)} ⋊ Ẑ` in which `Ẑ` acts on `Ẑ^{(q)}` through the powers of the unit
`u = χ 1`. -/
public abbrev Gamma : Type :=
  Multiplicative (RestrictedProfiniteIntegers q) ⋊[frobeniusAut χ] Multiplicative ProfiniteIntegers

/-- The degree homomorphism `Γ → Ẑ`. -/
public abbrev degree : Gamma χ →* Multiplicative ProfiniteIntegers := SemidirectProduct.rightHom

/-- The inclusion of the kernel `G = Ẑ^{(q)} → Γ`. -/
public abbrev incl : Multiplicative (RestrictedProfiniteIntegers q) →* Gamma χ :=
  SemidirectProduct.inl

/-- The Frobenius element of `Γ`. -/
public def frobenius : Gamma χ :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ProfiniteIntegers))

/-- The degree homomorphism `Γ → Ẑ` is surjective. -/
public theorem degree_surjective : Function.Surjective (degree χ) :=
  SemidirectProduct.rightHom_surjective

/-- The inclusion of `G = Ẑ^{(q)}` into `Γ` is injective. -/
public theorem incl_injective : Function.Injective (incl χ) :=
  SemidirectProduct.inl_injective

/-- The image of `G = Ẑ^{(q)}` in `Γ` is the kernel of the degree homomorphism. -/
public theorem range_incl_eq_ker_degree : (incl χ).range = (degree χ).ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

/-- The Frobenius element has degree `1`. -/
@[simp]
public theorem degree_frobenius :
    degree χ (frobenius χ) = Multiplicative.ofAdd (1 : ProfiniteIntegers) :=
  SemidirectProduct.rightHom_inr _

/-- **Stacks Project, Tag 03VQ.** The extension `1 → Ẑ^{(q)} → Γ → Ẑ → 1` exhibited by the
semidirect product: conjugation by the Frobenius element is multiplication by the unit
`u = χ 1`, that is, `F x F⁻¹ = u x` for every `x` in the kernel `G = Ẑ^{(q)}`. -/
@[stacks 03VQ "the exact sequence 1 → Ẑ^{(q)} → Γ → Ẑ → 1 with F of degree 1 and F x F⁻¹ = u x,
as an extension of groups"]
public theorem frobenius_conj (x : RestrictedProfiniteIntegers q) :
    frobenius χ * incl χ (Multiplicative.ofAdd x) * (frobenius χ)⁻¹ =
      incl χ (Multiplicative.ofAdd
        ((χ (Multiplicative.ofAdd (1 : ProfiniteIntegers)) :
          RestrictedProfiniteIntegers q) * x)) := by
  rw [frobenius, ← map_inv, ← SemidirectProduct.inl_aut, frobeniusAut_apply]

/-- The topology of `Γ = Ẑ^{(q)} ⋊ Ẑ`, namely the product topology of its two factors. -/
public instance instTopologicalSpaceGamma : TopologicalSpace (Gamma χ) :=
  .induced (fun g : Gamma χ => (g.left, g.right)) inferInstance

/-- `Γ` is homeomorphic to the product of its two factors. -/
public def homeomorphProd : Gamma χ ≃ₜ
    Multiplicative (RestrictedProfiniteIntegers q) × Multiplicative ProfiniteIntegers where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom (f := fun g : Gamma χ => (g.left, g.right))
  continuous_invFun := continuous_induced_rng.mpr continuous_id

/-- The projection of `Γ` onto the factor `Ẑ^{(q)}` is continuous. -/
public theorem continuous_left : Continuous fun g : Gamma χ => g.left :=
  continuous_fst.comp (homeomorphProd χ).continuous

/-- The degree homomorphism `Γ → Ẑ` is continuous. -/
public theorem continuous_degree : Continuous (degree χ) :=
  continuous_snd.comp (homeomorphProd χ).continuous

/-- `Γ` is compact. -/
public theorem compactSpace_gamma : CompactSpace (Gamma χ) :=
  (homeomorphProd χ).symm.compactSpace

/-- `Γ` is totally disconnected. -/
public theorem totallyDisconnectedSpace_gamma : TotallyDisconnectedSpace (Gamma χ) :=
  (homeomorphProd χ).symm.totallyDisconnectedSpace

/-- **Stacks Project, Tag 03VQ.** The extension `Γ = Ẑ^{(q)} ⋊ Ẑ` is a topological group, as
soon as the powers `u^z = χ z` of the unit vary continuously with `z`. Together with
`Stacks.TraceFormula.compactSpace_gamma` and
`Stacks.TraceFormula.totallyDisconnectedSpace_gamma` this makes `Γ` profinite. -/
@[stacks 03VQ "Γ is a profinite group"]
public theorem isTopologicalGroup_gamma (hχ : Continuous χ) : IsTopologicalGroup (Gamma χ) := by
  have hv : Continuous fun z : Multiplicative ProfiniteIntegers =>
      ((χ z : (RestrictedProfiniteIntegers q)ˣ) : RestrictedProfiniteIntegers q) :=
    Units.continuous_val.comp hχ
  have hmul : ContinuousMul (Gamma χ) := by
    have hL : Continuous fun p : Gamma χ × Gamma χ => (p.1 * p.2).left :=
      continuous_ofAdd.comp
        ((continuous_toAdd.comp ((continuous_left χ).comp continuous_fst)).add
          ((hv.comp ((continuous_degree χ).comp continuous_fst)).mul
            (continuous_toAdd.comp ((continuous_left χ).comp continuous_snd))))
    have hR : Continuous fun p : Gamma χ × Gamma χ => (p.1 * p.2).right :=
      ((continuous_degree χ).comp continuous_fst).mul ((continuous_degree χ).comp continuous_snd)
    exact ⟨continuous_induced_rng.mpr (hL.prodMk hR)⟩
  have hinv : ContinuousInv (Gamma χ) := by
    have hL : Continuous fun g : Gamma χ => (g⁻¹).left :=
      continuous_ofAdd.comp
        ((hv.comp (continuous_degree χ).inv).mul
          (continuous_toAdd.comp (continuous_left χ)).neg)
    have hR : Continuous fun g : Gamma χ => (g⁻¹).right := (continuous_degree χ).inv
    exact ⟨continuous_induced_rng.mpr (hL.prodMk hR)⟩
  exact ⟨⟩

end Extension

/-!
### The congruence for the trivial coefficient modules, and the integer `qu`
-/

/-- The sum `∑_{d ∣ n} d · #S_d` of the trace formula for the trivial coefficient modules,
where `s d = #S_d`. -/
public def pointCountSum (s : ℕ → ℕ) (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d * s d

/-- For `n = 1` the sum `∑_{d ∣ n} d · #S_d` is `#S_1`. -/
@[simp]
public theorem pointCountSum_one (s : ℕ → ℕ) : pointCountSum s 1 = s 1 := by
  simp [pointCountSum]

/-- Each summand `d · #S_d` with `d ∣ n` is at most the sum `∑_{d ∣ n} d · #S_d`, for `n ≠ 0`. -/
private theorem mul_le_pointCountSum {s : ℕ → ℕ} {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    d * s d ≤ pointCountSum s n :=
  Finset.single_le_sum (f := fun e => e * s e) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨hd, hn⟩)

/-- The term `d = 1` is one of the summands, so `#S_1 ≤ ∑_{d ∣ n} d · #S_d` for `n ≠ 0`. -/
public theorem pointCountSum_one_le {s : ℕ → ℕ} {n : ℕ} (hn : n ≠ 0) :
    pointCountSum s 1 ≤ pointCountSum s n := by
  simpa using mul_le_pointCountSum (s := s) hn (one_dvd n)

/-- A vanishing sum `∑_{d ∣ n} d · #S_d` forces `S_n` to be empty. -/
public theorem eq_zero_of_pointCountSum_eq_zero {s : ℕ → ℕ} {d : ℕ} (hd : d ≠ 0)
    (h : pointCountSum s d = 0) : s d = 0 := by
  have hle := mul_le_pointCountSum (s := s) hd (dvd_refl d)
  exact (Nat.mul_eq_zero.mp (Nat.le_zero.mp (h ▸ hle))).resolve_left hd

/-- The congruence `q^n - b^n ≡ ∑_{d ∣ n} d · #S_d` modulo every power of every prime not
dividing `q`, with `s d = #S_d`. This is what an abstract trace formula for `Γ` gives on the
trivial coefficient modules `ℤ/mℤ`, with `b` the element `qu`. -/
public def IsTrivialModuleCongruence (q : ℕ) (b : RestrictedProfiniteIntegers q)
    (s : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (p : CoprimePrimes q) (k : ℕ),
    PadicInt.toZModPow k ((q : ℤ_[p.1]) ^ n - b p ^ n) =
      (pointCountSum s n : ZMod (p.1 ^ k))

/-- The integer `a = q - #S_1`, the value of `qu`. -/
public def traceParameter (q : ℕ) (s : ℕ → ℕ) : ℤ := (q : ℤ) - (s 1 : ℤ)

variable {q : ℕ} {b : RestrictedProfiniteIntegers q} {s : ℕ → ℕ}

/-- The congruence modulo all prime powers prime to `q` is an equality in `Ẑ^{(q)}`: the
`n`-th power of `qu` is the integer `q^n - ∑_{d ∣ n} d · #S_d`. -/
public theorem pow_eq_intCast (h : IsTrivialModuleCongruence q b s) {n : ℕ} (hn : 0 < n) :
    b ^ n = (((q : ℤ) ^ n - (pointCountSum s n : ℤ) : ℤ) : RestrictedProfiniteIntegers q) := by
  funext p
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  have hp := h n hn p k
  simp only [map_sub, map_pow, map_natCast] at hp
  change PadicInt.toZModPow k (b p ^ n) =
    PadicInt.toZModPow k (((q : ℤ) ^ n - (pointCountSum s n : ℤ) : ℤ) : ℤ_[p.1])
  simp only [map_pow, map_intCast]
  push_cast
  linear_combination -hp

/-- **Stacks Project, Tag 03VQ.** The congruence for the trivial coefficient modules forces
`qu` to be the ordinary integer `a = q - #S_1`. -/
@[stacks 03VQ "qu = a ∈ ℤ, with a = q - #S₁"]
public theorem eq_intCast_traceParameter (h : IsTrivialModuleCongruence q b s) :
    b = ((traceParameter q s : ℤ) : RestrictedProfiniteIntegers q) := by
  simpa [traceParameter] using pow_eq_intCast h (n := 1) Nat.one_pos

/-- The integer `a = q - #S_1` satisfies `a^n = q^n - ∑_{d ∣ n} d · #S_d` for every `n > 0`. -/
public theorem traceParameter_pow (hq : 1 ≤ q) (h : IsTrivialModuleCongruence q b s) {n : ℕ}
    (hn : 0 < n) : traceParameter q s ^ n = (q : ℤ) ^ n - (pointCountSum s n : ℤ) := by
  refine intCast_injective hq ?_
  show ((traceParameter q s ^ n : ℤ) : RestrictedProfiniteIntegers q) = _
  rw [Int.cast_pow, ← eq_intCast_traceParameter h, pow_eq_intCast h hn]

/-- The integer `a = q - #S_1` is at most `q`. -/
public theorem traceParameter_le : traceParameter q s ≤ (q : ℤ) := by
  simp only [traceParameter]
  omega

/-- The integer `a = q - #S_1` is greater than `-q`. Were it `-q`, the sum for `n = 1` would be
`2q > 0` while the sum for `n = 2` would vanish, contradicting `#S_1 ≤ ∑_{d ∣ 2} d · #S_d`. -/
public theorem neg_lt_traceParameter (hq : 1 ≤ q) (h : IsTrivialModuleCongruence q b s) :
    -(q : ℤ) < traceParameter q s := by
  by_contra! hcon
  have h2 := traceParameter_pow hq h (n := 2) (by norm_num)
  have hmono : (pointCountSum s 1 : ℤ) ≤ (pointCountSum s 2 : ℤ) :=
    mod_cast pointCountSum_one_le (s := s) (n := 2) (by norm_num)
  have hc1 : (pointCountSum s 1 : ℤ) = (q : ℤ) - traceParameter q s := by
    simp [traceParameter]
  have hq' : (1 : ℤ) ≤ (q : ℤ) := mod_cast hq
  have hpos : (0 : ℤ) ≤ ((q : ℤ) - traceParameter q s) * (-(traceParameter q s + (q : ℤ))) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The integer `a = q - #S_1` equals `q` exactly when every `S_d` with `d ≥ 1` is empty. -/
public theorem traceParameter_eq_iff (hq : 1 ≤ q) (h : IsTrivialModuleCongruence q b s) :
    traceParameter q s = (q : ℤ) ↔ ∀ d : ℕ, 0 < d → s d = 0 := by
  refine ⟨fun ha d hd => eq_zero_of_pointCountSum_eq_zero hd.ne' ?_, fun hs => ?_⟩
  · have := traceParameter_pow hq h hd
    rw [ha] at this
    exact_mod_cast (by linarith : (pointCountSum s d : ℤ) = 0)
  · simp [traceParameter, hs 1 Nat.one_pos]

/-- **Stacks Project, Tag 03VQ.** If some `S_d` is nonempty then the integer `a` with `qu = a`
satisfies `|a| < q`. -/
@[stacks 03VQ "the bound |a| < q"]
public theorem abs_traceParameter_lt (hq : 1 ≤ q) (h : IsTrivialModuleCongruence q b s)
    (hs : ∃ d : ℕ, 0 < d ∧ s d ≠ 0) : |traceParameter q s| < (q : ℤ) := by
  obtain ⟨d, hd, hsd⟩ := hs
  exact abs_lt.mpr ⟨neg_lt_traceParameter hq h,
    traceParameter_le.lt_of_ne fun hcon => hsd ((traceParameter_eq_iff hq h).mp hcon d hd)⟩

/-- **Stacks Project, Tag 03VQ.** For a unit `u` of `Ẑ^{(q)}`, the congruence
`q^n - (qu)^n ≡ ∑_{d ∣ n} d · #S_d` for the trivial coefficient modules forces `qu` to be an
integer `a` with `|a| < q`, provided some `S_d` is nonempty. -/
@[stacks 03VQ "q^n - (qu)^n ≡ ∑_{d ∣ n} d #S_d for all moduli prime to q implies qu = a ∈ ℤ with
|a| < q"]
public theorem exists_intCast_eq_and_abs_lt (hq : 1 ≤ q) (u : (RestrictedProfiniteIntegers q)ˣ)
    (s : ℕ → ℕ)
    (h : IsTrivialModuleCongruence q ((q : RestrictedProfiniteIntegers q) * u) s)
    (hs : ∃ d : ℕ, 0 < d ∧ s d ≠ 0) :
    ∃ a : ℤ, (q : RestrictedProfiniteIntegers q) * u =
      (a : RestrictedProfiniteIntegers q) ∧ |a| < (q : ℤ) :=
  ⟨traceParameter q s, eq_intCast_traceParameter h, abs_traceParameter_lt hq h hs⟩

end Stacks.TraceFormula

end
