module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksCore.Tactic.StacksAttribute

/-! # Iterating a degree `-2` derivation on divided powers

This is the engine of Gulliksen's argument for Stacks Tag 09PU. Let `θ` be a derivation of
degree `-2` on a graded divided-power algebra, let `ξ` be a positive even element and put
`y = θ ξ`. If `θ y = 0`, then `θ` applied `n` times to the `n`-th divided power of `ξ` is `yⁿ`:

`θ^[n] (γ.dpow n ξ) = y ^ n`.

The point is that each application of `θ` consumes one divided power and emits one factor of
`y`, by the divided-power Leibniz rule `θ (γ_n x) = θ x · γ_{n-1} x`; the hypothesis `θ y = 0`
is what lets the accumulated factors of `y` be carried past the remaining applications of `θ`.
Consequently, if `y` is not nilpotent then no divided power of `ξ` vanishes
(`dpow_ne_zero_of_not_isNilpotent`) — which is how a non-nilpotent `g` in Tag 09PU forces
`Tor` to be nonzero in every even degree.

Tag 09PU needs this both for a genuine derivation on an algebra and for the quotient
`A/IA`, where `θ` is only a derivation "up to lifts": the identity `θ (xz) = θ(x) z + x θ(z)`
holds for *some* representatives of `θ x` and `θ z`, because `A` need not be commutative and
`IA` need not be two-sided. `iterate_derivation_dpow_quotient` is that version.

The last two results concern the square of a lifted differential. On `𝒜 2` the operator `d ∘ d`
satisfies the divided-power Leibniz rule `d²(γ_n x) = d²(x) · γ_{n-1} x`
(`differential_sq_dpow`), which is what identifies `θ` as a derivation of degree `-2`: the two
Koszul signs cancel, and the cross term dies because `d x` has odd degree and so square zero.

## Main results

* `iterate_derivation_dpow`, `iterate_derivation_dpow_quotient` — `θ^[n] (γ_n ξ) = yⁿ`.
* `dpow_ne_zero_of_not_isNilpotent` — no divided power of `ξ` vanishes.
* `differential_sq_dpow` — `d²` obeys the divided-power Leibniz rule on `𝒜 2`.

## References

* [Stacks Project, Tag 09PU](https://stacks.math.columbia.edu/tag/09PU)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

universe u v w z

/-- A non-nilpotent element has no vanishing power. -/
public theorem pow_ne_zero_of_not_isNilpotent
    {A : Type u} [MonoidWithZero A] {x : A}
    (hnil : ¬ IsNilpotent x) (n : ℕ) : x ^ n ≠ 0 :=
  fun hzero => hnil ⟨n, hzero⟩

/-- `I • ⊤` absorbs multiplication on the right. Although `I • (⊤ : Submodule R A)` is only a
submodule, it behaves as a two-sided ideal of `A` because the scalars are central. -/
public theorem mul_mem_smul_top_right
    {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (I : Ideal R) {x z : A} (hx : x ∈ I • (⊤ : Submodule R A)) :
    x * z ∈ I • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr a _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro a b ha hb
    rw [add_mul]
    exact add_mem ha hb

/-- `I • ⊤` absorbs multiplication on the left. -/
public theorem mul_mem_smul_top_left
    {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (I : Ideal R) {x z : A} (hx : x ∈ I • (⊤ : Submodule R A)) :
    z * x ∈ I • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr a _
    rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro a b ha hb
    rw [mul_add]
    exact add_mem ha hb

/-- A surjection of graded algebras that preserves degrees admits homogeneous preimages: project
a preimage onto the relevant degree, which the graded ring hom `map_directSumDecompose` shows is
still a preimage. -/
public theorem exists_mem_grade_map_eq
    {R' : Type v} {R : Type u} {B : Type w} {A : Type z}
    [CommRing R'] [CommRing R] [Ring B] [Ring A]
    [Algebra R' B] [Algebra R A]
    {𝒜 : ℕ → Submodule R' B} {ℬ : ℕ → Submodule R A}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (π : B →+* A) (hπ : Function.Surjective π)
    (hgrade : ∀ n b, b ∈ 𝒜 n → π b ∈ ℬ n)
    {n : ℕ} {x : A} (hx : x ∈ ℬ n) :
    ∃ b : B, b ∈ 𝒜 n ∧ π b = x := by
  obtain ⟨b, rfl⟩ := hπ x
  refine ⟨GradedAlgebra.proj 𝒜 n b, (DirectSum.decompose 𝒜 b n).property, ?_⟩
  let f : 𝒜 →+*ᵍ ℬ := ⟨π, fun {i b} hb => hgrade i b hb⟩
  rw [GradedAlgebra.proj_apply]
  change f (DirectSum.decompose 𝒜 b n) = f b
  rw [f.map_directSumDecompose (x := b) (i := n),
    DirectSum.decompose_of_mem ℬ (show f b ∈ ℬ n from hx)]
  simp

/-- **Gulliksen's computation.** For a derivation `θ` on a commutative graded divided-power
algebra, a positive even `ξ` with `y = θ ξ` and `θ y = 0`, the `n`-fold iterate of `θ` sends the
`n`-th divided power of `ξ` to `yⁿ`. Each application of `θ` consumes one divided power and
emits a factor of `y`, and `θ y = 0` lets those factors be carried past later applications. -/
public theorem iterate_derivation_dpow
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (θ : A →ₗ[R] A)
    (hderiv : ∀ x y : A, θ (x * y) = θ x * y + x * θ y)
    {ξ y : A} (hξ : θ ξ = y) (hy : θ y = 0)
    (hdpow : ∀ {n : ℕ}, n ≠ 0 → ξ ∈ positiveEvenPart 𝒜 →
      θ (γ.dpow n ξ) = θ ξ * γ.dpow (n - 1) ξ)
    (hξpos : ξ ∈ positiveEvenPart 𝒜) (n : ℕ) :
    θ^[n] (γ.dpow n ξ) = y ^ n := by
  have hiter (k : ℕ) (z : A) : θ^[k] (y * z) = y * θ^[k] z := by
    induction k generalizing z with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hderiv, hy, zero_mul,
        zero_add, ih (θ z)]
  induction n with
  | zero => simp [γ.dpow_zero hξpos]
  | succ n ih =>
    calc
      θ^[n + 1] (γ.dpow (n + 1) ξ) = θ^[n] (θ (γ.dpow (n + 1) ξ)) := by
            rw [Function.iterate_succ_apply]
      _ = θ^[n] (y * γ.dpow n ξ) := by
            rw [hdpow (by omega) hξpos, hξ]
            simp
      _ = y * θ^[n] (γ.dpow n ξ) := hiter n _
      _ = y * y ^ n := by rw [ih]
      _ = y ^ (n + 1) := (pow_succ' y n).symm

/-- If `y = θ ξ` is not nilpotent then no divided power of `ξ` vanishes: applying `θ` the right
number of times to a vanishing divided power would make a power of `y` vanish. -/
public theorem dpow_ne_zero_of_not_isNilpotent
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (θ : A →ₗ[R] A)
    (hderiv : ∀ x y : A, θ (x * y) = θ x * y + x * θ y)
    {ξ y : A} (hξ : θ ξ = y) (hy : θ y = 0)
    (hdpow : ∀ {n : ℕ}, n ≠ 0 → ξ ∈ positiveEvenPart 𝒜 →
      θ (γ.dpow n ξ) = θ ξ * γ.dpow (n - 1) ξ)
    (hξpos : ξ ∈ positiveEvenPart 𝒜) (hnil : ¬ IsNilpotent y)
    (n : ℕ) : γ.dpow n ξ ≠ 0 := by
  intro hzero
  refine pow_ne_zero_of_not_isNilpotent hnil n ?_
  simpa [hzero] using (iterate_derivation_dpow 𝒜 γ θ hderiv hξ hy hdpow hξpos n).symm

/-- The version of `iterate_derivation_dpow` for a derivation on a quotient `A ⧸ J`, where the
Leibniz rule is only available through lifts of the values of `θ`. This is the form Tag 09PU
needs: `A` is graded-commutative rather than commutative and `J = I • ⊤` need not be a
two-sided ideal, so `θ` cannot be presented as a derivation of a ring. The relation `θ ξ = y`
is not assumed separately, being the case `n = 1` of `hdpow`. -/
public theorem iterate_derivation_dpow_quotient
    {R : Type v} {A : Type z} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜)
    (J : Submodule R A) (θ : (A ⧸ J) →ₗ[R] (A ⧸ J))
    (hderiv : ∀ x z : A, ∃ a b : A,
      θ (Submodule.Quotient.mk (R := R) x) = Submodule.Quotient.mk (R := R) a ∧
      θ (Submodule.Quotient.mk (R := R) z) = Submodule.Quotient.mk (R := R) b ∧
      θ (Submodule.Quotient.mk (R := R) (x * z)) =
        Submodule.Quotient.mk (R := R) (a * z + x * b))
    (hJmul : ∀ {x z : A}, x ∈ J → x * z ∈ J)
    (hJmulLeft : ∀ {x z : A}, x ∈ J → z * x ∈ J)
    {ξ y : A}
    (hθy : θ (Submodule.Quotient.mk (R := R) (p := J) y) = 0)
    (hξpos : ξ ∈ positiveEvenPart 𝒜)
    (hdpow : ∀ {n : ℕ}, n ≠ 0 →
      θ (Submodule.Quotient.mk (R := R) (p := J) (γ.dpow n ξ)) =
        Submodule.Quotient.mk (R := R) (p := J) (y * γ.dpow (n - 1) ξ))
    (n : ℕ) :
    θ^[n] (Submodule.Quotient.mk (R := R) (p := J) (γ.dpow n ξ)) =
      Submodule.Quotient.mk (R := R) (p := J) (y ^ n) := by
  have hiter (k : ℕ) (z w : A)
      (hz : θ^[k] (Submodule.Quotient.mk (R := R) (p := J) z) =
        Submodule.Quotient.mk (R := R) (p := J) w) :
      θ^[k] (Submodule.Quotient.mk (R := R) (p := J) (y * z)) =
        Submodule.Quotient.mk (R := R) (p := J) (y * w) := by
    induction k generalizing z w with
    | zero =>
        apply (Submodule.Quotient.eq (R := R) (M := A) J).2
        rw [← mul_sub]
        exact hJmulLeft ((Submodule.Quotient.eq (R := R) (M := A) J).mp hz)
    | succ k ih =>
        obtain ⟨a, b, ha, hb, hab⟩ := hderiv y z
        have hya : a ∈ J := by
          apply (Submodule.Quotient.mk_eq_zero (R := R) (M := A) J).mp
          rw [← ha, hθy]
        have hcancel : Submodule.Quotient.mk (R := R) (p := J) (a * z + y * b) =
            Submodule.Quotient.mk (R := R) (p := J) (y * b) := by
          apply (Submodule.Quotient.eq (R := R) (M := A) J).2
          simpa using hJmul hya
        rw [Function.iterate_succ_apply, hab, hcancel]
        exact ih b w (by rwa [Function.iterate_succ_apply, hb] at hz)
  induction n with
  | zero => simp [γ.dpow_zero hξpos]
  | succ n ih =>
      rw [Function.iterate_succ_apply, hdpow (by omega), pow_succ']
      exact hiter n _ _ ih

/-- Iterating a derivation of the quotient on a boundary yields a boundary, provided one
application does. -/
public theorem iterate_derivation_differential_quotient
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (J : Submodule R A) (θ : A ⧸ J →ₗ[R] A ⧸ J)
    (d : A →ₗ[R] A)
    (hbound : ∀ z : A, ∃ w : A,
      θ (Submodule.Quotient.mk (p := J) (d z)) =
        Submodule.Quotient.mk (p := J) (d w))
    (n : ℕ) (z : A) :
    ∃ w : A, θ^[n] (Submodule.Quotient.mk (p := J) (d z)) =
      Submodule.Quotient.mk (p := J) (d w) := by
  induction n generalizing z with
  | zero => exact ⟨z, rfl⟩
  | succ n ih =>
      obtain ⟨w, hw⟩ := hbound z
      obtain ⟨w', hw'⟩ := ih w
      exact ⟨w', by rwa [Function.iterate_succ_apply, hw]⟩

/-- `d ∘ d` obeys the divided-power Leibniz rule on `𝒜 2`, stated over the three rules a
differential graded divided-power algebra supplies rather than over the classes, so that it
applies to a *lifted* differential whose square need not vanish. Applying the rule twice
produces a cross term `d x · (d x · γ_{n-2} x)`, which vanishes because `d x` lies in `𝒜 1` and
odd-degree elements have square zero; the two Koszul signs are both `(-1)¹` and cancel. -/
public theorem differential_sq_dpow_of_rules
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A)
    (hdmem : ∀ {i : ℕ} {x : A}, x ∈ 𝒜 (i + 1) → d x ∈ 𝒜 i)
    (hleibniz : ∀ {i j : ℕ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y))
    (hdpow : ∀ {k : ℕ} {x : A}, k ≠ 0 → x ∈ positiveEvenPart 𝒜 →
      d (γ.dpow k x) = d x * γ.dpow (k - 1) x)
    {x : A} (hx : x ∈ 𝒜 2) (n : ℕ) (hn : n ≠ 0) :
    d (d (γ.dpow n x)) = d (d x) * γ.dpow (n - 1) x := by
  have hxpos : x ∈ positiveEvenPart 𝒜 := by
    rw [positiveEvenPart]
    exact Submodule.mem_iSup_of_mem 0 (by simpa using hx)
  have hdx : d x ∈ 𝒜 1 := hdmem (by simpa using hx)
  have hpow (k : ℕ) (hk : k ≠ 0) : γ.dpow k x ∈ 𝒜 (2 * k) := by
    simpa using γ.dpow_mem_grade (d := 1) hk hxpos hx
  have hodd : (d x) ^ 2 = 0 := IsStrictlyGradedComm.odd_sq_zero (d := 0) hdx
  by_cases h1 : n = 1
  · subst n
    simp [γ.dpow_one hxpos, γ.dpow_zero hxpos]
  · rw [hdpow hn hxpos, hleibniz hdx (hpow (n - 1) (by omega)),
      hdpow (k := n - 1) (by omega) hxpos, ← mul_assoc, ← pow_two, hodd]
    simp

/-- `differential_sq_dpow_of_rules` for an honest differential graded divided-power algebra.
Note that `d ∘ d` is zero in that case, so the content is in the `of_rules` version, which is
what the lifted differential of Tag 09PS satisfies. -/
public theorem differential_sq_dpow
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (d : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 d] [IsCompatibleWithDifferential γ d]
    {x : A} (hx : x ∈ 𝒜 2) (n : ℕ) (hn : n ≠ 0) :
    d (d (γ.dpow n x)) = d (d x) * γ.dpow (n - 1) x :=
  differential_sq_dpow_of_rules 𝒜 γ d
    (fun hx => IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) hx)
    (fun hx hy => IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) hx hy)
    (fun hk hx => IsCompatibleWithDifferential.d_dpow (γ := γ) (d := d) hk hx)
    hx n hn

end DividedPowers.TateResolution

end
