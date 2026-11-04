module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DifferentialLift

/-!
# Extending a differential along a set-variable divided-power extension

Let `A` be a strictly graded-commutative nonnegatively graded algebra with divided powers `γ`
carrying a differential `d`, and let `C` be obtained from `A` by adjoining a family of
homogeneous variables `T j` of positive degrees, freely as a graded algebra with divided powers.
This file shows that `d` extends to a differential on `C` taking an arbitrary prescribed value
of degree `deg j - 1` on each variable `T j`.

This is the inductive step of the Tate resolution tower of
[Stacks, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN): each stage of the tower adjoins
variables of one degree whose differentials are prescribed cycles of the previous stage, and the
differential of the new stage has to restrict to the old one.

## Main results

* `DividedPowers.TateResolution.exists_differential_setVariableExtension` — the differential of
  `C` restricting to `d` on `A` and taking prescribed values on the variables.

## Implementation notes

The construction is the one of
`DividedPowers.TateResolution.exists_differential_gradedDividedPowerPolynomial`, with the
coefficient algebra no longer required to sit in degree zero with zero differential. A
degree-lowering map obeying the two Leibniz rules is the same thing as a grading- and
divided-power-preserving algebra map `x ↦ x + σ(D x) T` into the odd-variable extension by one
variable `T` of degree one, and the universal property of a set-variable extension produces such
a map from a coefficient map and an image for each variable. The coefficient map is now
`a ↦ a + σ(d a) T` rather than the plain inclusion: it is `exists_oddExtAlgHom_of_differential`
for `d`, pushed into the odd-variable extension of `C` by the functoriality
`exists_oddExtMap` of that extension. This is why the universal property is needed in its
*graded* form, taking a coefficient map that preserves every homogeneous piece, rather than in
the degree-zero form `existsUnique_gradedDividedPowerPolynomial_map`.

The universal property is a hypothesis rather than an instance of
`exists_setVariableDividedPowerExtension`, in exactly the shape that theorem's
conclusion provides it. Stating it that way keeps the proof independent of the packaging of the
construction, and lets it be used for a stage of the tower presented in any other way.

Squareness of the differential is not asserted: `D ∘ D` vanishes on the coefficients and on the
variables as soon as `d ∘ d = 0` and each prescribed value is a cycle, but concluding `D ∘ D = 0`
from that needs the separate fact that a degree `-2` derivation vanishing on the coefficients and
the variables is zero. As in
`DividedPowers.TateResolution.exists_differential_gradedDividedPowerPolynomial`, the conclusion
therefore lists the differential graded algebra axioms individually rather than using
`IsDifferentialGradedAlgebra`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w t

section SetVariable

variable {R : Type u} {A : Type v} {C : Type w} {J : Type t}
  [CommRing R] [Ring A] [Algebra R A] [Ring C] [Algebra R C]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜)
  (𝒞 : ℕ → Submodule R C) [GradedAlgebra 𝒞] [IsStrictlyGradedComm 𝒞]
  (δ : DividedPowerStructure 𝒞)

/-- **A differential extends along a set-variable divided-power extension, with arbitrary
prescribed values on the variables.** -/
public theorem exists_differential_setVariableExtension
    (ι : A →ₐ[R] C)
    (hιgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → ι a ∈ 𝒞 n)
    (hιdpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 →
      ι (γ.dpow n a) = δ.dpow n (ι a))
    (d : A →ₗ[R] A)
    (hd0 : ∀ a : A, a ∈ 𝒜 0 → d a = 0)
    (hdgrade : ∀ (n : ℕ) (a : A), a ∈ 𝒜 (n + 1) → d a ∈ 𝒜 n)
    (hdleibniz : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
      d (x * y) = d x * y + (-1 : R) ^ i • (x * d y))
    (hddpow : ∀ (n : ℕ) (a : A), n ≠ 0 → a ∈ positiveEvenPart 𝒜 →
      d (γ.dpow n a) = d a * γ.dpow (n - 1) a)
    (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (T : J → C) (hT : ∀ j, T j ∈ 𝒞 (deg j))
    (z : J → C) (hz : ∀ j, z j ∈ 𝒞 (deg j - 1))
    (huniv : ∀ {D : Type w} [Ring D] [Algebra R D]
      (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ]
      [IsStrictlyGradedComm Dᵢ] (ε : DividedPowerStructure Dᵢ)
      (f : A →ₐ[R] D) (s : J → D),
      (∀ (m : ℕ) (a : A), a ∈ 𝒜 m → f a ∈ Dᵢ m) →
      (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 →
        ε.dpow n (f a) = f (γ.dpow n a)) →
      (∀ j : J, s j ∈ Dᵢ (deg j)) →
      ∃! g : C →ₐ[R] D,
        (∀ a : A, g (ι a) = f a) ∧
        (∀ j : J, g (T j) = s j) ∧
        (∀ (m : ℕ) (x : C), x ∈ 𝒞 m → g x ∈ Dᵢ m) ∧
        (∀ (n : ℕ) (x : C), x ∈ positiveEvenPart 𝒞 →
          ε.dpow n (g x) = g (δ.dpow n x))) :
    ∃ D : C →ₗ[R] C,
      (∀ a : A, D (ι a) = ι (d a)) ∧
      (∀ j : J, D (T j) = z j) ∧
      (∀ x : C, x ∈ 𝒞 0 → D x = 0) ∧
      (∀ (n : ℕ) (x : C), x ∈ 𝒞 (n + 1) → D x ∈ 𝒞 n) ∧
      (∀ (i j : ℕ) (x y : C), x ∈ 𝒞 i → y ∈ 𝒞 j →
        D (x * y) = D x * y + (-1 : R) ^ i • (x * D y)) ∧
      (∀ (n : ℕ) (x : C), n ≠ 0 → x ∈ positiveEvenPart 𝒞 →
        D (δ.dpow n x) = D x * δ.dpow (n - 1) x) := by
  classical
  have hσinv : ∀ x : C, signRingEquiv 𝒞 1 (signRingEquiv 𝒞 1 x) = x :=
    signRingEquiv_signRingEquiv 𝒞 1
  have hσmem : ∀ (m : ℕ) (x : C), x ∈ 𝒞 m → signRingEquiv 𝒞 1 x ∈ 𝒞 m :=
    fun m _ hx => signRingEquiv_mem_grade 𝒞 1 hx
  -- the differential of `A`, as an algebra map into the odd-variable extension of `A`
  obtain ⟨Φ, hΦ, hΦgrade, hΦdpow⟩ :=
    exists_oddExtAlgHom_of_differential 𝒜 γ d hd0 hdgrade hdleibniz hddpow
  -- pushed into the odd-variable extension of `C`
  obtain ⟨ρ, hρ, hρgrade, hρdpow⟩ :=
    exists_oddExtMap (𝒜 := 𝒞) (ℬ := 𝒜) (γ := δ) (δ := γ) (φ := ι) hιgrade hιdpow
  have hf : ∀ a : A, (ρ.comp Φ) a = oddExtPair 𝒞 (ι a) (signRingEquiv 𝒞 1 (ι (d a))) := by
    intro a
    rw [AlgHom.comp_apply, hΦ a, hρ, map_signRingEquiv 𝒞 𝒜 ι hιgrade 1 (d a)]
  have hfgrade : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m →
      (ρ.comp Φ) a ∈ OddVariableExtension.grade 𝒞 1 m :=
    fun m a ha => hρgrade m (Φ a) (hΦgrade m a ha)
  have hfdpow : ∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 →
      (oddVariableDividedPowerStructure 𝒞 δ 1 Nat.one_pos odd_one).dpow n ((ρ.comp Φ) a) =
        (ρ.comp Φ) (γ.dpow n a) := by
    intro n a ha
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hΦdpow n a ha,
      hρdpow n (Φ a) (algHom_mem_positiveEvenPart 𝒜 (OddVariableExtension.grade 𝒜 1) Φ
        hΦgrade ha)]
  -- the prescribed images of the variables
  have htgrade : ∀ j : J, oddExtPair 𝒞 (T j) (signRingEquiv 𝒞 1 (z j)) ∈
      OddVariableExtension.grade 𝒞 1 (deg j) := by
    intro j
    obtain ⟨e, he⟩ : ∃ e, deg j = e + 1 := ⟨deg j - 1, by have := hdeg j; omega⟩
    have hTj : T j ∈ 𝒞 (e + 1) := by rw [← he]; exact hT j
    have hzj : z j ∈ 𝒞 e := by
      have h := hz j
      rwa [he, Nat.add_sub_cancel] at h
    rw [he]
    exact oddExtPair_mem_grade_succ 𝒞 hTj (hσmem e (z j) hzj)
  obtain ⟨g, ⟨hgι, hgT, hggrade, hgdpow⟩, -⟩ :=
    huniv (OddVariableExtension.grade 𝒞 1)
      (oddVariableDividedPowerStructure 𝒞 δ 1 Nat.one_pos odd_one) (ρ.comp Φ)
      (fun j => oddExtPair 𝒞 (T j) (signRingEquiv 𝒞 1 (z j))) hfgrade hfdpow htgrade
  -- the first coefficient of `g` is the identity, by uniqueness
  have hfst : ∀ x : C, (OddVariableExtension.coefficients 𝒞 1 (g x)).1 = x := by
    obtain ⟨gid, -, hu⟩ := huniv 𝒞 δ ι T hιgrade (fun n a ha => (hιdpow n a ha).symm) hT
    have h1 : (oddExtFst 𝒞).comp g = AlgHom.id R C := by
      refine (hu _ ?_).trans (hu _ ?_).symm
      · refine ⟨fun a => ?_, fun j => ?_, fun m x hx => ?_, fun n x hx => ?_⟩
        · show (OddVariableExtension.coefficients 𝒞 1 (g (ι a))).1 = ι a
          rw [hgι a, hf a, coefficients_oddExtPair]
        · show (OddVariableExtension.coefficients 𝒞 1 (g (T j))).1 = T j
          rw [hgT j, coefficients_oddExtPair]
        · show (OddVariableExtension.coefficients 𝒞 1 (g x)).1 ∈ 𝒞 m
          exact ((OddVariableExtension.mem_grade_coefficients_iff 𝒞 1 m (g x)).mp
            (hggrade m x hx)).1
        · show δ.dpow n (OddVariableExtension.coefficients 𝒞 1 (g x)).1 =
            (OddVariableExtension.coefficients 𝒞 1 (g (δ.dpow n x))).1
          rw [← hgdpow n x hx]
          exact (oddExtFst_dpow 𝒞 δ n
            (algHom_mem_positiveEvenPart 𝒞 (OddVariableExtension.grade 𝒞 1) g hggrade hx)).symm
      · exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ hx => hx, fun _ _ _ => rfl⟩
    intro x
    exact congrArg (fun k : C →ₐ[R] C => k x) h1
  -- the second coefficient, twisted by the grading sign, is the differential
  set D : C →ₗ[R] C := (signLinearMap 𝒞 1).comp ((LinearMap.snd R C C).comp
    ((OddVariableExtension.coefficients 𝒞 1).toLinearMap.comp g.toLinearMap))
  have hDapp : ∀ x : C,
      D x = signRingEquiv 𝒞 1 (OddVariableExtension.coefficients 𝒞 1 (g x)).2 := fun _ => rfl
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hDapp, hgι a, hf a, coefficients_oddExtPair, hσinv]
  · intro j
    rw [hDapp, hgT j, coefficients_oddExtPair, hσinv]
  · intro x hx
    have hmem := ((OddVariableExtension.mem_grade_coefficients_iff 𝒞 1 0 (g x)).mp
      (hggrade 0 x hx)).2
    rw [ite_eq_right (by omega : ¬ (1 : ℕ) ≤ 0), Submodule.mem_bot] at hmem
    rw [hDapp, hmem]
    simp
  · intro n x hx
    have hmem := ((OddVariableExtension.mem_grade_coefficients_iff 𝒞 1 (n + 1) (g x)).mp
      (hggrade (n + 1) x hx)).2
    rw [ite_eq_left (by omega : (1 : ℕ) ≤ n + 1), Nat.add_sub_cancel] at hmem
    rw [hDapp]
    exact hσmem n _ hmem
  · intro i _ x y hx _
    rw [hDapp, hDapp, hDapp, map_mul, OddVariableExtension.coefficients_mul, hfst x, hfst y,
      map_add, map_mul, map_mul, hσinv, signRingEquiv_of_mem 𝒞 1 i hx, one_mul, smul_mul_assoc,
      add_comm]
  · intro n x hn hx
    have hgx : g x ∈ positiveEvenPart (OddVariableExtension.grade 𝒞 1) :=
      algHom_mem_positiveEvenPart 𝒞 (OddVariableExtension.grade 𝒞 1) g hggrade hx
    have heven : δ.dpow (n - 1) x ∈ evenPart 𝒞 := by
      rcases Nat.eq_zero_or_pos (n - 1) with hzero | hp
      · rw [hzero, δ.dpow_zero hx]
        exact Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded 𝒞)
      · exact positiveEvenPart_le_evenPart 𝒞 (δ.dpow_mem (by omega) hx)
    rw [hDapp, hDapp, ← hgdpow n x hx, coefficients_dpow 𝒞 δ n hn hgx, hfst x, map_mul,
      signRingEquiv_one_of_mem_evenPart 𝒞 heven, mul_comm_of_mem_evenPart 𝒞 heven]

end SetVariable

end DividedPowers.TateResolution

end
