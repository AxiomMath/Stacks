module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableExample

/-!
# The parameter condition of the non-algebraizable example

The family `(𝓛ₙ)` of [Stacks, Tag 0EHE] is glued along the unit

`u = 1 + t/(xy) + ∑_{m ≥ 2} aₘ tᵐ/(xy)^{φ(m)}`

and the source allows *any* `aₘ ∈ k[x,y]` and *any* `φ(m) ∈ ℕ`. This file is about where the
parameters matter, and where they do not.

**They do not matter for non-algebraizability.** The source's proof — the stalks of an
algebraizing coherent module are invertible, so it is invertible on an open `V ⊇ U ∩ Y`, so
trivial because `A = k[x,y][[t]]` is a UFD, so `𝓛₂ ≅ 𝒪_U/I²𝒪_U`, contradiction — never looks
past the first two terms of `u`: modulo `t²` the transition element is `1 + t/(xy)` for every
choice of `a` and `φ` (`Stacks.Algebraization.NonAlgebraizableExample.transitionElement_two`),
and that is already not a coboundary
(`Stacks.Algebraization.NonAlgebraizableExample.not_isUnit_of_mem_gluedSections_two`, and
`not_isTrivial_levelModule_two` for its sheaf-theoretic form). **So there is no parameter
condition to impose for the conclusion of the tag**, and none of the statements of this
development that lead to it carry one.

**They matter for the source's second proof.** The last paragraph of the example observes that
for `aₘ = 0` the limit `lim H⁰(U, 𝓛ₙ)` is nonzero — the functions `x` on `D(x)` and `x + t/y` on
`D(y)` glue at every order
(`Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit_ne_bot`) — whereas for `aₘ = 1`
and `φ(m) = 2ᵐ`, or `φ(m) = m²`, it vanishes, "which gives another proof that `(𝓛ₙ)` is not
algebraizable in this case". That is the one place a condition on `a` and `φ` is used, and
`Stacks.Algebraization.NonAlgebraizableExample.IsVanishingSectionsParameter` is it, abstracted
away from the two prescriptions to what the argument actually consumes: the coefficients are all
`1`, and the exponents separate degrees
(`Stacks.Algebraization.NonAlgebraizableExample.HasSeparatedExponents`).

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.IsVanishingSectionsParameter` — **the parameter
  condition**: `aₘ = 1` for `m ≥ 2`, and `φ` separates degrees.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.isVanishingSectionsParameter_two_pow` and
  `…_sq` — the source's two prescriptions satisfy the condition.
* `Stacks.Algebraization.NonAlgebraizableExample.not_isVanishingSectionsParameter_of_eq_zero` —
  the degenerate choice `aₘ = 0` does not, as it must not: for it the limit of global sections
  is nonzero.
* `sectionsLimit_eq_bot_of_isVanishingSectionsParameter`, in the same namespace — under the
  condition the limit `lim H⁰(U, 𝓛ₙ)` vanishes.
* `Stacks.Algebraization.NonAlgebraizableExample.not_exists_compatible_isUnit_mem_gluedSections`
  — under the condition the system `(𝓛ₙ)` admits no compatible system of trivializing sections:
  a compatible system of glued pairs whose `D(x̄)`-components are invertible would be a nonzero
  element of the limit.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- **The parameter condition of [Stacks, Tag 0EHE], second paragraph.** Every higher
coefficient `aₘ` is `1` and the exponents `φ(m)` separate degrees. This is the hypothesis under
which the limit `lim H⁰(U, 𝓛ₙ)` of global sections vanishes, which is the source's second proof
that `(𝓛ₙ)` is not algebraizable.

It is **not** a hypothesis of the source's first proof, nor of the conclusion of the tag: the
family is non-algebraizable for every choice of `a` and `φ`, the obstruction being already
visible modulo `t²`. -/
public def IsVanishingSectionsParameter (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) : Prop :=
  (∀ m : ℕ, 2 ≤ m → a m = 1) ∧ HasSeparatedExponents φ

/-- **Stacks Project, Tag 0EHE (the first prescribed choice).** The coefficients `aₘ = 1` and
the exponents `φ(m) = 2ᵐ` satisfy the parameter condition. -/
@[stacks 0EHE "a_m = 1 and φ(m) = 2^m satisfy the parameter condition"]
public theorem isVanishingSectionsParameter_two_pow {a : ℕ → PlaneRing k} {φ : ℕ → ℕ}
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1) (hφ : ∀ m : ℕ, 2 ≤ m → φ m = 2 ^ m) :
    IsVanishingSectionsParameter k a φ :=
  ⟨ha, hasSeparatedExponents_of_eq_two_pow_or_sq (Or.inl hφ)⟩

/-- **Stacks Project, Tag 0EHE (the second prescribed choice).** The coefficients `aₘ = 1` and
the exponents `φ(m) = m²` satisfy the parameter condition. -/
@[stacks 0EHE "a_m = 1 and φ(m) = m^2 satisfy the parameter condition"]
public theorem isVanishingSectionsParameter_sq {a : ℕ → PlaneRing k} {φ : ℕ → ℕ}
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 1) (hφ : ∀ m : ℕ, 2 ≤ m → φ m = m ^ 2) :
    IsVanishingSectionsParameter k a φ :=
  ⟨ha, hasSeparatedExponents_of_eq_two_pow_or_sq (Or.inr hφ)⟩

/-- The degenerate choice `aₘ = 0` of the source's last paragraph does **not** satisfy the
parameter condition, as it cannot: for it the limit of global sections is nonzero
(`sectionsLimit_ne_bot`), so no condition implying the vanishing of that limit can hold. -/
public theorem not_isVanishingSectionsParameter_of_eq_zero (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (ha : ∀ m : ℕ, 2 ≤ m → a m = 0) : ¬ IsVanishingSectionsParameter k a φ := by
  rintro ⟨h1, -⟩
  exact one_ne_zero ((h1 2 le_rfl).symm.trans (ha 2 le_rfl))

/-- **Stacks Project, Tag 0EHE (the vanishing of the limit of global sections).** Under the
parameter condition the limit `lim H⁰(U, 𝓛ₙ)` is zero. -/
@[stacks 0EHE "lim H^0(U, L_n) = 0 under the parameter condition"]
public theorem sectionsLimit_eq_bot_of_isVanishingSectionsParameter (a : ℕ → PlaneRing k)
    (φ : ℕ → ℕ) (h : IsVanishingSectionsParameter k a φ) : sectionsLimit k a φ = ⊥ :=
  sectionsLimit_eq_bot_of_hasSeparatedExponents k a φ h.1 h.2

/-- **Stacks Project, Tag 0EHE (no compatible trivializing sections under the parameter
condition).** A trivialization of the glued module `𝓛ₙ` is a pair of invertible chart functions
matched by the transition element, so a *compatible system* of trivializations of the whole
family would be a system of glued pairs, compatible with reduction modulo `tⁿ`, whose
`D(x̄)`-components are invertible. Under the parameter condition no such system exists: it would
be a nonzero element of `lim H⁰(U, 𝓛ₙ)`, which vanishes. This is the content of the source's
second proof of non-algebraizability. -/
@[stacks 0EHE "under the parameter condition (L_n) has no compatible trivializing sections"]
public theorem not_exists_compatible_isUnit_mem_gluedSections (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (h : IsVanishingSectionsParameter k a φ) :
    ¬ ∃ s : (n : ℕ) → chartRing k (xVar k) n × chartRing k (yVar k) n,
      (∀ n : ℕ, s n ∈ gluedSections k n (transitionElement k a φ n)) ∧
      (∀ n : ℕ, (chartReduction k (xVar k) n (s (n + 1)).1,
        chartReduction k (yVar k) n (s (n + 1)).2) = s n) ∧
      ∀ n : ℕ, 0 < n → IsUnit (s n).1 := by
  rintro ⟨s, hs, hred, hunit⟩
  have hzero : s 1 = 0 :=
    eq_zero_of_compatible_mem_gluedSections k a φ h.1 h.2 s hs hred 1
  have h1 : (s 1).1 = 0 := by rw [hzero]; rfl
  have := nontrivial_chartRing_xVar k 1 Nat.one_pos
  exact one_ne_zero (isUnit_zero_iff.mp (h1 ▸ hunit 1 Nat.one_pos)).symm

end Stacks.Algebraization.NonAlgebraizableExample

end
