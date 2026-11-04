module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of a hypersurface in affine space

A polynomial ring `k[ι]` over a field, with `ι` finite, is *equidimensional*: every maximal ideal
has height `#ι`, not merely height at most `#ι`.  Consequently cutting `k[ι]` by a single nonzero
nonunit always drops the Krull dimension by exactly one, and **this holds whether or not the
quotient is a domain** — the quotient of `k[x, y]` by `xy` is one-dimensional for the same reason
the quotient by `x` is.

This is the form in which the dimension theory of finite-type algebras over a field is needed for
singular plane curves.  The usual formula `dim = trdeg` is available in this repository only for a
domain (`StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField`), and the coordinate ring of a
reducible or non-reduced plane curve is not one.

## Main results

* `Stacks.MvPolynomial.ringKrullDim_mvPolynomial` — `dim k[ι] = #ι`.
* `Stacks.MvPolynomial.height_eq_natCard_of_isMaximal` — **every** maximal ideal of `k[ι]` has
  height `#ι`.
* `Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton_add_one` — `dim k[ι]/(f) + 1 = #ι`
  for every nonzero nonunit `f`, with **no hypothesis that the quotient is reduced, irreducible
  or a domain**.
* `Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton` — the same, read off as
  `dim k[ι]/(f) = n` when `#ι = n + 1`.
* `Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton_one` — the control showing the nonunit
  hypothesis is load-bearing.

## Implementation notes

Equidimensionality is not proved here: it is read off the third conjunct of the repository's
Tag 00OQ,
`MvPolynomial.isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization`,
which already asserts `ringKrullDim A = #ι` for a localization of `k[ι]` at an *arbitrary*
maximal ideal.  Translating that into a statement about heights is
`IsLocalization.AtPrime.ringKrullDim_eq_height`.

The drop-by-one step is Mathlib's `Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors`,
whose two hypotheses are exactly what the two results above supply: `f` is a non-zero-divisor
because `k[ι]` is a domain, and `f` lies in a prime of maximal height because every maximal ideal
containing `f` has height `#ι`.  Neither hypothesis mentions the quotient, which is why the
formula is insensitive to the quotient being a domain.

The hypothesis `¬ IsUnit f` cannot be dropped: for a unit `f` the quotient is the zero ring, whose
Krull dimension is `⊥`, and `⊥ + 1 = ⊥`.

## References

* [Stacks Project, Tag 00OQ](https://stacks.math.columbia.edu/tag/00OQ)
* [Stacks Project, Tag 00KW](https://stacks.math.columbia.edu/tag/00KW)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u v

namespace Stacks.MvPolynomial

variable (k : Type u) [Field k] (ι : Type v) [Finite ι]

/-- **The Krull dimension of a polynomial ring over a field in finitely many variables is the
number of variables.** -/
@[ega "IV 5.5.4" "special case"]
theorem ringKrullDim_mvPolynomial :
    ringKrullDim (MvPolynomial ι k) = (Nat.card ι : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- **`k[ι]` is equidimensional: every maximal ideal has height `#ι`.**  This is the third
conjunct of Tag 00OQ, which gives the Krull dimension of the localization at an arbitrary maximal
ideal, read as a height. -/
theorem height_eq_natCard_of_isMaximal (𝔪 : Ideal (MvPolynomial ι k)) [𝔪.IsMaximal] :
    𝔪.height = (Nat.card ι : ℕ∞) := by
  obtain ⟨-, -, hloc⟩ :=
    MvPolynomial.isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization
      k ι
  obtain ⟨-, hdim⟩ := hloc 𝔪 (Localization.AtPrime 𝔪)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (Localization.AtPrime 𝔪)] at hdim
  exact_mod_cast hdim

/-- Cancellation of `+ 1` against a positive natural number in `WithBot ℕ∞`, which is where
Krull dimensions live. -/
private theorem eq_natCast_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ}
    (h : d + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : d = (n : WithBot ℕ∞) := by
  have hbot : d ≠ ⊥ := by
    rintro rfl
    rw [WithBot.bot_add, eq_comm] at h
    simp at h
  lift d to ℕ∞ using hbot with e
  have he : e + 1 = ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  have hetop : e ≠ ⊤ := by
    rintro rfl
    rw [top_add, eq_comm] at he
    simp at he
  lift e to ℕ using hetop with m
  have hm : m + 1 = n + 1 := by exact_mod_cast he
  simp_all

/-- **Cutting a polynomial ring over a field by one nonzero nonunit drops the Krull dimension by
exactly one — with no hypothesis on the quotient.**

In particular the quotient need not be a domain, nor reduced: `k[x, y]/(xy)` and `k[x, y]/(x²)`
are both one-dimensional. -/
theorem ringKrullDim_quotient_span_singleton_add_one (f : MvPolynomial ι k) (hf0 : f ≠ 0)
    (hfu : ¬ IsUnit f) :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span {f}) + 1 = (Nat.card ι : WithBot ℕ∞) := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {f})
    (fun h => hfu (Ideal.span_singleton_eq_top.mp h))
  have := h𝔪
  rw [← ringKrullDim_mvPolynomial k ι]
  refine Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf0) (p := 𝔪) ?_ (hle (Ideal.mem_span_singleton_self f))
  rw [height_eq_natCard_of_isMaximal k ι 𝔪, ringKrullDim_mvPolynomial k ι]
  norm_cast

/-- **A hypersurface in affine `(n+1)`-space over a field has dimension `n`**, whatever its
singularities and whether or not it is reduced or irreducible. -/
theorem ringKrullDim_quotient_span_singleton {n : ℕ} (hn : Nat.card ι = n + 1)
    (f : MvPolynomial ι k) (hf0 : f ≠ 0) (hfu : ¬ IsUnit f) :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span {f}) = (n : WithBot ℕ∞) :=
  eq_natCast_of_add_one_eq
    (hn ▸ ringKrullDim_quotient_span_singleton_add_one k ι f hf0 hfu)

omit [Finite ι] in
/-- **The nonunit hypothesis of the two results above cannot be dropped**: at a unit the quotient
is the zero ring, whose Krull dimension is `⊥`, and `⊥ + 1 = ⊥`.  A predicted-failure control for
`ringKrullDim_quotient_span_singleton_add_one`, proved rather than merely expected. -/
theorem ringKrullDim_quotient_span_singleton_one :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span {(1 : MvPolynomial ι k)}) = ⊥ := by
  have : Subsingleton (MvPolynomial ι k ⧸ Ideal.span {(1 : MvPolynomial ι k)}) :=
    Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
  exact ringKrullDim_eq_bot_of_subsingleton

end Stacks.MvPolynomial

end
