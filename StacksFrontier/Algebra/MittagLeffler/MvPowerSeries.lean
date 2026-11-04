module

import StacksFrontier.Algebra.MittagLeffler.Pi
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Module.FinitePresentation


@[expose] public section

universe u v

/-!
# Power series over a Noetherian ring are flat and Mittag-Leffler

Let `R` be a Noetherian ring. This file states that the power series ring `M = R[[t_1, …, t_n]]`,
regarded as an `R`-module, is flat and Mittag-Leffler.

The mechanism is a single observation about the underlying module: a power series in `t_1, …, t_n`
is a family of coefficients indexed by the monomials, so as an `R`-module `M` is the product `R^A`
over the countable set `A` of monomials in `n` variables. Both conclusions are then the case
`A = ` monomials of Lemma 05D0, which is Chase's theorem for flatness (a Noetherian ring is
coherent, and over a coherent ring a product of flat modules is flat) together with Lemma 059S for
the Mittag-Leffler condition (over a Noetherian ring the submodule of a finite free `F` generated
by the coordinates of `x ∈ F ⊗[R] R^A` is the smallest one whose tensor product carries `x`).

Neither conclusion is formal: for `n ≥ 1` the module `M` is a countably infinite product of copies
of `R`, so it is neither free nor projective in general — over `R = ℤ` the module `ℤ[[t]] = ℤ^ℕ`
is not free, by the Baer–Specker theorem — and both conclusions fail for suitable non-coherent `R`.

## Main results

* `Module.flat_and_mittagLeffler_mvPowerSeries`: for a Noetherian ring `R` and any number of
  variables, the `R`-module `R[[t_1, …, t_n]]` is flat and Mittag-Leffler.

## Implementation notes

`R[[t_1, …, t_n]]` is `MvPowerSeries (Fin n) R`, whose underlying type is the product
`(Fin n →₀ ℕ) → R` indexed by the monomials, carrying the coefficientwise module structure: the
instance found for `Module R (MvPowerSeries (Fin n) R)` is `Pi.module` on that product, up to
`rfl`. This is the source's "the `R`-module `M`" with nothing chosen, and the statement uses only
that structure, never the ring structure of `M`.

The source's hypothesis that `n` be positive is dropped, and the lemma is stated for every
`n : ℕ`. It is consumed by neither conjunct: at `n = 0` the monomials form a subsingleton, so `M`
is free of rank one and hence flat and Mittag-Leffler, and Lemma 05D0, the only input, puts no
condition on its index set at all. Dropping it strengthens the statement.

The variables are indexed by `Fin n`, the source's object. Nothing in the mathematics uses the
finiteness of the index set — the form with an arbitrary index set is Lemma 05D0, cited here — but
an index type in its own universe would put 05D0's index set outside `Type u`, where 05D0 fixes it,
so the index-general form is not restated here. Remark 059Y quotes the one-variable case, and
`PowerSeries R` is `MvPowerSeries Unit R` up to `rfl`, reached along an index equivalence.

Mathlib has no predicate for a Mittag-Leffler *module* — its
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system* —
so being Mittag-Leffler is spelled out inline in the intrinsic form 059E (1), exactly as in
Lemma 05D0, Proposition 059M, Lemma 059S and Lemma 0AS6: every map `f : P → M` from a finitely
presented module dominates and is dominated by a map `g : P → Q` into a finitely presented module,
domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. The second conjunct
is therefore that condition at `M = MvPowerSeries (Fin n) R`.

The two conclusions are one conjunction, as the source states them: they are two properties of a
single module, both consequences of the single hypothesis on `R`, and the Mittag-Leffler criterion
059S is stated for a flat module, so the second conclusion is reached through the first.

Since `R : Type u` and the monomials `Fin n →₀ ℕ` lie in `Type 0`, the module
`MvPowerSeries (Fin n) R` lies in `Type u`, and the modules `P`, `Q`, `N` of the Mittag-Leffler
condition range over `Type u` as well, as they do in 05D0 and, at `v := u`, in 059S; `Small.{u} R`
then holds by `small_self`, so that quantifier is the source's quantifier over all finitely
presented `R`-modules. Lemma 05D0 indexes its product by a set in the universe of `R`, and the
monomials are recovered from it as `Shrink.{u} (Fin n →₀ ℕ)`, transporting along
`LinearEquiv.funCongrLeft R R (equivShrink _).symm`; a test module in a larger universe is reached
by applying the statement to a `ULift` copy of it.

The ring structure of `M` plays no part. As an `R`-module a power series is its family of
coefficients, so `M` is the product of copies of `R` indexed by the monomials in `t_1, …, t_n`, and
both conclusions are the case `A = ` monomials of Lemma 05D0. The monomials `Fin n →₀ ℕ` lie in
`Type 0` while 05D0 indexes its product by a set in the universe of `R`, so the index set used is
`Shrink.{u} (Fin n →₀ ℕ)`, and the two conclusions are transported back along the linear
equivalence `LinearEquiv.funCongrLeft R R (equivShrink _)`: flatness by
`Module.Flat.of_linearEquiv`, and the Mittag-Leffler condition by
`Module.mittagLeffler_of_linearEquiv`.

Transporting the Mittag-Leffler condition uses no property of the equivalence `e` beyond
`LinearMap.rTensor N e` being an equivalence again: a test map `f : P → M` is pushed to `e ∘ₗ f`,
which has the same tensored kernels as `f`, so a map dominating `e ∘ₗ f` dominates `f`. The
condition, spelled out inline by every statement of this family, is
`Module.IsMittagLefflerKerEq`, and that is how the transport lemma states it.

The identification of `MvPowerSeries (Fin n) R` with the product `(Fin n →₀ ℕ) → R` needs no map:
Mathlib defines the former as the latter and its `Module R` instance is `inferInstanceAs` of the
`Pi` instance, so the two are the same `R`-module and the transporting equivalence is the index
equivalence alone.

Faithfulness. (1) `IsNoetherianRing R` is consumed by both conjuncts, by coherence for the first
and through the finite presentation of the submodules of a finite free module for the second, and
it is the only hypothesis: `n` carries nothing, the source's positivity having been dropped as
unused. (2) The scalars and the base are the source's: one commutative ring `R` throughout, `M` an
`R`-module by its coefficientwise structure, flatness over `R`, every tensor product of the
Mittag-Leffler condition over `R` and every map `R`-linear; nothing is over the ring
`R[[t_1, …, t_n]]`, nothing is localized or base changed. (3) The source names no canonical map
here; the one map the statement does mention it pins, the Mittag-Leffler condition comparing the
kernels of `LinearMap.rTensor N f` and `LinearMap.rTensor N g` by equality rather than asserting a
factorization to exist. (4) The instantiation is not degenerate: for `R = ℤ` and `n = 1` the module
is `ℤ[[t]] = ℤ^ℕ`, which is flat and Mittag-Leffler and not free, so neither conjunct is automatic,
and the Mittag-Leffler condition genuinely excludes flat modules, `ℚ` over `ℤ` being flat and not
Mittag-Leffler by Example 059I; the quantifier of the second conjunct is non-vacuous, `P := R`
being available.

## References

* [StacksProject 059T](https://stacks.math.columbia.edu/tag/059T)
-/

/-- Let `R` be a Noetherian ring and let `n : ℕ`. Then the power series module
`M = R[[t_1, …, t_n]]`, regarded as an `R`-module, is flat and Mittag-Leffler.

Being Mittag-Leffler is spelled out inline as condition (1) of Proposition 059E: every map
`f : P → M` from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q`
into a finitely presented `R`-module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every
`R`-module `N`. -/
@[stacks 059T "The source's `0 < n` is dropped as unused: at `n = 0` the module is free of rank
one, hence flat and Mittag-Leffler. Mittag-Leffler is spelled out inline as condition (1) of 059E,
as in 05D0, 059M, 059S and 0AS6; `R[[t_1, …, t_n]]` is `MvPowerSeries (Fin n) R`, the product over
the monomials with its coefficientwise `R`-module structure, and the two conclusions are one
conjunction, as in the source. Test data in the universe of `R`. See the module docstring."]
theorem Module.flat_and_mittagLeffler_mvPowerSeries (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℕ) :
    Module.Flat R (MvPowerSeries (Fin n) R) ∧
      ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] MvPowerSeries (Fin n) R), ∃ (Q : Type u) (_ : AddCommGroup Q)
          (_ : Module R Q) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
            ∀ (N : Type u) [AddCommGroup N] [Module R N],
              LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  obtain ⟨hflat, hML⟩ := Module.flat_and_mittagLeffler_pi R (Shrink.{u} (Fin n →₀ ℕ))
  have e : MvPowerSeries (Fin n) R ≃ₗ[R] (Shrink.{u} (Fin n →₀ ℕ) → R) :=
    (LinearEquiv.funCongrLeft R R (equivShrink _)).symm
  exact ⟨Module.Flat.of_linearEquiv e, Module.mittagLeffler_of_linearEquiv e hML⟩

end
