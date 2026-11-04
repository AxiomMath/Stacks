module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation of flat finite modules over an algebra of finite type

Let `R → S` be a ring map of finite type and let `M` be a finite `S`-module which is flat over
`R`. Whether `M` is finitely presented over `S` is a question that only has to be answered when
`S` is a polynomial ring: choosing a surjection `R[x_1, …, x_n] → S` makes `M` a finite module
over the polynomial ring, still flat over `R`, and finite presentation descends from the
polynomial ring to `S` because `S` is of finite type over it. The same reduction applied to `M =
S` turns finite presentation of `S` as a module over the polynomial ring into finite
presentation of `S` as an `R`-algebra, the kernel of the surjection being finitely generated.

This file carries out that reduction, for both the module and the algebra conclusion, and
records the ring-theoretic input it is applied with over a domain: a domain has exactly one
weakly associated prime, the zero ideal.

## Main results

* `Algebra.FinitePresentation.of_surjective_of_finitePresentation_module`: a quotient of a
  finitely presented algebra which is finitely presented as a module over it is a finitely
  presented algebra.
* `Module.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial` and
  `Algebra.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial`: the reduction of the
  module and the algebra conclusion to the case of a polynomial ring.
* `weaklyAssociatedPrimes_eq_singleton_bot_of_isDomain` and
  `weaklyAssociatedPrimes_finite_of_isDomain`: the weakly associated primes of a domain.

## Implementation notes

The hypothesis of the two reduction theorems is the statement to be reduced, quantified over
the number of variables and over the modules of one universe: every module over
`R[x_1, …, x_n]` which is finite over it and flat over `R` is finitely presented over it. It is
not assumed for a single `n`, because the surjection produced by finite type of `S` has a number
of variables that is not known in advance.

Descent of finite presentation from the polynomial ring to `S` is
`Module.FinitePresentation.of_restrictScalars_of_finiteType`, which needs only that `S` is of
finite type over the polynomial ring, and not that it is finite over it.

## References

* [Stacks Project, Tag 0561](https://stacks.math.columbia.edu/tag/0561)
* [Stacks Project, Tag 0EMA](https://stacks.math.columbia.edu/tag/0EMA)
-/

@[expose] public section

universe u v w

/-- **A quotient of a finitely presented algebra which is a finitely presented module over it is
a finitely presented algebra.** The kernel of the surjection is finitely generated because the
target is a finitely presented module over the source, and a quotient of a finitely presented
algebra by a finitely generated ideal is finitely presented. -/
@[ega "IV 1.4.7" "special case"]
theorem Algebra.FinitePresentation.of_surjective_of_finitePresentation_module {A : Type u}
    [CommRing A] {P : Type v} [CommRing P] [Algebra A P] [Algebra.FinitePresentation A P]
    {B : Type w} [CommRing B] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
    [Module.FinitePresentation P B] (hsurj : Function.Surjective (algebraMap P B)) :
    Algebra.FinitePresentation A B := by
  have hker : (RingHom.ker (Algebra.ofId P B).toRingHom).FG :=
    Module.FinitePresentation.fg_ker (Algebra.linearMap P B) hsurj
  have : Algebra.FinitePresentation P B :=
    Algebra.FinitePresentation.of_surjective (f := Algebra.ofId P B) hsurj hker
  exact Algebra.FinitePresentation.trans A P B

/-- An algebra of finite type over `R` is a finite module over a polynomial ring, through a
surjection compatible with `R`. -/
private theorem exists_algebra_mvPolynomial_surjective (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) R) S),
      IsScalarTower R (MvPolynomial (Fin n) R) S ∧
        Function.Surjective (algebraMap (MvPolynomial (Fin n) R) S) ∧
          Module.Finite (MvPolynomial (Fin n) R) S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let : Algebra (MvPolynomial (Fin n) R) S := f.toRingHom.toAlgebra
  exact ⟨n, this, IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm, hf,
    Module.Finite.of_surjective (Algebra.linearMap _ S) hf⟩

/-- **Finite presentation of a flat finite module reduces to the polynomial case.** If every
module over a polynomial ring `R[x_1, …, x_n]` which is finite over it and flat over `R` is
finitely presented over it, then every finite module over an `R`-algebra of finite type which is
flat over `R` is finitely presented. -/
theorem Module.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial {R : Type u}
    [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] {M : Type w}
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] [Module.Finite S M]
    [Module.Flat R M]
    (hpoly : ∀ (n : ℕ) (N : Type w) [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
      [Module R N] [IsScalarTower R (MvPolynomial (Fin n) R) N]
      [Module.Finite (MvPolynomial (Fin n) R) N] [Module.Flat R N],
      Module.FinitePresentation (MvPolynomial (Fin n) R) N) :
    Module.FinitePresentation S M := by
  obtain ⟨n, _, _, -, _⟩ := exists_algebra_mvPolynomial_surjective R S
  let P := MvPolynomial (Fin n) R
  let : Module P M := Module.compHom M (algebraMap P S)
  let : IsScalarTower P S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R P M := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap P S (algebraMap R P r) • m = r • m
    rw [← IsScalarTower.algebraMap_apply, algebraMap_smul]
  have : Module.Finite P M := Module.Finite.trans (R := P) S M
  have : Module.FinitePresentation P M := hpoly n M
  exact Module.FinitePresentation.of_restrictScalars_of_finiteType P S M

/-- **Finite presentation of a flat algebra of finite type reduces to the polynomial case.** If
every module over a polynomial ring `R[x_1, …, x_n]` which is finite over it and flat over `R`
is finitely presented over it, then every `R`-algebra of finite type which is flat over `R` is
finitely presented. -/
theorem Algebra.FinitePresentation.of_flat_of_finitePresentation_mvPolynomial {R : Type u}
    [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [Module.Flat R S]
    (hpoly : ∀ (n : ℕ) (N : Type v) [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
      [Module R N] [IsScalarTower R (MvPolynomial (Fin n) R) N]
      [Module.Finite (MvPolynomial (Fin n) R) N] [Module.Flat R N],
      Module.FinitePresentation (MvPolynomial (Fin n) R) N) :
    Algebra.FinitePresentation R S := by
  obtain ⟨n, _, _, hsurj, _⟩ := exists_algebra_mvPolynomial_surjective R S
  have : Module.FinitePresentation (MvPolynomial (Fin n) R) S := hpoly n S
  exact Algebra.FinitePresentation.of_surjective_of_finitePresentation_module hsurj

/-- **The weakly associated primes of a domain.** In a domain the annihilator of a nonzero
element is zero, so the only weakly associated prime is the zero ideal. -/
theorem weaklyAssociatedPrimes_eq_singleton_bot_of_isDomain (R : Type u) [CommRing R]
    [IsDomain R] : weaklyAssociatedPrimes R R = {⊥} := by
  rw [weakAss_eq_minimalPrimes0EMA, IsDomain.minimalPrimes_eq_singleton_bot]

/-- A domain has finitely many weakly associated primes. -/
theorem weaklyAssociatedPrimes_finite_of_isDomain (R : Type u) [CommRing R] [IsDomain R] :
    (weaklyAssociatedPrimes R R).Finite := by
  simp [weaklyAssociatedPrimes_eq_singleton_bot_of_isDomain R]
