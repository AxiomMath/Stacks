module

public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Countable generation along a tower and over a finite type algebra

`Module.CountablyGenerated R M` asks for an at most countable subset of `M` whose `R`-span is all
of `M`. This file supplies the two closure properties that the definition is missing, and the
consequence they are wanted for.

The first is transitivity along a tower `R → S → M`: the products of a countable generating set of
`S` over `R` with a countable generating set of `M` over `S` generate `M` over `R`, because
`Submodule.span_smul_of_span_eq_top` identifies the `R`-span of that product set with the
`S`-span of the second set, read as an `R`-submodule.

The second is that a finite type algebra is countably generated as a module. A finite type algebra
is a quotient of a polynomial ring in finitely many variables, and the monomials of such a ring
form a basis indexed by `ι →₀ ℕ` for `ι` finite, which is countable.

Together they give the statement actually consumed downstream: a module finite over a finite type
algebra is countably generated over the base ring. That is the hypothesis of the
Mittag-Leffler criterion for projectivity, Tag 059X, in its geometric applications, where `R → S`
is a ring map of finite presentation and the module is finitely presented over `S`.

## Main results

* `Module.CountablyGenerated.of_basis`: a module with an at most countable basis is countably
  generated.
* `Module.CountablyGenerated.trans`: countable generation is transitive along a tower.
* `Module.countablyGenerated_of_algebra_finiteType`: a finite type algebra is countably generated
  as a module over its base ring.
* `Module.countablyGenerated_of_finiteType_of_finite`: a module finite over a finite type algebra
  is countably generated over the base ring.

## Implementation notes

The three rings and modules are left in unrelated universes throughout; nothing in the arguments
relates them, and the geometric consumer instantiates all of them in one universe.

`Module.CountablyGenerated` is the notion defined alongside Tag 0GVD; the root-namespace
`CountablyGenerated` of `StacksFrontier.RingTheory.Module.Kaplansky` and the submodule-level
`Submodule.IsCountablyGenerated` are distinct declarations unfolding to the same existential, and
are not referred to here.
-/

@[expose] public section

open scoped Pointwise

universe u v w

namespace Module

/-- A module admitting a basis indexed by an at most countable type is countably generated: the
range of the basis is a countable spanning set. -/
theorem CountablyGenerated.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Countable ι] (b : Basis ι R M) : Module.CountablyGenerated R M :=
  ⟨Set.range b, Set.countable_range _, b.span_eq⟩

/-- **Countable generation is transitive along a tower.** If `S` is countably generated as an
`R`-module and `M` is countably generated as an `S`-module, then `M` is countably generated as an
`R`-module: for countable generating sets `s` of `S` and `t` of `M`, the set of products `s • t`
is countable, and its `R`-span is the `R`-submodule underlying the `S`-span of `t`, which is
everything. -/
theorem CountablyGenerated.trans {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module S M] [Module R M] [IsScalarTower R S M]
    (hS : Module.CountablyGenerated R S) (hM : Module.CountablyGenerated S M) :
    Module.CountablyGenerated R M := by
  obtain ⟨s, hsc, hss⟩ := hS
  obtain ⟨t, htc, hts⟩ := hM
  refine ⟨s • t, hsc.image2 htc _, ?_⟩
  rw [Submodule.span_smul_of_span_eq_top hss t, hts, Submodule.restrictScalars_top]

/-- **A finite type algebra is countably generated as a module.** A finite type `R`-algebra `S` is
a quotient of a polynomial ring over `R` in finitely many variables, whose monomials form a basis
indexed by the countable type `ι →₀ ℕ`; countable generation passes to the quotient. -/
theorem countablyGenerated_of_algebra_finiteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] : Module.CountablyGenerated R S := by
  obtain ⟨ι, hι, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp ‹_›
  have : Fintype ι := hι
  exact CountablyGenerated.of_surjective f.toLinearMap hf
    (CountablyGenerated.of_basis (MvPolynomial.basisMonomials ι R))

/-- **A module finite over a finite type algebra is countably generated over the base ring.** For
a finite type `R`-algebra `S` and an `S`-module `N` which is finite over `S`, the products of a
monomial in finitely many algebra generators of `S` with one of finitely many module generators of
`N` form a countable `R`-generating set of `N`.

This is the countable generation hypothesis of Tag 059X in the situation of Tag 05MD, where
`R → S` is of finite presentation and `N` is finitely presented over `S`. -/
theorem countablyGenerated_of_finiteType_of_finite (R S N : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Algebra.FiniteType R S] [Module.Finite S N] : Module.CountablyGenerated R N :=
  (countablyGenerated_of_algebra_finiteType R S).trans (CountablyGenerated.of_finite S N)

end Module

end
