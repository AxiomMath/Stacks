module

public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.PowerConditions
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.BaseChange
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples.GenerationCriteria

/-!
# Universal homeomorphisms

A ring map `φ : R → S` induces a *universal homeomorphism* on spectra when `Spec(S) → Spec(R)`
is a homeomorphism and remains one after every base change of `φ`. This file collects the
criteria for recognizing such a map, together with the field theory and the combinatorial
computation they rest on.

The criteria form a chain. An integral ring map injective on spectra is a closed embedding on
spectra, and a bijective one is a homeomorphism; in both cases the hypotheses — integrality,
injectivity or bijectivity on spectra, and pure inseparability of the induced residue field
extensions — are inherited by every base change, so an integral ring map bijective on spectra
with purely inseparable residue field extensions is a universal homeomorphism. The remaining
criteria are ways of recognizing one: `S` is generated over `R` by elements `x` with a liftable
power of `T - x`, or with `x ^ p ^ n` and `p ^ n • x` in the image of `φ` for a prime `p`, or
with `x ^ 2` and `x ^ 3` in the image, in each case with `ker φ` locally nilpotent.

Three of the ingredients are about fields. A field extension in which every element has a
positive power in the base field is either purely inseparable or of positive characteristic and
algebraic over its prime field, and this power condition is inherited by the residue field
extensions of a ring map having it. The arithmetic variant of the condition — every element
having some `x ^ p ^ n` and `p ^ n • x` in the base — is likewise either trivial or purely
inseparable of characteristic `p`; its proof rests on the divisibility computation of
`Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.exists_pow_mem` in `ℤ[x, y]`, which is what
  makes the set of such elements closed
under addition and is where the primality of `p` enters.

## Main definitions

* `Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.subringR`: the subring `ℤ[x ^ p ^ n, p ^ n
  x, y ^ p ^ m, p ^ m y]` of
  `ℤ[x, y] = MvPolynomial (Fin 2) ℤ`, where `x` and `y` are the two indeterminates `X 0`, `X 1`.

## Main results

* `Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.exists_pow_mem`: `(x + y) ^ p ^ a` and `p ^
  a (x + y)` lie in
  `ℤ[x ^ p ^ n, p ^ n x, y ^ p ^ m, p ^ m y]` for some `a`.
* `satisfiesGeneratingCondition_iff_structuralCondition`: for a field `K` with a subfield `k` and
  a prime `p`, the elements admitting an `n > 0` with `x ^ p ^ n ∈ k` and `p ^ n • x ∈ k` generate
  `K` over `k` if and only if `k = K`, or `char K = p` and `K / k` is purely inseparable.
* `Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective`: the base change of a surjective
  ring map is surjective, with kernel the image ideal of the original kernel.
* `forall_exists_pow_mem_iff_isPurelyInseparable_or_isAlgebraic_bot`: a field extension in which
  every element has a positive power in the base is purely inseparable, or of positive
  characteristic and algebraic over its prime field.
* `Ideal.ResidueField.exists_pow_mem_range_map`: that power condition passes to the residue
  field extensions induced by a ring map having it.
* `Algebra.IsPushout.injective_comap_and_residueFieldMap_isPurelyInseparable`: injectivity on
  spectra together with pure inseparability of the residue field extensions is stable under
  base change.
* `PrimeSpectrum.isClosedEmbedding_comap_of_isIntegral`,
  `PrimeSpectrum.isClosedEmbedding_comap_and_baseChange_of_injective_comap_of_isPurelyInseparable`,
  `PrimeSpectrum.isHomeomorph_comap_and_baseChange_of_bijective_comap_of_isPurelyInseparable`:
  an integral ring map injective, resp. bijective, on spectra is a closed embedding, resp. a
  homeomorphism, on spectra, universally so when the residue field extensions are purely
  inseparable.
* `PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_eq_top`,
  `PrimeSpectrum.isHomeomorph_comap_and_isPurelyInseparable_and_baseChange_of_adjoin_pow_eq_top`,
  `PrimeSpectrum.isHomeomorph_comap_and_residueFieldMap_bijective_of_adjoin_sq_cube_eq_top`:
  the three generation criteria.

## Implementation notes

"The kernel of `φ` is locally nilpotent" is `RingHom.ker (algebraMap R S) ≤ nilradical R`, the
spelling of the hypothesis of the upstream `PrimeSpectrum.isHomeomorph_comap`: an ideal is
locally nilpotent exactly when each of its elements is nilpotent. Each generation hypothesis is
a single equation `Algebra.adjoin R {x | …} = ⊤` on the set of *all* elements with the stated
property rather than an existential over generating sets; the two are equivalent because
`Algebra.adjoin` is monotone, and the equational form is literally the base-change conjunct of
the same statement, so a criterion can be fed back into itself along a tower of base changes
with no glue.

A base change is an arbitrary pushout square `Algebra.IsPushout R S R' S'` rather than the
construction `R' ⊗[R] S`; the latter is an instance of the former once
`Algebra.TensorProduct.rightAlgebra` is a local instance, and a base change already presented
in another shape — a quotient `R ⧸ I → S ⧸ I S`, a localization — is covered with no
intermediate isomorphism. Since "for every base change" is an honest quantifier, `R'` and `S'`
are bound inside the conclusion, in arbitrary universes.

A residue field extension is the canonical `Ideal.ResidueField.map p q φ hpq : κ(p) → κ(q)`,
with the prime below pinned by `hpq : p = q.comap φ` rather than fixed as `q.comap φ`, so that
a `p` presented in another way (through `Ideal.LiesOver`, say) needs no rewriting; "purely
inseparable" is `RingHom.IsPurelyInseparable` of that map, and "isomorphism" is
`Function.Surjective`, injectivity being automatic for a ring map of fields. A homeomorphism of
spectra is the predicate `IsHomeomorph` on the function rather than a bundled `Homeomorph`, and
a homeomorphism onto a closed subset is `Topology.IsClosedEmbedding`, whose range is closed and
which is a homeomorphism onto it.

`satisfiesGeneratingCondition_iff_structuralCondition` models a field extension `k'/k` by a
single field `K` together with a subfield `k : Subfield K`, so that `IsPurelyInseparable k K`
expresses pure inseparability and `k = k'` becomes `k = ⊤`. A subfield shares the prime subfield
of `K`, hence its characteristic, so "`char k = char k' = p`" is the single condition
`ringChar K = p`.

Two statements are more general than their sources. `Ideal.ResidueField.exists_pow_mem_range_map`
omits the hypothesis that `ker φ` be locally nilpotent, which the source's proof of the residue
field assertion does not use; and `PrimeSpectrum.isClosedEmbedding_comap_of_isIntegral` is
stated for a bare ring map with no hypothesis on residue fields, that being all its proof needs.
Conversely `…_of_adjoin_sq_cube_eq_top` is not a case of `PrimeSpectrum.isHomeomorph_comap`:
generation by elements whose square and cube lie in the image does not give every element of `S`
a power in the image, as `k → k[X] ⧸ (X ^ 2)` in characteristic `0` shows, where
`(1 + X) ^ n = 1 + n X ∉ k` for all `n > 0`.

## References

* [Stacks Project, Tag 0545](https://stacks.math.columbia.edu/tag/0545)
* [Stacks Project, Tag 09EF](https://stacks.math.columbia.edu/tag/09EF)
* [Stacks Project, Tag 0BR6](https://stacks.math.columbia.edu/tag/0BR6)
* [Stacks Project, Tag 0BR7](https://stacks.math.columbia.edu/tag/0BR7)
* [Stacks Project, Tag 0BR8](https://stacks.math.columbia.edu/tag/0BR8)
* [Stacks Project, Tag 0BR9](https://stacks.math.columbia.edu/tag/0BR9)
* [Stacks Project, Tag 0BRA](https://stacks.math.columbia.edu/tag/0BRA)
* [Stacks Project, Tag 0BRB](https://stacks.math.columbia.edu/tag/0BRB)
* [Stacks Project, Tag 0BRC](https://stacks.math.columbia.edu/tag/0BRC)
* [Stacks Project, Tag 0BRD](https://stacks.math.columbia.edu/tag/0BRD)
* [Stacks Project, Tag 0EUH](https://stacks.math.columbia.edu/tag/0EUH)
* [Alper, *Adequate moduli spaces and geometrically reductive group schemes*, Lemma 3.1.6]
  [Alper-adequate]

## Tags

universal homeomorphism, prime spectrum, homeomorphism, closed embedding, base change, residue
field, purely inseparable, radicial, locally nilpotent, integral

-/
