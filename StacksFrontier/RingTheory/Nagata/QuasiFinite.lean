module

public import Mathlib.RingTheory.Finiteness.Quotient
public import StacksFrontier.RingTheory.Nagata.JapaneseCriteria

@[expose] public section

universe u

/-!
# The Nagata condition ascends along a quasi-finite ring map

Proof of `isNagataRing_of_quasiFinite`: if `R` is a Nagata ring — Noetherian, with every quotient
`R ⧸ p` by a prime ideal N-2 — and `R → S` is quasi-finite, that is of finite type with
finite-dimensional fibres, then `S` is a Nagata ring.

The argument is the source's, and both clauses of the conclusion are read off existing results.
`S` is Noetherian because it is of finite type over the Noetherian ring `R`. For a prime `q ⊆ S`,
put `p = q ∩ R`; then the induced map `R ⧸ p → S ⧸ q` is an *injective* quasi-finite map of
domains between Noetherian rings, so `S ⧸ q` is N-2 by Tag 032I applied to the N-2 domain
`R ⧸ p` supplied by the Nagata hypothesis. Injectivity, which Tag 032I needs and `R → S` need not
have, is what passing to the quotient at `p = q ∩ R` manufactures.

## Main results

* `Stacks.Nagata.QuasiFiniteAscent.solution`: the proof of `isNagataRing_of_quasiFinite`.

## Implementation notes

Every step of the descent to the quotients is an instance already in Mathlib for the relation
`q.LiesOver p`, taken here at `p = q.under R`, where it holds by definition
(`Ideal.over_under`): the algebra structure on `R ⧸ p → S ⧸ q` is `Ideal.algebraOfLiesOver`, its
injectivity is `Ideal.instFaithfulSMul`, its finite type is `algebra_finiteType_of_liesOver`, and
`(q.under R).IsPrime` is `Ideal.IsPrime.under`. The one assertion of the source's proof that no
instance delivers — that `R ⧸ p → S ⧸ q` is again quasi-finite — is
`algebra_quasiFinite_of_liesOver` below, the missing member of the Mathlib family
`module_finite_of_liesOver`, `algebra_finiteType_of_liesOver`, `isNoetherian_of_liesOver`, and
proved as they are: `S ⧸ q` is a quotient of `S`, hence quasi-finite over `R`, and
quasi-finiteness of a composite passes to its upper map. It is stated here as a `private` theorem
rather than the instance it should be, so that nothing is added to instance search downstream.

## References

* [Stacks Project, Tag 032T](https://stacks.math.columbia.edu/tag/032T)
* [Stacks Project, Tag 032I](https://stacks.math.columbia.edu/tag/032I)
* [Stacks Project, Tag 032R](https://stacks.math.columbia.edu/tag/032R)
-/

@[expose] public section



namespace Stacks.Nagata.QuasiFiniteAscent

/-- `S ⧸ q` is a quasi-finite `R ⧸ p`-algebra if `S` is a quasi-finite `R`-algebra and `q` lies
over `p`. This is the quasi-finite sibling of `algebra_finiteType_of_liesOver`. -/
private theorem algebra_quasiFinite_of_liesOver {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) (p : Ideal R) [q.LiesOver p] [Algebra.QuasiFinite R S] :
    Algebra.QuasiFinite (R ⧸ p) (S ⧸ q) :=
  .of_restrictScalars R (R ⧸ p) (S ⧸ q)

/-- **A quasi-finite algebra over a Nagata ring is a Nagata ring.** Proof of Tag 032T: `S` is
Noetherian since it is of finite type over the Noetherian ring `R`, and for a prime `q ⊆ S` the
quotient `S ⧸ q` is N-2 by Tag 032I applied to the injective quasi-finite map of domains
`R ⧸ (q ∩ R) → S ⧸ q`, whose source is N-2 by hypothesis. -/
public theorem solution {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] (hR : IsNagataRing R) :
    IsNagataRing S := by
  have : IsNoetherianRing R := hR.1
  refine ⟨Algebra.FiniteType.isNoetherianRing R S, fun q _ ↦ ?_⟩
  have := algebra_quasiFinite_of_liesOver q (q.under R)
  exact isJapaneseRing_of_quasiFinite (hR.2 (q.under R))

end Stacks.Nagata.QuasiFiniteAscent

end

/-!
# The Nagata condition ascends along a quasi-finite ring map

A ring is a **Nagata ring** when it is Noetherian and each of its quotients by a prime ideal is
N-2 (Japanese); this is `IsNagataRing`, the predicate of Tag 032R(2). Let `R → S` be a
quasi-finite ring map — of finite type, with finite-dimensional fibres — for instance a
module-finite one. If `R` is a Nagata ring, then so is `S`.

Both clauses of the conclusion transfer, and by different routes. `S` is Noetherian because an
algebra of finite type over a Noetherian ring is (`Algebra.FiniteType.isNoetherianRing`). For a
prime `q ⊆ S` lying over `p = q ∩ R`, the induced map `R ⧸ p → S ⧸ q` is again quasi-finite and is
now *injective*, so `S ⧸ q` is N-2 by Tag 032I applied to the Nagata hypothesis
`IsJapaneseRing (R ⧸ p)`. Nothing is asked of `R → S` beyond quasi-finiteness: the injectivity
that Tag 032I needs is manufactured by passing to the quotients, which is why the statement covers
maps as far from injective as `R → R ⧸ p`.

## Main results

* `isNagataRing_of_quasiFinite`: a quasi-finite algebra over a Nagata ring is a Nagata ring.

## Implementation notes

Quasi-finiteness in the sense of [Stacks, Tag 00PL] is the pair
`[Algebra.FiniteType R S] [Algebra.QuasiFinite R S]`: Mathlib's `Algebra.QuasiFinite` asks only
that every fibre `κ(p) ⊗[R] S` be a finite `κ(p)`-module and deliberately drops the finite type
requirement (`R → Frac(R)` is `Algebra.QuasiFinite`). Both halves are used, in different places:
finite type gives Noetherianity of `S` and is what Zariski's main theorem consumes inside Tag
032I, while finiteness of the fibres is what makes the extension of fraction fields
`Frac(R ⧸ p) ⊆ Frac(S ⧸ q)` finite. The source's parenthetical "for example finite" needs no
separate statement: `Module.Finite R S` supplies both instances by inference.

The hypothesis and the conclusion are one and the same predicate, so no reformulation of "Nagata"
is interposed between them: this is `IsNagataRing R → IsNagataRing S` for the `IsNagataRing`
carrying Tag 032R(2), rather than that predicate's two clauses spelled out at the two ends.

`R` and `S` share the universe `u`, because `IsNagataRing` — through the `IsJapaneseRing` of Tag
032F — tests a ring against the finite extensions of the fraction fields of its prime quotients
that live in the ring's own universe. Nothing is lost: `S` is of finite type over `R`, hence a
quotient of `MvPolynomial (Fin n) R`, so it is `R`-isomorphic to a ring in `Type u`, and
`IsNagataRing` is invariant under ring isomorphism.

Faithfulness, point by point.
1. No hypothesis is dead: `Algebra.FiniteType R S` is consumed twice (Noetherianity of `S`, and
   the finite type hypothesis of Tag 032I on `R ⧸ p → S ⧸ q`), `Algebra.QuasiFinite R S` gives the
   fibre of that map, and `IsNagataRing R` supplies both the Noetherian and the N-2 input.
2. The scalars and base are the source's: N-2 for `S ⧸ q` asserts finiteness of an integral
   closure as a module over `S ⧸ q` itself, and the Nagata hypothesis is read on the quotients of
   `R` — not over the fraction fields, and not on localizations of `S`.
3. The map along which `S` is an `R`-algebra is the pinned `algebraMap R S`, and it is that map
   that `Algebra.FiniteType` and `Algebra.QuasiFinite` both speak about; the quotient maps
   `R ⧸ p → S ⧸ q` used in the proof are induced by it rather than chosen.
4. The instantiation is not degenerate: the module-finite extension `ℤ ⊆ ℤ[i]` satisfies the
   hypotheses over the Nagata ring `ℤ`, and `R → Localization.Away f` is of finite type and
   quasi-finite by instance inference without being module-finite, so the hypotheses are strictly
   weaker than finiteness and the statement already contains the one-element case of Tag 032U.

## References

* [Stacks Project, Tag 032T](https://stacks.math.columbia.edu/tag/032T)
* [Stacks Project, Tag 032R](https://stacks.math.columbia.edu/tag/032R)
* [Stacks Project, Tag 032I](https://stacks.math.columbia.edu/tag/032I)
* [Stacks Project, Tag 00PL](https://stacks.math.columbia.edu/tag/00PL)
-/

@[expose] public section



/-- **A quasi-finite algebra over a Nagata ring is a Nagata ring.** If `R` is a Nagata ring —
Noetherian, with every quotient `R ⧸ p` by a prime N-2 — and `R → S` is quasi-finite, that is of
finite type with finite-dimensional fibres (for example module-finite), then `S` is a Nagata ring.

Quasi-finiteness in the sense of [Stacks, Tag 00PL] is the conjunction
`[Algebra.FiniteType R S] [Algebra.QuasiFinite R S]`, Mathlib's `Algebra.QuasiFinite` omitting the
finite type condition. No injectivity is required: the map `R → S` is arbitrary. -/
@[stacks 032T]
public theorem isNagataRing_of_quasiFinite {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] (hR : IsNagataRing R) :
    IsNagataRing S := Stacks.Nagata.QuasiFiniteAscent.solution hR

end
