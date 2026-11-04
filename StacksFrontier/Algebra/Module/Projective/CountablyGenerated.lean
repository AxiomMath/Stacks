module

import StacksFrontier.LinearAlgebra.DirectSum.ProjectiveCountablyGenerated
import Mathlib.LinearAlgebra.DirectSum.Basis

public import StacksFrontier.Algebra.MittagLeffler.ShortExact
public import StacksFrontier.Algebra.MittagLeffler.MvPowerSeries
public import StacksFrontier.Algebra.MittagLeffler.ProjectiveCharacterization

@[expose] public section


@[expose] public section

universe u v

/-!
# Freeness of projective modules is a countably generated question

Let `R` be a ring. This file proves that every projective `R`-module is free as soon as every
countably generated projective `R`-module is free.

One direction is a weakening of the hypothesis. For the other, let `M` be a projective `R`-module.
By Kaplansky's theorem (Stacks 058Y) there is an independent set `S` of submodules of `M` with
supremum `⊤`, each member of it countably generated and projective; each member is therefore free
by hypothesis. Independence together with `sSup S = ⊤` says that `M` is the internal direct sum of
the members of `S`, so `M` is isomorphic to a direct sum of free modules and hence free.

## Main results

* `Module.CountableSpanFree.forall_free_iff`: the proof of Stacks 0590, as stated in
  `Module.forall_free_of_projective_iff_forall_free_of_projective_of_countable_span`.

## Implementation notes

The two steps of the nontrivial direction are the two lemmas preceding `forall_free_iff`, and
both are general facts with no Mathlib name.

`exists_countable_span_eq_top_of_span_eq` converts countable generation of a submodule `N ≤ M` by
a subset of `M`, the form in which Stacks 058W, 058X and 058Y state it, into countable generation
of `↥N` as a module, the form the right-hand side of Stacks 0590 asks for; over `↥N` the spanning
set is the preimage of the given one along the inclusion, which spans by
`Submodule.span_span_coe_preimage`.

`free_of_sSupIndep_of_sSup_eq_top` is the endgame: an independent set of submodules with supremum
`⊤` and free members makes the ambient module free. Independence and `sSup S = ⊤` give the internal
direct sum decomposition indexed by `↥S` — this is `sSupIndep_iff` and `sSup_eq_iSup'` followed by
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` — and freeness then transfers from the
external direct sum along `Module.Free.directSum` and `Module.Free.of_equiv`. It is stated for a
*set* of submodules rather than an indexed family because that is the form Stacks 058W, 058X and
058Y state their decompositions in.

Stacks 058Y presents its decomposition internally, as submodules of `M`; these live in the same
universe as `M`, which is why the reduction needs no smallness hypothesis relating the universe of
`R` to that of the modules.

## References

* [Stacks 0590](https://stacks.math.columbia.edu/tag/0590)
* [Stacks 058Y](https://stacks.math.columbia.edu/tag/058Y)
* I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372-377
-/

namespace Module.CountableSpanFree



/-- A submodule spanned by a countable subset of the ambient module is countably generated as a
module in its own right: the preimage of the spanning set along the inclusion spans `↥N`. -/
private lemma exists_countable_span_eq_top_of_span_eq {R : Type*} {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] {N : Submodule R M} {t : Set M} (ht : t.Countable)
    (hts : Submodule.span R t = N) : ∃ s : Set ↥N, s.Countable ∧ Submodule.span R s = ⊤ := by
  subst hts
  exact ⟨_, ht.preimage Subtype.val_injective, Submodule.span_span_coe_preimage⟩

/-- A module is free as soon as it is the internal direct sum of free submodules, presented as an
independent set of submodules with supremum `⊤`: it is isomorphic to the external direct sum of the
members of that set, which is free. -/
private lemma free_of_sSupIndep_of_sSup_eq_top {R : Type*} {M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {S : Set (Submodule R M)} (hindep : sSupIndep S) (htop : sSup S = ⊤)
    (hfree : ∀ N ∈ S, Module.Free R ↥N) : Module.Free R M := by
  classical
  have : ∀ N : S, Module.Free R ↥(N : Submodule R M) := fun N => hfree N N.2
  exact Module.Free.of_equiv (LinearEquiv.ofBijective
    (DirectSum.coeLinearMap fun N : S => (N : Submodule R M))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ((sSupIndep_iff S).1 hindep)
      ((sSup_eq_iSup' S).symm.trans htop)))

/-- Let `R` be a ring. Every projective `R`-module is free if and only if every projective
`R`-module admitting a countable generating set is free. -/
public theorem forall_free_iff (R : Type u) [Ring R] :
    (∀ (M : Type v) [AddCommGroup M] [Module R M], Module.Projective R M → Module.Free R M) ↔
      ∀ (M : Type v) [AddCommGroup M] [Module R M], Module.Projective R M →
        (∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤) → Module.Free R M := by
  refine ⟨fun h M _ _ hM _ => h M hM, fun h M _ _ hM => ?_⟩
  obtain ⟨S, hindep, htop, hS⟩ :=
    Submodule.exists_sSupIndep_countable_span_projective_of_projective (R := R) (M := M)
  refine free_of_sSupIndep_of_sSup_eq_top hindep htop fun N hN => ?_
  obtain ⟨⟨t, htc, hts⟩, hproj⟩ := hS N hN
  exact h _ hproj (exists_countable_span_eq_top_of_span_eq htc hts)

end Module.CountableSpanFree

/-!
# Freeness of projective modules is a countably generated question

Let `R` be a ring. Then every projective `R`-module is free if and only if every countably
generated projective `R`-module is free (Stacks 0590). One direction is a weakening of the
hypothesis; the other is Kaplansky's decomposition of a projective module as a direct sum of
countably generated projective modules (Stacks 058Y), whose summands are free by assumption, so
that the module is a direct sum of free modules and hence free. Together with the criterion for a
countably generated module to be free (Stacks 0591) and the fact that over a local ring every
element of a projective module lies in a free direct summand (Stacks 0592), this reduction is the
first step of Kaplansky's theorem that a projective module over a local ring is free
(Stacks 0593).

## Main results

* `Module.forall_free_of_projective_iff_forall_free_of_projective_of_countable_span`: freeness of
  all projective `R`-modules is equivalent to freeness of the countably generated ones.

## Implementation notes

Countable generation is written as the existence of a countable generating set,
`∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤`. Mathlib has no predicate for it, and this
set-level form is both the source's wording and what a user of either side of the equivalence
produces and consumes. It is equivalent to the cardinal bound
`(⊤ : Submodule R M).spanRank ≤ Cardinal.aleph0` by `Submodule.spanRank_span_le_card` and
`Submodule.exists_span_set_card_eq_spanRank`, so nothing is lost by keeping the literal form.

The source quantifies over the class of all `R`-modules; here both sides quantify over the
modules in one universe `v`, arbitrary and unrelated to the universe `u` of `R`, so the statement
is a family of equivalences covering every universe. No smallness hypothesis is needed for this
to be the source's statement in each universe: Stacks 058Y decomposes a projective `M : Type v`
as an internal direct sum of countably generated projective *submodules* of `M`, and a submodule
of `M` again lives in `Type v`, so the right-hand side applies to the summands exactly as stated.

The ring is arbitrary and not assumed commutative, as in the source. It is a `Ring` and the
modules are `AddCommGroup`s rather than the `Semiring`/`AddCommMonoid` generality in which
`Module.Projective` and `Module.Free` are defined, because the route above decomposes a projective
module as a direct summand of a free module, which needs additive inverses.

Faithfulness. (1) No hypothesis is dead: `Ring R` is the source's only hypothesis, and the
countable generation condition is live, since it is what makes the right-hand side a priori
weaker — it is discharged only on the summands produced by Stacks 058Y. (2) The scalars and the
base are the source's: `Module.Projective R M`, `Module.Free R M` and `Submodule.span R s` are
all over `R` itself, with no localization or base change. (3) The source names no canonical map;
the one notion to pin down, "countably generated", is pinned as a countable spanning set rather
than as an abstract cardinality of `M`. (4) The instantiation is not degenerate and neither side
is vacuous or automatic: for `R` a division ring both sides hold, as every module is free, while
for the Dedekind domain `R = ℤ[√-5]` both sides fail, the ideal `(2, 1 + √-5)` being finitely,
hence countably, generated and projective but not free; and the classes quantified over are
nonempty, as `R` itself is a countably generated projective `R`-module.

## References

* [StacksProject 0590](https://stacks.math.columbia.edu/tag/0590)
-/



@[expose] public section

/-- Let `R` be a ring. Every projective `R`-module is free if and only if every projective
`R`-module admitting a countable generating set is free. -/
@[stacks 0590 "The equivalence, with countable generation written as a countable spanning set."]
public theorem Module.forall_free_of_projective_iff_forall_free_of_projective_of_countable_span
    (R : Type u) [Ring R] :
    (∀ (M : Type v) [AddCommGroup M] [Module R M], Module.Projective R M → Module.Free R M) ↔
      ∀ (M : Type v) [AddCommGroup M] [Module R M], Module.Projective R M →
        (∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤) → Module.Free R M :=
  Module.CountableSpanFree.forall_free_iff R

end

/-!
# A direct sum of countably generated modules pure in a flat Mittag-Leffler module is projective

Let `R` be a commutative ring and let `f : M → N` be a universally injective map of `R`-modules,
that is, one for which `f ⊗ id_T` is injective for every `R`-module `T`. This file proves Stacks
05A0: if `M` is a direct sum of countably generated `R`-modules and `N` is flat and Mittag-Leffler,
then `M` is projective.

Both properties of `N` descend to `M` along `f`, because `0 → M → N → N ⧸ f(M) → 0` is a
universally exact sequence. Flatness descends by Stacks 058P, and the whole of its argument is one
cancellation in the naturality square of the tensor product: for `g : A → B` the two composites
`(f ⊗ id_B) ∘ (id_M ⊗ g)` and `(id_N ⊗ g) ∘ (f ⊗ id_A)` are both `f ⊗ g`, so injectivity of
`f ⊗ id_A` and of `id_N ⊗ g` makes `id_M ⊗ g` a right factor of an injection, hence injective.
Taking `g` injective and using flatness of `N` for the second hypothesis, this is flatness of `M`.
The Mittag-Leffler property descends by Stacks 059N (1). Flatness, the Mittag-Leffler property and
the given decomposition are the three conditions of the characterization of projectivity,
Stacks 059Z, whose third condition is the hypothesis on `M` verbatim.

## Main results

* `Module.CountableSpanProjective.projective_of_sSupIndep_countable_span`: Stacks 05A0, the
  statement of `Module.projective_of_forall_rTensor_injective_of_exists_sSupIndep_countable_span`.

## Implementation notes

*The cancellation is separated from flatness.* `lTensor_injective_of_rTensor_injective` carries the
mathematics of the descent and mentions neither flatness nor a universe restriction: it is the
sub-object companion of Mathlib's `lTensor_injective_of_exact_of_exact_of_rTensor_injective`, which
transports injectivity of `id ⊗ g` along a right-exact row to the quotient term. On the sub-object
term no exactness is needed at all, only the naturality square, so the lemma is stated over a
commutative semiring for additive monoids, with the four modules in unrelated universes.

*Flatness of `M` is the first conclusion of Stacks 058P,* the descent of flatness to the sub-object
of a universally exact sequence, here with `R : Type u` and `M`, `N : Type v` under `Small.{v} R`,
the convention of Stacks 058K, 059E, 059N and 059Z. It is `flat_of_forall_rTensor_injective`,
stated for a single universally injective map into a flat module, which is all Stacks 058P uses for
its first conclusion — no quotient and no exactness enter the argument.

*The quotient supplies the sequence Stacks 059N asks for.* Stacks 059N is stated for a short exact
sequence, while Stacks 05A0 gives only the map `f`, so the third term is taken to be
`N ⧸ LinearMap.range f` with `LinearMap.exact_map_mkQ_range` and `Submodule.mkQ_surjective` for its
exactness and surjectivity; only item (1) of Stacks 059N is used, and it does not mention the third
term.

## References

* [StacksProject 05A0](https://stacks.math.columbia.edu/tag/05A0)
-/

namespace Module.CountableSpanProjective



/-- Injectivity of `id_M ⊗ g` descends from `id_N ⊗ g` along a map `f : M →ₗ[R] N` for which
`f ⊗ id_A` is injective: both `(f ⊗ id_B) ∘ (id_M ⊗ g)` and `(id_N ⊗ g) ∘ (f ⊗ id_A)` are `f ⊗ g`,
so `id_M ⊗ g` is a right factor of an injection. This is the sub-object companion of
`lTensor_injective_of_exact_of_exact_of_rTensor_injective`, and needs no exactness. -/
private theorem lTensor_injective_of_rTensor_injective {R : Type*} [CommSemiring R]
    {M N A B : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    (f : M →ₗ[R] N) (g : A →ₗ[R] B) (hf : Function.Injective (f.rTensor A))
    (hg : Function.Injective (g.lTensor N)) :
    Function.Injective (g.lTensor M) := by
  have h : Function.Injective (f.rTensor B ∘ g.lTensor M) := by
    rw [← LinearMap.coe_comp, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.coe_comp]
    exact hg.comp hf
  exact h.of_comp

/-- Flatness descends along a universally injective map: if `f : M →ₗ[R] N` is such that
`f ⊗ id_T` is injective for every `R`-module `T` and `N` is flat, then `M` is flat. This is the
first conclusion of Stacks 058P, whose proof uses neither the quotient nor the exactness of the
universally exact sequence it is stated for. -/
private theorem flat_of_forall_rTensor_injective {R : Type u} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]
    [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f.rTensor T)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{v, u, v}]
  intro A B _ _ _ _ g hg
  exact lTensor_injective_of_rTensor_injective f g (hf A)
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

/-- Let `f : M →ₗ[R] N` be universally injective, with `N` flat and Mittag-Leffler in the form
`hML`. If `M` is the internal direct sum of an independent set of submodules, each spanned by a
countable set, then `M` is projective. -/
public theorem projective_of_sSupIndep_countable_span
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f.rTensor T))
    (hM : ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ K ∈ S, ∃ t : Set M, t.Countable ∧ Submodule.span R t = K)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (g : P →ₗ[R] N), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (h : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (g.rTensor T) = LinearMap.ker (h.rTensor T)) :
    Module.Projective R M := by
  -- `0 → M → N → N ⧸ f(M) → 0` is universally exact, so Stacks 059N (1) gives Mittag-Leffler.
  have hMLM := (Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective
    (M₃ := N ⧸ LinearMap.range f) (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective _) hf).1 hML
  -- Flatness descends along `f`, and Stacks 059Z assembles the three conditions.
  exact (Module.projective_iff_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span R M).mpr
    ⟨flat_of_forall_rTensor_injective f hf, hMLM, hM⟩

end Module.CountableSpanProjective

/-!
# Projectivity of a direct sum of countably generated modules pure in a flat Mittag-Leffler module

Let `R` be a commutative ring and let `f : M → N` be a universally injective map of `R`-modules,
that is, one for which `f ⊗ id_T : M ⊗_R T → N ⊗_R T` is injective for every `R`-module `T`
(Definition 058I). Suppose `M` is a direct sum of countably generated `R`-modules and `N` is flat
and Mittag-Leffler. Then `M` is projective (Stacks 05A0).

The two properties of `N` descend to `M` along `f`. Universal injectivity of `f` makes
`0 → M → N → N/f(M) → 0` a universally exact sequence, so flatness of `N` gives flatness of `M`
(Stacks 058P) and the Mittag-Leffler property of `N` gives the Mittag-Leffler property of `M`
(Stacks 059N (1)); together with the given decomposition of `M` these are the three conditions of
the characterization of projectivity, Stacks 059Z, whose third condition is the hypothesis on `M`
verbatim. So the lemma is the transfer of conditions (1) and (2) of that theorem along a pure
inclusion, condition (3) being one that does not transfer and therefore stays a hypothesis.

## Main results

* `Module.projective_of_forall_rTensor_injective_of_exists_sSupIndep_countable_span`: a direct sum
  of countably generated modules admitting a universally injective map into a flat Mittag-Leffler
  module is projective.

## Implementation notes

*Universal injectivity is spelled out with `LinearMap.rTensor`.* Neither Mathlib nor this project
has a predicate for it, so the hypothesis is `∀ T, Function.Injective (f.rTensor T)`, exactly as in
Stacks 058K (1), 058L, 058M and 059N. `Function.Injective f` is not assumed separately: it is the
case `T = R` of `hf`, so assuming it would be assuming a consequence of another hypothesis.

*The Mittag-Leffler property is spelled out.* Mathlib has no predicate for a Mittag-Leffler module
(`CategoryTheory.Functor.IsMittagLeffler` is the condition on an inverse system, condition (4) of
Stacks 059E), so `hML` is written inline in the intrinsic form 059E (1) — every map `g : P → N`
from a finitely presented module dominates and is dominated by a map `h : P → Q` into a finitely
presented module, domination meaning `Ker(g ⊗ id_T) = Ker(h ⊗ id_T)` for every `R`-module `T` — the
spelling of Stacks 059M, 059N, 059P, 059R, 059X, 059Z, 05CQ, 05D6 and 0AS7.

*"`M` is a direct sum of countably generated `R`-modules" is spelled internally,* as in Stacks
058W, 058X, 058Y, 059Z and 05D6: a set `S` of submodules of `M` which is independent (`sSupIndep`)
and has supremum `⊤`, each member of which is spanned by a countable subset of `M`. Independence
together with `sSup S = ⊤` says that the canonical map `⨁ K : S, K → M` is an isomorphism, by
`sSupIndep_iff` and `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, and conversely
the images of the summands under an isomorphism `M ≅ ⨁_{i ∈ I} K_i` form such a set; countable
generation as a countable spanning set in the ambient module, `∃ t : Set M, t.Countable ∧
span R t = K`, is the form of Stacks 0590, 058W, 058X, 058Y, 059Z and 05A3, equivalent to countable
generation of `↥K` as a module, spanning sets matching along `K.subtype`.

*Flatness of `N` is the instance `Module.Flat R N`* and the conclusion is `Module.Projective R M`,
as in Stacks 059X.

*Universes.* `M`, `N`, the test module `T` of universal injectivity and the modules `P`, `Q`, `T`
of the Mittag-Leffler condition all live in `Type v`, with `R : Type u` assumed `Small.{v}`, the
convention of Stacks 058K, 059E, 059M, 059N, 059X, 059Z and 05CQ. This is no weakening:
`Small.{v} R` is automatic when `v = max u v`, in particular whenever `R` and the modules share a
universe, so the single-universe statement is the instance `v := max u v`. It is also what makes
the `Type v` quantifiers the source's quantifiers over all modules, domination being testable on
the finitely presented modules of `Type v` alone (Stacks 059C).

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead. `hf` carries both properties of `N` to `M`; `Module.Flat R N` and `hML`
are what it carries, and `hM` is condition (3) of Stacks 059Z, which does not follow from the
others. Each is needed, over `R = ℤ`: without `hM`, `M = N = ℤ[[x]]` with `f = id` satisfies
everything else and is not projective (Stacks 059Y); without flatness of `N`, `M = N = ℤ/2` with
`f = id` is finitely presented, hence Mittag-Leffler (Stacks 059R (1)) and a direct sum of
countably generated modules, and is not projective; without `hML`, `M = N = ℚ` with `f = id` is
flat and countably generated but not Mittag-Leffler (Stacks 059I) and not projective; without `hf`,
`M = ℤ/2`, `N = ℤ`, `f = 0` has `N` flat and Mittag-Leffler and `M` a direct sum of countably
generated modules, with `M` not projective. `Small.{v} R` is used by `hML`, as described above.
(2) The scalars and the base are the source's: `M`, `N` and all test modules are `R`-modules, `f`,
`g` and `h` are `R`-linear, finite presentation is over `R`, every tensor product is `⊗[R]`,
flatness and projectivity are over `R`, and the members of `S` are `R`-submodules of `M` spanned
over `R`; nothing is localized or base changed.
(3) The map the source names is pinned, not merely asserted to exist: `f` is a parameter and
universal injectivity is stated of `f.rTensor T`, built from `f` itself; only the finitely
presented module `Q` and the map `h` of the Mittag-Leffler condition are existentially quantified,
as they are in Stacks 059E (1), and the decomposition of `M` is pinned as a set of submodules of
`M` rather than as an abstract isomorphism onto an external direct sum.
(4) The instantiation is not degenerate. Over `R = ℤ` take `N = ℤ[[x]]`, which is flat and
Mittag-Leffler (Stacks 059T) but not projective (Stacks 059Y), and `M = ℤ[x]` with `f` the
inclusion: `M` is the direct sum of the countably generated submodules `ℤ·xⁱ`, and the inclusion is
universally injective because a subgroup `A ≤ B` of abelian groups is pure as soon as
`A ∩ nB = nA` for every `n`, which here is the observation that a power series with `n g = f`
polynomial has `g` polynomial. So the hypotheses hold with the conclusion true and not inherited
from `N`, which fails it; the intended application, Stacks 05A1, is this shape with `ℤ[[x]]`
replaced by `R[[t₁, …, tₙ]]` over a Noetherian `R`.

## References

* [StacksProject 05A0](https://stacks.math.columbia.edu/tag/05A0)
-/



@[expose] public section

/-- Let `f : M → N` be a universally injective map of `R`-modules, that is, one for which
`f ⊗ id_T` is injective for every `R`-module `T`. Suppose `M` is a direct sum of countably
generated `R`-modules and suppose `N` is flat and Mittag-Leffler. Then `M` is projective. Being a
direct sum of countably generated modules is spelled internally, as in 058W and 058Y: an
independent set of submodules of `M` with supremum `⊤`, each spanned by a countable set. Being
Mittag-Leffler is spelled out in the intrinsic form 059E (1): every map `g : P → N` from a finitely
presented module dominates and is dominated by a map `h : P → Q` into a finitely presented module,
domination meaning `Ker(g ⊗ id_T) = Ker(h ⊗ id_T)` for every `R`-module `T`. -/
@[stacks 05A0 "Universal injectivity of `f` is injectivity of `f ⊗ id_T` for every `T`, as in
058K (1) and 059N; Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059N, 059X
and 059Z; the direct sum decomposition internally, as an independent set of submodules of `M` with
supremum `⊤`, as in 058W and 058Y, with countable generation as a countable spanning set, as in
0590. Test data in the universe of `M` and `N`, whence `Small.{v} R`. See the module docstring."]
public theorem Module.projective_of_forall_rTensor_injective_of_exists_sSupIndep_countable_span
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f.rTensor T))
    (hM : ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ K ∈ S, ∃ t : Set M, t.Countable ∧ Submodule.span R t = K)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (g : P →ₗ[R] N), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (h : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (g.rTensor T) = LinearMap.ker (h.rTensor T)) :
    Module.Projective R M :=
  Module.CountableSpanProjective.projective_of_sSupIndep_countable_span R M N f hf hM hML

end

/-!
# A direct sum of countably generated modules pure in a power series ring is projective

Let `R` be a Noetherian ring and let `M` be an `R`-module which is a direct sum of countably
generated `R`-modules and admits a universally injective map `f : M → R[[t_1, …, t_n]]`, that is,
one for which `f ⊗ id_T` is injective for every `R`-module `T`. This file proves Stacks 05A1: `M`
is projective.

The power series ring enters only as an `R`-module, namely the product of copies of `R` indexed by
the monomials in `t_1, …, t_n`, and over a Noetherian ring that module is flat and Mittag-Leffler
(Stacks 059T). Those are exactly the two properties of the target that Stacks 05A0 transports along
a universally injective map, so 05A0 applied to `f`, with the given decomposition of `M`, is the
whole proof. Neither input restricts the number of variables, so the case `n = 0`, where the
monomials form a subsingleton and the target is free of rank one, needs no separate argument.

## Main results

* `Module.MvPowerSeriesSubmodule.projective_of_mvPowerSeries`: Stacks 05A1, the statement of
  `Module.projective_of_forall_rTensor_injective_mvPowerSeries_of_exists_sSupIndep_countable_span`.

## Implementation notes

Stacks 05A0 takes flatness of the target as an instance argument and the Mittag-Leffler condition
as an ordinary one, so the conjunction of Stacks 059T is destructed and its flatness half left
anonymous in the local context: the target is flat because `R` is Noetherian, a reason instance
search cannot find in `MvPowerSeries`.

Stacks 05A0 has `R : Type u` with its modules and test data in `Type v` under `Small.{v} R`, and is
applied here at `v := u`, the universe of `R` and hence of the target, where `Small.{u} R` is
`small_self`. This is where 05A0 and 059T, which fixes `Type u` throughout, meet.

## References

* [StacksProject 05A1](https://stacks.math.columbia.edu/tag/05A1)
-/

/-!
# Projectivity of a direct sum of countably generated modules pure in a power series ring

Let `R` be a Noetherian ring and let `M` be an `R`-module which is a direct sum of countably
generated `R`-modules and admits a universally injective map `f : M → R[[t_1, …, t_n]]` for some
`n`, that is, one for which `f ⊗ id_T` is injective for every `R`-module `T` (Definition 058I).
Then `M` is projective (Stacks 05A1).

The power series ring is here only an `R`-module, namely the product of copies of `R` indexed by
the monomials in `t_1, …, t_n`, and over a Noetherian ring that module is flat and Mittag-Leffler
(Stacks 059T): flat because a Noetherian ring is coherent and over a coherent ring a product of
flat modules is flat, Mittag-Leffler because over a Noetherian ring the submodule of a finite free
`F` generated by the coordinates of an element of `F ⊗[R] R^A` is the smallest one whose tensor
product already carries that element. So the target satisfies the two hypotheses that Stacks 05A0
transports along a universally injective map, and 05A0 turns them, together with the given
decomposition of `M`, into projectivity of `M`. The target itself is in general not projective —
over `R = ℤ` and `n = 1` it is `ℤ^ℕ`, which is not even free by the Baer–Specker theorem
(Stacks 059Y) — so the conclusion is not inherited from it but produced by purity.

## Main results

* `Module.projective_of_forall_rTensor_injective_mvPowerSeries_of_exists_sSupIndep_countable_span`:
  a direct sum of countably generated modules over a Noetherian ring admitting a universally
  injective map into a power series ring in finitely many variables is projective.

## Implementation notes

*`R[[t_1, …, t_n]]` is `MvPowerSeries (Fin n) R`,* whose underlying type is the product
`(Fin n →₀ ℕ) → R` over the monomials, with its coefficientwise `R`-module structure; this is the
spelling of Stacks 059T, the lemma this one consumes, and no structure on the target beyond its
`R`-module structure is used.

*`n` is a parameter, not existentially bound.* The source says "there is a universally injective
map `M → R[[t_1, …, t_n]]` for some `n`"; since the conclusion does not mention `n` or the map,
universally quantifying both in the hypotheses is the same statement, and it pins them instead of
hiding them behind an existential. No positivity is assumed, as none is in the source: for `n = 0`
the monomials form a subsingleton, so the target is free of rank one, hence flat and projective and
therefore Mittag-Leffler by Stacks 059R (2), so that case is not excluded even though Stacks 059T
is stated for `0 < n`.

*Universal injectivity is spelled out with `LinearMap.rTensor`.* Neither Mathlib nor this project
has a predicate for it, so the hypothesis is `∀ T, Function.Injective (f.rTensor T)`, exactly as in
Stacks 058K (1), 058L, 058M, 059N and 05A0. `Function.Injective f` is not assumed separately: it is
the case `T = R` of `hf`.

*"`M` is a direct sum of countably generated `R`-modules" is spelled internally,* character for
character as in Stacks 058W, 058X, 058Y, 059Z, 05A0 and 05D6: a set `S` of submodules of `M` which
is independent (`sSupIndep`) and has supremum `⊤`, each member of which is spanned by a countable
subset of `M`. Independence together with `sSup S = ⊤` says that the canonical map `⨁ K : S, K → M`
is an isomorphism, by `sSupIndep_iff` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, and conversely the images of the
summands under an isomorphism `M ≅ ⨁_{i ∈ I} K_i` form such a set; countable generation as a
countable spanning set in the ambient module, `∃ t : Set M, t.Countable ∧ span R t = K`, is the
form of Stacks 0590, 058W, 058X, 058Y, 059Z, 05A0 and 05A3, equivalent to countable generation of
`↥K` as a module, spanning sets matching along `K.subtype`.

*Universes.* `M` and the test modules of universal injectivity lie in `R`'s universe `Type u`,
where the target `MvPowerSeries (Fin n) R` lives; this is where the two inputs meet, Stacks 059T
being stated in `Type u` and Stacks 05A0 at `v := u`, where its `Small.{v} R` is `small_self`. It
is no restriction: `hf` at `T = R` makes `f` injective, so a module `M` in any universe satisfying
the hypotheses injects into a type of `Type u` and is therefore `Small.{u}`, hence isomorphic to a
module of `Type u` along which every hypothesis and the conclusion transport.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead. `IsNoetherianRing R` is what makes the target flat and Mittag-Leffler,
the two properties `hf` transports; `hf` is what transports them, and `hM` is condition (3) of the
characterization Stacks 059Z, which is not implied by the others. Each is needed, over `R = ℤ`:
without `hM`, `M = ℤ[[t]]` with `f = id` satisfies everything else and is not projective
(Stacks 059Y); without `hf`, `M = ℤ/2` with `f = 0`, `n = 1` is a direct sum of countably generated
modules over a Noetherian ring and is not projective; and Noetherianness is the hypothesis of
Stacks 059T, which fails for suitable non-coherent `R`, its conclusion being what the proof of this
lemma consumes.
(2) The scalars and the base are the source's: `M`, the target and every test module are
`R`-modules, `f` is `R`-linear, every tensor product is `⊗[R]`, projectivity is over `R`, and the
members of `S` are `R`-submodules of `M` spanned over `R`; nothing is over the ring
`R[[t_1, …, t_n]]`, nothing is localized or base changed.
(3) The map the source names is pinned, not merely asserted to exist: `f` is a parameter and
universal injectivity is stated of `f.rTensor T`, built from `f` itself; the target is the power
series module itself rather than an abstract module isomorphic to it, and the decomposition of `M`
is pinned as a set of submodules of `M` rather than as an isomorphism onto an external direct sum.
(4) The instantiation is not degenerate. Over `R = ℤ`, Noetherian, take `n = 1` and `M = ℤ[t]` with
`f` the inclusion into `ℤ[[t]]`: `M` is the direct sum of the countably generated submodules
`ℤ·tⁱ`, and the inclusion is universally injective because a subgroup `A ≤ B` of abelian groups is
pure as soon as `A ∩ mB = mA` for every `m`, which here is the observation that a power series `g`
with `m g` polynomial is itself polynomial. So the hypotheses hold, the conclusion is true and is
not inherited from the target, which fails it, and the quantifier of `hf` is non-vacuous.

## References

* [StacksProject 05A1](https://stacks.math.columbia.edu/tag/05A1)
-/



@[expose] public section

/-- Let `R` be a Noetherian ring and let `M` be an `R`-module. Suppose `M` is a direct sum of
countably generated `R`-modules, and suppose there is a universally injective map
`f : M → R[[t_1, …, t_n]]` for some `n`, that is, one for which `f ⊗ id_T` is injective for every
`R`-module `T`. Then `M` is projective. Being a direct sum of countably generated modules is
spelled internally, as in 058W, 058Y and 05A0: an independent set of submodules of `M` with
supremum `⊤`, each spanned by a countable set. -/
@[stacks 05A1 "`R[[t_1, …, t_n]]` is `MvPowerSeries (Fin n) R` with its coefficientwise `R`-module
structure, as in 059T; universal injectivity of `f` is injectivity of `f ⊗ id_T` for every `T`, as
in 058K (1), 059N and 05A0; the direct sum decomposition internally, as an independent set of
submodules of `M` with supremum `⊤` each spanned by a countable set, as in 058W, 058Y and 05A0.
`n` and `f` are parameters rather than existentially bound, the conclusion mentioning neither, and
no positivity of `n` is assumed, as none is in the source. See the module docstring."]
public theorem
    Module.projective_of_forall_rTensor_injective_mvPowerSeries_of_exists_sSupIndep_countable_span
    (R : Type u) [CommRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (n : ℕ) (f : M →ₗ[R] MvPowerSeries (Fin n) R)
    (hf : ∀ (T : Type u) [AddCommGroup T] [Module R T], Function.Injective (f.rTensor T))
    (hM : ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ K ∈ S, ∃ t : Set M, t.Countable ∧ Submodule.span R t = K) :
    Module.Projective R M :=
  have ⟨_, hML⟩ := Module.flat_and_mittagLeffler_mvPowerSeries R n
  Module.projective_of_forall_rTensor_injective_of_exists_sSupIndep_countable_span
    R M (MvPowerSeries (Fin n) R) f hf hM hML

namespace Module.MvPowerSeriesSubmodule

/-- Let `R` be a Noetherian ring and `f : M →ₗ[R] MvPowerSeries (Fin n) R` universally injective.
If `M` is the internal direct sum of an independent set of submodules, each spanned by a countable
set, then `M` is projective. -/
public alias projective_of_mvPowerSeries :=
  Module.projective_of_forall_rTensor_injective_mvPowerSeries_of_exists_sSupIndep_countable_span

end Module.MvPowerSeriesSubmodule

end
