module

public import StacksFrontier.LinearAlgebra.DirectSum.CountablyGenerated

@[expose] public section

/-!
# A projective module is a direct sum of countably generated projective modules

Let `M` be a projective module over a ring `R`. This file proves Kaplansky's theorem that `M` is a
direct sum of countably generated projective `R`-modules, in the internal form: there is an
independent set of submodules of `M` with supremum `⊤`, each spanned by a countable set and each
projective over `R`.

The argument is the one of the source. A projective module is a retract of a free module: for the
canonical surjection `Finsupp.linearCombination R id : (M →₀ R) →ₗ[R] M`, projectivity provides a
section `σ`. Stacks 058X says that being a direct sum of countably generated modules passes to a
direct summand, that is, to a complemented submodule; what the corollary needs is that it passes to
a retract, and the passage from one to the other is the content of this file: the range of a
section is complemented in the ambient module, with complement the kernel of the associated
projection, and it is isomorphic to the source of the section, so Stacks 058X applies to it and
transports back along that isomorphism. A free module is the direct sum of the lines spanned by the
members of a basis, which are countably — indeed singly — generated, so the free module `M →₀ R`
satisfies the hypothesis of Stacks 058X. The projectivity of the summands is then automatic: a
member `N` of an independent set with supremum `⊤` is a direct summand of `M`, with complement the
supremum of the other members, and a direct summand of a projective module is projective.

## Main results

* `Stacks.DirectSum.ProjectiveDecomposition.solution`: the proof of Stacks 058Y, as stated in
  `Submodule.exists_sSupIndep_countable_span_projective_of_projective`.

## Implementation notes

The step which carries the content of the corollary is `exists_sSupIndep_countable_span_of_split`,
the retract form of Stacks 058X: the splitting enters as a pair of maps `p ∘ₗ i = LinearMap.id`
rather than as a complemented submodule, so that both the construction of the complement of
`LinearMap.range i` and the transport along `M ≃ₗ[R] LinearMap.range i` happen inside it. Mathlib
has neither that form nor the fact behind it, that the range of a linear map with a left inverse
is a complemented submodule.

The free module of the argument is taken to be `M →₀ R` through `Module.projective_def'`, rather
than the unspecified free module of `Module.Projective.iff_split`: the latter carries only an
`AddCommMonoid` structure, while the projection API used to produce the complement of the range of
the section (`LinearMap.isCompl_of_proj`) needs additive inverses.

The remaining steps have no Mathlib name either and are proved here as private lemmas, in the
generality in which they hold: `sSupIndep_image_orderIso`, that independence of a set of lattice
elements is preserved by an order isomorphism; `isCompl_sSup_sdiff_singleton`, that a member of an
independent set with supremum `⊤` is complemented by the supremum of the others;
`exists_sSupIndep_countable_span_of_linearEquiv`, the transport of the internal "direct sum of
countably generated submodules" predicate along a linear equivalence;
`exists_sSupIndep_countable_span_of_free`, that a free module is such a direct sum; and
`projective_of_isCompl`, that a complemented submodule of a projective module is projective — the
`IsCompl` form of `Module.Projective.of_split`.

## References

* [Stacks 058Y](https://stacks.math.columbia.edu/tag/058Y)
* I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372-377
-/

namespace Stacks.DirectSum.ProjectiveDecomposition

open Submodule

/-! ### Lattice preliminaries -/

/-- An order isomorphism carries an independent set of lattice elements to an independent set. -/
private lemma sSupIndep_image_orderIso {α β : Type*} [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) {s : Set α} (hs : sSupIndep s) : sSupIndep (e '' s) := by
  simpa [Set.range_comp] using (((sSupIndep_iff s).1 hs).map_orderIso e).sSupIndep_range

/-- A member of an independent set of lattice elements with supremum `⊤` is complemented by the
supremum of the other members. -/
private lemma isCompl_sSup_sdiff_singleton {α : Type*} [CompleteLattice α] {S : Set α} {a : α}
    (hS : sSupIndep S) (htop : sSup S = ⊤) (ha : a ∈ S) : IsCompl a (sSup (S \ {a})) :=
  ⟨hS ha, codisjoint_iff.2 <| by
    rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_self.2 ha, htop]⟩

/-! ### Direct sums of countably generated submodules -/

/-- Being an internal direct sum of countably generated submodules — an independent set of
submodules with supremum `⊤`, each spanned by a countable set — is transported along a linear
equivalence. -/
private lemma exists_sSupIndep_countable_span_of_linearEquiv {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N)
    (h : ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ K ∈ S, ∃ t : Set M, t.Countable ∧ span R t = K) :
    ∃ S : Set (Submodule R N), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ K ∈ S, ∃ t : Set N, t.Countable ∧ span R t = K := by
  obtain ⟨S, hindep, htop, hcnt⟩ := h
  refine ⟨orderIsoMapComap e '' S, sSupIndep_image_orderIso _ hindep, ?_, ?_⟩
  · rw [sSup_image, ← (orderIsoMapComap e).map_sSup, htop, (orderIsoMapComap e).map_top]
  · rintro K ⟨K₀, hK₀, rfl⟩
    obtain ⟨t, ht, hspan⟩ := hcnt K₀ hK₀
    exact ⟨e '' t, ht.image _, by rw [← hspan]; exact (map_span (e : M →ₗ[R] N) t).symm⟩

/-- A free module is the internal direct sum of the singly generated submodules spanned by the
members of a basis; in particular it is a direct sum of countably generated submodules. -/
private lemma exists_sSupIndep_countable_span_of_free {R F : Type*} [Semiring R] [AddCommMonoid F]
    [Module R F] [Module.Free R F] :
    ∃ S : Set (Submodule R F), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set F, t.Countable ∧ span R t = N := by
  let b := Module.Free.chooseBasis R F
  refine ⟨Set.range fun i => span R {b i},
    b.linearIndependent.iSupIndep_span_singleton.sSupIndep_range, ?_, ?_⟩
  · rw [sSup_range, ← span_iUnion, Set.iUnion_singleton_eq_range, b.span_eq]
  · rintro N ⟨i, rfl⟩
    exact ⟨{b i}, Set.countable_singleton _, rfl⟩

/-- A retract of a module which is an internal direct sum of countably generated submodules is
again one: the retract form of Stacks 058X. If `F` is a direct sum of countably generated
submodules and `p ∘ₗ i = LinearMap.id` for `i : M →ₗ[R] F` and `p : F →ₗ[R] M`, then `M` is a
direct sum of countably generated submodules.

The map `F → LinearMap.range i` induced by `p` restricts to the identity on `LinearMap.range i`,
so that range is complemented in `F` by the kernel of that projection and Stacks 058X makes it a
direct sum of countably generated submodules; `i` is injective, so `M` is isomorphic to it and
inherits the decomposition. -/
private lemma exists_sSupIndep_countable_span_of_split {R F M : Type*} [Ring R] [AddCommGroup F]
    [Module R F] [AddCommGroup M] [Module R M]
    (hF : ∃ S : Set (Submodule R F), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set F, t.Countable ∧ span R t = N)
    (i : M →ₗ[R] F) (p : F →ₗ[R] M) (h : p ∘ₗ i = LinearMap.id) :
    ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ span R t = N := by
  have hpi : ∀ m, p (i m) = m := fun m => congrArg (fun g : M →ₗ[R] M => g m) h
  have hinj : Function.Injective i := Function.LeftInverse.injective hpi
  have hproj : ∀ x : ↥(LinearMap.range i),
      ((LinearEquiv.ofInjective i hinj).toLinearMap ∘ₗ p) ↑x = x := by
    rintro ⟨x, m, rfl⟩
    exact Subtype.ext (by simp [hpi])
  exact exists_sSupIndep_countable_span_of_linearEquiv (LinearEquiv.ofInjective i hinj).symm
    (exists_sSupIndep_countable_span_of_isCompl hF _ _ (LinearMap.isCompl_of_proj hproj))

/-- A complemented submodule of a projective module is projective: the `IsCompl` form of
`Module.Projective.of_split`. -/
private lemma projective_of_isCompl {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] {N Q : Submodule R M} (h : IsCompl N Q) : Module.Projective R ↥N :=
  Module.Projective.of_split N.subtype (N.projectionOnto Q h) (projectionOnto_comp_subtype h)

/-! ### Kaplansky's theorem -/

/-- A projective `R`-module `M` is the internal direct sum of an independent set of submodules,
each spanned by a countable subset of `M` and each projective. -/
public theorem solution {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] :
    ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, (∃ t : Set M, t.Countable ∧ span R t = N) ∧ Module.Projective R ↥N := by
  -- `M` is a retract of the free module `M →₀ R`, by a section `σ` of the canonical map.
  obtain ⟨σ, hσ⟩ := Module.projective_def'.1 ‹Module.Projective R M›
  obtain ⟨S, hindep, htop, hcnt⟩ := exists_sSupIndep_countable_span_of_split
    exists_sSupIndep_countable_span_of_free σ (Finsupp.linearCombination R id) hσ
  -- Each summand is a direct summand of `M`, hence projective.
  exact ⟨S, hindep, htop, fun N hN =>
    ⟨hcnt N hN, projective_of_isCompl (isCompl_sSup_sdiff_singleton hindep htop hN)⟩⟩

end Stacks.DirectSum.ProjectiveDecomposition

/-!
# A projective module is a direct sum of countably generated projective modules

Let `M` be a projective module over a ring `R`. Then `M` is a direct sum of countably generated
projective `R`-modules: there is an independent set of submodules of `M` whose supremum is `⊤`,
each of them spanned by a countable set and each of them projective. This is Kaplansky's theorem
(Stacks 058Y), the result the section on transfinite dévissage is built for. It is a corollary of
the theorem that being a direct sum of countably generated modules passes to direct summands
(Stacks 058X): a projective module is a direct summand of a free module, and a free module is the
direct sum of the lines spanned by the members of a basis, which are countably — indeed singly —
generated. The projectivity of the summands is then automatic, a direct summand of a projective
module being projective. Through this theorem the freeness of projective modules reduces to the
countably generated case (Stacks 0590), which is the first step of Kaplansky's theorem that a
projective module over a local ring is free (Stacks 0593).

## Main results

* `Submodule.exists_sSupIndep_countable_span_projective_of_projective`: a projective module over a
  ring is the direct sum of a family of countably generated projective submodules.

## Implementation notes

"`M` is a direct sum of countably generated projective `R`-modules" is spelled internally, exactly
as in Stacks 058W and Stacks 058X: a set `S` of submodules of `M` which is independent
(`sSupIndep`) and has supremum `⊤`, each member of which is spanned by a countable set and is
projective. Independence together with `sSup S = ⊤` says that the canonical map `⨁ N : S, N → M` is
an isomorphism, by `sSupIndep_iff` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, and conversely the images of the
summands under an isomorphism `M ≅ ⨁_{i ∈ I} N_i` form such a set. So the conclusion here is
literally the conclusion of Stacks 058X, at `M` itself, with projectivity of the summands added.

Countable generation is written as a countable spanning set inside the ambient module,
`∃ t : Set M, t.Countable ∧ span R t = N`, the form used by Stacks 058W, 058X and 05A3; it is
equivalent to countable generation of `↥N` as a module, the preimages and images along `N.subtype`
matching spanning sets.

The projectivity of the summands is retained although it follows from the rest of the conclusion
together with the hypothesis, each `N ∈ S` being a direct summand of the projective module `M`: it
is part of the statement of the source, and it is what a user of the theorem wants supplied rather
than re-derived. It is not a strengthening obtained from extra hypotheses.

The source's commutative ring is weakened to a ring; commutativity is nowhere used, and Kaplansky's
argument is for arbitrary rings. Additive inverses are not slack: over a semiring an independent
set of submodules with supremum `⊤` need not decompose `M` (for `R = ℕ` and `M = ℕ∞` the submodules
`{0, ⊤}` and `ℕ` are disjoint with supremum `⊤`, while `⊤ = ⊤ + 0 = ⊤ + 1`), so over a semiring the
conclusion would not say what the source means, and the route through a free module needs the
inverses as well.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead. Dropping projectivity of `M` is false: over `R = ℤ` the Baer–Specker
group `M = ℤ^ℕ` is not a direct sum of countably generated subgroups, since its countable subgroups
are free (it is `ℵ₁`-free) and a direct sum of free groups is free, which Specker's theorem
forbids; `M` is not projective, projective and free agreeing over `ℤ`. The projectivity demanded of
the summands is used by the applications, Stacks 0590 discharging its hypothesis on exactly these
summands.
(2) The scalars and the base are the source's: `S` consists of `R`-submodules of `M`, each spanning
set spans over `R`, and each `↥N` is projective over `R` itself, carrying its induced `R`-module
structure; nothing is localized or base changed.
(3) The source names no canonical map, and what is pinned instead is internal to `M`: the
decomposition is by an independent set of submodules of `M` with supremum `⊤`, not merely an
abstract isomorphism of `M` onto some external direct sum of countably generated projective
modules.
(4) The instantiation is not degenerate. For `R` a field and `M` a vector space of uncountable
dimension the hypothesis holds and the conclusion needs an uncountable set of summands, so it is
not witnessed by `S = {⊤}`; for `R = ℤ[√-5]` and `M` the ideal `(2, 1 + √-5)`, `M` is projective
and not free, so the summands cannot be taken free; and taking `M` the image of an idempotent
endomorphism of a free module of uncountable rank which is not the projection onto a subfamily of
the coordinates gives an instance whose decomposition is not read off a basis, which is the content
of the theorem.

## References

* [StacksProject 058Y](https://stacks.math.columbia.edu/tag/058Y)
* I. Kaplansky, *Projective modules*, Ann. of Math. (2) 68 (1958), 372–377
-/

@[expose] public section

namespace Submodule

/-- Let `M` be a projective module over a ring `R`. Then `M` is a direct sum of countably generated
projective `R`-modules: there is an independent set of submodules of `M` with supremum `⊤`, each
spanned by a countable set and each projective over `R`. -/
@[stacks 058Y "Being a direct sum of countably generated projective modules is written internally,
  as in 058W and 058X: an independent set of submodules with supremum `⊤`, each spanned by a
  countable set and each projective. Countable generation is a countable spanning set."]
public theorem exists_sSupIndep_countable_span_projective_of_projective {R : Type*} {M : Type*}
    [Ring R] [AddCommGroup M] [Module R M] [Module.Projective R M] :
    ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, (∃ t : Set M, t.Countable ∧ span R t = N) ∧ Module.Projective R ↥N :=
  Stacks.DirectSum.ProjectiveDecomposition.solution

end Submodule

end
