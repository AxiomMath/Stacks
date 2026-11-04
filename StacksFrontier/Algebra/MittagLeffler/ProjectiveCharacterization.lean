module

import StacksFrontier.LinearAlgebra.DirectSum.ProjectiveCountablyGenerated
import StacksFrontier.Algebra.MittagLeffler.Projective
import StacksFrontier.Algebra.MittagLeffler.Basic
import StacksFrontier.Algebra.MittagLeffler.DirectSum
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Module.FinitePresentation


@[expose] public section

universe u v

/-!
# Projective modules are the flat Mittag-Leffler direct sums of countably generated modules

Let `R` be a commutative ring and `M` an `R`-module. This file proves Stacks 059Z: `M` is
projective if and only if `M` is flat, `M` is Mittag-Leffler, and `M` is a direct sum of countably
generated `R`-modules.

If `M` is projective it is flat (`Module.Flat.of_projective`) and Mittag-Leffler (Stacks 059R (2)),
and it is a direct sum of countably generated modules by Kaplansky's theorem (Stacks 058Y), whose
conclusion is the third condition with projectivity of the summands added.

The converse is proved summand by summand. A flat Mittag-Leffler direct sum `⨁ i, N i` of countably
generated modules is projective (`projective_directSum_of_mittagLeffler`): each `N i` is flat,
being a summand of a flat direct sum (`Module.Flat.directSum_iff`), and Mittag-Leffler, the
condition passing from a direct sum to its summands (Stacks 059P), so each `N i` is projective by
Stacks 059X and a direct sum of projective modules is projective. An independent set `S` of
submodules of `M` with `sSup S = ⊤` presents `M` as such a direct sum, the canonical map
`⨁ N : S, N → M` being an isomorphism, along which flatness and the Mittag-Leffler condition travel
back to the direct sum; and a member of `S` spanned by a countable subset of `M` is countably
generated as a module in its own right. This is
`projective_of_mittagLeffler_of_sSupIndep_countable_span`.

## Main results

* `Stacks.MittagLeffler.ProjectiveCriterion.solution`: Stacks 059Z, the statement of
  `Module.projective_iff_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span`.

## Implementation notes

The Mittag-Leffler condition, spelled out inline in the statement as condition (1) of Stacks 059E,
is `Module.IsMittagLefflerKerEq`, and it transports along a linear equivalence `e`
(`Module.mittagLeffler_of_linearEquiv`), because `e ⊗ id_T` is again an equivalence, so
precomposing with `e` changes neither side of `Ker (f ⊗ id_T) = Ker (g ⊗ id_T)`. The converse
direction needs this because Stacks 059P, which passes the condition from a direct sum to its
summands, is stated for `Mathlib`'s external `DirectSum`, whereas condition (3) is internal to `M`.

`exists_countable_span_eq_top_iff` identifies the two spellings of countable generation for a
submodule `N` of `M`: a countable subset of `M` spanning `N`, which is the form used by condition
(3) here and by Stacks 058W, 058X and 058Y, and a countable subset of `↥N` spanning `⊤`, which is
the form Stacks 059X asks for. Spanning sets match along `N.subtype` in both directions. `Mathlib`
has the second direction for the tautological presentation `N = span R t`
(`Submodule.span_span_coe_preimage`), but neither direction for a submodule presented by a spanning
set, and the statement for `Submodule.FG` in place of countable generation is missing as well.

## References

* [StacksProject 059Z](https://stacks.math.columbia.edu/tag/059Z)
-/

namespace Stacks.MittagLeffler.ProjectiveCriterion


open _root_.DirectSum

/-- A submodule `N` of `M` is countably generated as a module in its own right if and only if it is
spanned by a countable subset of `M`: spanning sets match along `N.subtype`, by taking the image
one way and the preimage the other. -/
private lemma exists_countable_span_eq_top_iff {R : Type*} {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (N : Submodule R M) :
    (∃ s : Set ↥N, s.Countable ∧ Submodule.span R s = ⊤) ↔
      ∃ t : Set M, t.Countable ∧ Submodule.span R t = N := by
  constructor
  · rintro ⟨s, hs, hsp⟩
    exact ⟨N.subtype '' s, hs.image _, by
      rw [← Submodule.map_span, hsp, Submodule.map_top, Submodule.range_subtype]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ht.preimage Subtype.val_injective, Submodule.span_span_coe_preimage⟩

/-- A flat Mittag-Leffler direct sum of countably generated `R`-modules is projective: every
summand of it is flat (`Module.Flat.directSum_iff`) and Mittag-Leffler (Stacks 059P) and countably
generated, hence projective by Stacks 059X, and a direct sum of projective modules is projective.
-/
private lemma projective_directSum_of_mittagLeffler (R : Type u) [CommRing R] [Small.{v} R]
    {ι : Type v} (N : ι → Type v) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [Module.Flat R (⨁ i, N i)] (hML : _root_.Module.IsMittagLefflerKerEq R (⨁ i, N i))
    (hcg : ∀ i, ∃ s : Set (N i), s.Countable ∧ Submodule.span R s = ⊤) :
    Module.Projective R (⨁ i, N i) :=
  have : ∀ i, Module.Projective R (N i) := fun i =>
    have := Module.Flat.directSum_iff.mp ‹Module.Flat R (⨁ i, N i)› i
    Module.Flat.projective_of_isMittagLeffler_of_countablyGenerated R (N i)
      ((isMittagLeffler_def_iff R (N i)).mpr ((Module.mittagLeffler_directSum_iff R N).mp hML i))
      (hcg i)
  inferInstance

/-- A flat Mittag-Leffler module presented as the internal direct sum of an independent set `S` of
countably generated submodules is projective. The presentation as a *set* of submodules is the form
Stacks 058W, 058X, 058Y and 0590 state their decompositions in; the equivalence with `⨁ N : S, N`
is what carries the hypotheses over to `projective_directSum_of_mittagLeffler`. -/
private lemma projective_of_mittagLeffler_of_sSupIndep_countable_span (R : Type u) [CommRing R]
    [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hML : _root_.Module.IsMittagLefflerKerEq R M) {S : Set (Submodule R M)}
    (hindep : sSupIndep S) (htop : sSup S = ⊤)
    (hcg : ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ Submodule.span R t = N) :
    Module.Projective R M := by
  classical
  let e : (⨁ N : ↥S, ↥(N : Submodule R M)) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap _)
      ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
        ⟨(sSupIndep_iff S).mp hindep, (sSup_eq_iSup' S).symm.trans htop⟩)
  have := Module.Flat.of_linearEquiv e
  have := projective_directSum_of_mittagLeffler R (fun N : ↥S => ↥(N : Submodule R M))
    (Module.mittagLeffler_of_linearEquiv e hML)
    fun N => (exists_countable_span_eq_top_iff _).mpr (hcg N N.2)
  exact Module.Projective.of_equiv e

/-- Let `R` be a commutative ring and `M` an `R`-module. Then `M` is projective if and only if (1)
`M` is flat, (2) `M` is Mittag-Leffler, and (3) `M` is a direct sum of countably generated
`R`-modules. -/
public theorem solution
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Projective R M ↔
      Module.Flat R M ∧
        (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
                [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) ∧
        (∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
          ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ Submodule.span R t = N) := by
  refine ⟨fun _ => ⟨inferInstance, Module.mittagLeffler_of_projective R M, ?_⟩,
    fun ⟨_, hML, S, hindep, htop, hcg⟩ =>
      projective_of_mittagLeffler_of_sSupIndep_countable_span R hML hindep htop hcg⟩
  obtain ⟨S, hindep, htop, hS⟩ :=
    Submodule.exists_sSupIndep_countable_span_projective_of_projective (R := R) (M := M)
  exact ⟨S, hindep, htop, fun N hN => (hS N hN).1⟩

end Stacks.MittagLeffler.ProjectiveCriterion

/-!
# Projective modules are the flat Mittag-Leffler direct sums of countably generated modules

Let `R` be a commutative ring and let `M` be an `R`-module. Then `M` is projective if and only if
`M` is flat, `M` is Mittag-Leffler, and `M` is a direct sum of countably generated `R`-modules
(Stacks 059Z). This is the theorem the whole section on Mittag-Leffler modules is built towards: an
intrinsic characterization of projectivity by three conditions, none of which mentions lifting
along a surjection.

Both directions are short given the section's work. If `M` is projective it is a direct summand of
a free module, and flatness and the Mittag-Leffler property both pass to direct summands, so (1)
and (2) hold (Stacks 059R (2), (3)); condition (3) is Kaplansky's theorem (Stacks 058Y).
Conversely, given (1)-(3), write `M` as the direct sum of countably generated submodules furnished
by (3); each summand is a direct summand of `M`, hence flat and Mittag-Leffler as well as countably
generated, so each is projective by Stacks 059X, and a direct sum of projective modules is
projective (`Module.Projective.directSum`).

## Main results

* `Module.projective_iff_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span`: a module is
  projective if and only if it is flat, Mittag-Leffler, and a direct sum of countably generated
  modules.

## Implementation notes

Mittag-Leffler is spelled out inline as condition (1) of Stacks 059E — every map `f : P → M` from a
finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely presented
module, domination meaning `Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module `T` — as in Stacks
059M, 059N, 059P, 059R, 05CQ, 05D6, 059X and 0AS7, Mathlib having no predicate for it. Test data
lives in the universe `v` of `M`, whence `Small.{v} R`: without it a finitely presented `R`-module
need not be isomorphic to one in `Type v`, the condition as written is not the source's, and the
hypothesis degenerates. This is the hypothesis carried by Stacks 059M, 059R, 05CQ, 05D6, 059X and
0AS7 for the same reason, and it holds automatically when `R` and `M` share a universe.

"`M` is a direct sum of countably generated `R`-modules" is spelled internally, exactly as in
Stacks 058W, 058X, 058Y and 05D6: a set `S` of submodules of `M` which is independent (`sSupIndep`)
and has supremum `⊤`, each member of which is spanned by a countable set. Independence together
with `sSup S = ⊤` says that the canonical map `⨁ N : S, N → M` is an isomorphism, by
`sSupIndep_iff` and `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, and conversely
the images of the summands under an isomorphism `M ≅ ⨁_{i ∈ I} N_i` form such a set; countable
generation as a countable spanning set inside the ambient module,
`∃ t : Set M, t.Countable ∧ span R t = N`, is the form used by Stacks 058W, 058X, 058Y, 05A3 and
0590, and it is equivalent to countable generation of `↥N` as a module, spanning sets matching
along `N.subtype`.

Flatness is `Module.Flat R M` and projectivity is `Module.Projective R M`; both are classes, so
both appear here as bare `Prop`s inside the biconditional rather than as instance hypotheses, which
is what an `iff` between them requires.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead, and no conjunct on the right is dead either: each of the three is
independent of the other two over `R = ℤ`. Dropping flatness is false — `ℤ/2` is finitely
presented, hence Mittag-Leffler (Stacks 059R (1)), and is a direct sum of countably generated
modules, namely itself, but is not projective. Dropping the Mittag-Leffler condition is false —
`ℤ[1/2]` is flat and countably generated, hence a direct sum of countably generated modules, but is
not free and so not projective, subgroups of free abelian groups being free. Dropping condition (3)
is false — `ℤ[[x]]` is a flat Mittag-Leffler `ℤ`-module that is not projective (Stacks 059Y).
`Small.{v} R` is used by the Mittag-Leffler conjunct, as described above.
(2) The scalars and the base are the source's: `M` is an `R`-module, flatness and projectivity are
over `R`, the test maps and their tensor products in the Mittag-Leffler condition are `R`-linear
over `R`, and the members of `S` are `R`-submodules of `M` spanned over `R`; nothing is localized
or base changed.
(3) The source names no canonical map, and what is pinned in its place is internal to `M`:
condition (3) exhibits the decomposition as an independent set of submodules of `M` with supremum
`⊤`, not merely as the existence of an abstract isomorphism of `M` onto some external direct sum of
countably generated modules.
(4) The instantiation is not degenerate. For `R = ℤ` and `M` free of uncountable rank all four
notions are satisfied, the conclusion holds, and condition (3) needs an uncountable set of
summands, so it is not witnessed by `S = {⊤}`; for `R = ℤ[√-5]` and `M` the ideal `(2, 1 + √-5)`
the module is projective and not free, so neither side is read off a basis; and `M = ℤ[[x]]` over
`ℤ` is a witness for which the right-hand side genuinely fails, at its third conjunct only, so the
biconditional is not vacuously an implication.

## References

* [StacksProject 059Z](https://stacks.math.columbia.edu/tag/059Z)
-/


/-- Let `R` be a commutative ring and `M` an `R`-module. Then `M` is projective if and only if (1)
`M` is flat, (2) `M` is Mittag-Leffler, and (3) `M` is a direct sum of countably generated
`R`-modules. Being Mittag-Leffler is spelled out in the intrinsic form 059E (1): every map
`f : P → M` from a finitely presented module dominates and is dominated by a map `g : P → Q` into a
finitely presented module, domination meaning `Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module
`T`. Being a direct sum of countably generated modules is spelled internally, as in 058W and 058Y:
an independent set of submodules of `M` with supremum `⊤`, each spanned by a countable set. -/
@[stacks 059Z "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 059N,
059P, 059R, 05CQ, 05D6 and 059X; the direct sum decomposition internally, as an independent set of
submodules of `M` with supremum `⊤`, as in 058W and 058Y, with countable generation as a countable
spanning set, as in 0590. Test data in the universe of `M`, whence `Small.{v} R`. See the module
docstring."]
public theorem Module.projective_iff_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Projective R M ↔
      Module.Flat R M ∧
        (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
                [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) ∧
        (∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
          ∀ N ∈ S, ∃ t : Set M, t.Countable ∧ Submodule.span R t = N) :=
  Stacks.MittagLeffler.ProjectiveCriterion.solution R M

end
