module

public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology is local: Stacks 03P1

Let `C` be a site, `F` an abelian sheaf on `C`, `U` an object of `C`, `p > 0` an integer and
`ξ ∈ H^p(U, F)`.  [Stacks, Tag 03P1] asserts that there is a covering `{U_i → U}` of `U` in `C`
with `ξ|_{U_i} = 0` for every `i`.  The source proves it by citing
[Stacks, Tag 01FW], the same statement for a sheaf of modules on a ringed site, and that is
exactly what is done here: the abelian-sheaf form of 01FW is
`Stacks.Cohomology.Locality.cohomologyPresheaf_locally_zero` in the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero`,
and the two statements coincide once `H^p(U, F)` is read
as Mathlib's `CategoryTheory.Sheaf.H'`, the value over `U` of the cohomology presheaf.

What this file adds is the étale-cohomology chapter's reading of that lemma together with the
form in which the Čech machinery of chapter 21 consumes a covering.  `Stacks.CechSite`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/ComplexOfAFamily.lean` and its successors)
indexes the Čech complex
by a `CategoryTheory.PreZeroHypercover`, i.e. by an indexed family `{U_i → U}` with a chosen
index type, whereas Mathlib's `CategoryTheory.GrothendieckTopology.Cover` is a sieve.  The second
statement below converts between them, so that the covering produced by locality of cohomology
can be fed straight to a Čech complex.

## Main results

* `Stacks.CechComparison.exists_cover_restriction_eq_zero`: [Stacks, Tag 03P1] in its sieve
  form — a positive-degree cohomology class over `U` is killed by restriction along every
  member of some covering of `U`.
* `Stacks.CechComparison.exists_preZeroHypercover_restriction_eq_zero`: the same with the
  covering presented as an indexed family `{U_i → U}` whose generated sieve is a covering,
  which is the shape the Čech complex of a family is built on.

## Implementation notes

The hypothesis `0 < p` is essential and is the source's: in degree zero `H^0(U, F) = F(U)` and
a nonzero section is killed by no covering.

Both statements are about an arbitrary abelian sheaf on a small site, which is the source's
convention; no ring sheaf and no module structure appear, so neither statement is the
specialisation of the other — 01FW's own `@[stacks 01FW]` declaration is the module-valued one.

The index universe of `CategoryTheory.GrothendieckTopology.Cover.preOneHypercover` is `max u v`,
which for a small category is the single universe `u`; this is why the family form is stated at
one universe variable rather than at an independent index universe.

## References

* [Stacks Project, Tag 03P1](https://stacks.math.columbia.edu/tag/03P1)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.CechComparison

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}]

/-- **Stacks Project, Tag 03P1.** Cohomology is local: for an abelian sheaf `F` on a site `C`,
an object `U`, a degree `p > 0` and a class `ξ ∈ H^p(U, F)`, there is a covering
`{U_i → U}` of `U` such that `ξ|_{U_i} = 0` for every member `i` of the covering.

Here `H^p(U, F)` is `CategoryTheory.Sheaf.H' F p U`, the value over `U` of the cohomology
presheaf of `F`, and the restriction maps are the functoriality of that presheaf. -/
@[stacks 03P1]
theorem exists_cover_restriction_eq_zero (F : Sheaf J AddCommGrpCat.{u}) (p : ℕ) (hp : 0 < p)
    (U : C) (ξ : Sheaf.H' F p U) :
    ∃ S : J.Cover U, ∀ g : S.Arrow, (F.cohomologyPresheaf p).map g.f.op ξ = 0 :=
  Stacks.Cohomology.Locality.cohomologyPresheaf_locally_zero F p hp U ξ

/-- **Stacks Project, Tag 03P1, in the indexed-family form.** The covering produced by locality
of cohomology may be presented as a `CategoryTheory.PreZeroHypercover`, i.e. as an indexed
family `E = {U_i → U}` whose generated sieve `E.sieve₀` is a covering of `U`, with
`ξ|_{U_i} = 0` for every index `i`.

This is the shape in which the Čech complex of chapter 21 takes its covering, so it is this
form that pairs with the Čech-to-cohomology comparison. -/
theorem exists_preZeroHypercover_restriction_eq_zero (F : Sheaf J AddCommGrpCat.{u}) (p : ℕ)
    (hp : 0 < p) (U : C) (ξ : Sheaf.H' F p U) :
    ∃ E : PreZeroHypercover.{u} U, E.sieve₀ ∈ J U ∧
      ∀ i : E.I₀, (F.cohomologyPresheaf p).map (E.f i).op ξ = 0 := by
  obtain ⟨S, hS⟩ := exists_cover_restriction_eq_zero F p hp U ξ
  refine ⟨S.preOneHypercover.toPreZeroHypercover, ?_, hS⟩
  rw [show S.preOneHypercover.toPreZeroHypercover.sieve₀ = S.preOneHypercover.sieve₀ from rfl,
    S.preOneHypercover_sieve₀]
  exact S.2

end Stacks.CechComparison

end
