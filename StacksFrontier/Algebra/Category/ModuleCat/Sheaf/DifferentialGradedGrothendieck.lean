module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedFilteredColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafModulesGrothendieck

/-!
# Differential graded modules form a Grothendieck abelian category

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of differential graded
`R`-algebras. [Stacks, Tag 0FS9](https://stacks.math.columbia.edu/tag/0FS9) says that the
category `Mod(A, d)` of right differential graded `A`-modules is a Grothendieck abelian
category.

Mathlib's `CategoryTheory.IsGrothendieckAbelian.{s} C` for an abelian `C` asks for four things:
that `C` be locally small relative to `s`, that it have filtered colimits of size `s`, that
those be exact (AB5), and that it have a separator. Three of the four are Tag 0FRJ and are
already available: the abelian structure is
`SheafOfModules.DifferentialGradedModule.abelian`, the filtered colimits are
`SheafOfModules.DifferentialGradedModule.hasColimitsOfSize`, and their exactness is
`SheafOfModules.DifferentialGradedModule.filteredColimits_exact`. What this file adds is the
separator, and then assembles the four.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasSeparator`: **right differential graded modules
  have a separator**, namely `⨁_{k, U} j_{U!} C_U[k]`, where `C_U` is the cone on the identity
  of the restriction of `A` to the object `U` of the site.
* `SheafOfModules.DifferentialGradedModule.isGrothendieckAbelian` is **Tag 0FS9**: the category
  of right differential graded modules over a sheaf of differential graded algebras is a
  Grothendieck abelian category.

## Implementation notes

**The separator is the tag's own object.** Tag 0FS9 exhibits the generator
`⨁_{k, U} j_{U!} C_U[k]`, where `C_U = C(id : A_U → A_U)` is the cone on the identity of the
regular module over the restriction of `A` to `U`, and computes

`Hom_{Mod(A, d)}(j_{U!} C_U[k], M) = {(x, y) ∈ M^{-k}(U) × M^{-k-1}(U) | x = d y}`

by Tag 0FS8. Below, that object is produced by applying the *differential graded hull* functor
— the left adjoint of forgetting the differential, Tag 0FSK, built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetRightAdjoint.lean` — to the separator
`⨁_{k, U} j_{U!} A_U[k]` of right graded modules of Tag 0FRD
(`SheafOfModules.GradedModule.hasSeparator`). This produces the same object: a left adjoint
preserves direct sums, and the hull of `j_{U!} A_U[k]` is `j_{U!} C_U[k]`, since the hull of a
graded module `N` is `Nⁿ⁻¹ ⊕ Nⁿ` in degree `n` with differential `(x, y) ↦ (0, x)`, which for
`N` free on one generator is exactly the cone on the identity. The displayed Hom-formula is the
adjunction's hom-bijection composed with Tag 0FRD's corepresentation formula
`Hom_{Mod(A)}(j_{U!} A_U[k], M) = Γ(U, M^k)`; `CategoryTheory.HasSeparator.of_adjunction`
packages exactly that step, its faithfulness hypothesis being
`SheafOfModules.DifferentialGradedModule.forgetToGradedModule_faithful`.

**Hypotheses on the site.** Tag 0FRJ defers the exactness of `Mod(O)` to Cohomology on Sites,
resting on the standing convention that a site admits sheafification; in Lean that convention is
not automatic. So `HasSheafify J AddCommGrpCat.{max u v a w}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{max u v a w}` — the two conditions that make
`SheafOfModules.{max u v a w} R` abelian with exact filtered colimits — are hypotheses, exactly
as in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedModuleAbelian.lean`; and
`HasWeakSheafify J (Type max u v a w)` is the sheafification of sheaves of *sets* used by Tag
0FRD's separating family, whose members are free modules on the sheafified representable of an
object of the site.

**Universes.** The statement is at module universe `max u v a w`, for a site `C : Type u` with
`Category.{v} C` and algebra pieces in `SheafOfModules.{a} R`, with `w` free; this is the shape
already forced in the graded case by
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafModulesGrothendieck.lean` and it is inherited
here unchanged, because the separator is transported from there. Nothing in it is a choice:
`LocallySmall.{s}` needs the hom types of `Mod(A, d)` — which are indexed by the objects of `C`
and valued in the module universe — to be `s`-small, so `u ≤ s`; a direct sum indexed by a type
in `Type s` exists only for `s` the module universe, and the separating family is indexed by
pairs `(U, k)` with `U` an object of `C`, so again `u ≤ s`; the free graded module on a sheaf of
graded sets with values in `Type s` has pieces in `Type (max s a)`, so `a ≤ s`; and the
sheafified representable of an object of `C` takes values in `Type (max v s')`, so `v ≤ s`. The
source works over a ringed site, where the site is small and all of these collapse; a ringed
site `X` is the case `R := X.ringSheaf`.

**Generality.** The base is an arbitrary sheaf of rings on an arbitrary site rather than the
structure sheaf of a ringed site, and the universes of the site, the ring and the algebra pieces
are independent.

## References

* [Stacks Project, Tag 0FS9](https://stacks.math.columbia.edu/tag/0FS9)
* [Stacks Project, Tag 0FS8](https://stacks.math.columbia.edu/tag/0FS8)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD)
* [Stacks Project, Tag 0FSK](https://stacks.math.columbia.edu/tag/0FSK)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w a t v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J (Type max u v a w)]
  [HasSheafify J AddCommGrpCat.{max u v a w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v a w}]

/-- **Right differential graded modules over a sheaf of differential graded algebras have a
separator**, namely the direct sum `⨁_{k, U} j_{U!} C_U[k]` of the shifts of the cones on the
identities of the restrictions of the algebra to the objects of the site.

It is obtained by applying the differential graded hull — the left adjoint of the faithful
functor forgetting the differential — to the separator `⨁_{k, U} j_{U!} A_U[k]` of right graded
modules. -/
noncomputable instance hasSeparator (A : DifferentialGradedAlgebra.{t, a} R) :
    HasSeparator (DifferentialGradedModule.{t, a, max u v a w} A) :=
  haveI := forgetToGradedModule_faithful.{t, a, max u v a w} A
  HasSeparator.of_adjunction (dgHullAdjunction A)

/-- **Stacks Project, Tag 0FS9.** Let `(C, O)` be a ringed site and let `(A, d)` be a
differential graded `O`-algebra. The category `Mod(A, d)` of right differential graded
`A`-modules is a Grothendieck abelian category.

It is abelian and has filtered colimits by Tag 0FRJ, those colimits are exact by
`filteredColimits_exact`, it is locally small, and it has the separator
`⨁_{k, U} j_{U!} C_U[k]`, the direct sum of the shifts of the cones on the identities of the
restrictions of `A` to the objects of the site. -/
@[stacks 0FS9]
noncomputable instance isGrothendieckAbelian (A : DifferentialGradedAlgebra.{t, a} R) :
    IsGrothendieckAbelian.{max u v a w} (DifferentialGradedModule.{t, a, max u v a w} A) where
  ab5OfSize :=
    filteredColimits_exact.{max u v a w, max u v a w, max u v a w, a, t, v, u} A
  hasSeparator := DifferentialGradedModule.hasSeparator A

end DifferentialGradedModule

end SheafOfModules

end
