module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryCoproducts
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Direct sums in the homotopy category of differential graded modules on a ringed site

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. The
homotopy category of right differential graded `A`-modules has arbitrary direct sums, with no
side condition: the two sheafification conditions carried by the same statement over an
arbitrary sheaf of rings are automatic over a ringed site.

## Main results

* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.hasCoproducts_ringedSite`: over a
  ringed site the homotopy category of right differential graded modules admits arbitrary direct
  sums, unconditionally.

## Implementation notes

The mathematics is entirely in
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.hasCoproducts`, which is stated over
an arbitrary sheaf of rings `R : Sheaf J RingCat` and carries
`HasWeakSheafify J AddCommGrpCat.{m}` and `J.WEqualsLocallyBijective AddCommGrpCat.{m}` — of
necessity, since a degreewise direct sum of sheaves of modules is a sheafification. This file
discharges those two conditions for `R := X.ringSheaf`, so that the hypothesis-free statement of
the source is the one which carries the tag. The products half of the same tag,
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.hasProducts`, needs neither condition
and is already hypothesis-free over an arbitrary sheaf of rings, so it is tagged where it is
proved and nothing about it is repeated here.

**Why the two conditions are automatic.** Only the site half of a ringed site is used. The
underlying category of a ringed site is an `X.C : Type u` with morphisms in `Type v`, hence
essentially small relative to any universe containing both; on a small site abelian-group
sheafification exists and inverts exactly the locally bijective maps, and both properties
transport along the equivalence with a small model, by
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`. The structure
sheaf plays no part: a ringed site is a site together with a sheaf of commutative rings, and it
is the site alone that supplies both conditions.

**The module universe.** It is `max u v m` with `m` free. That is where the two conditions hold
and it is not a restriction on the conclusion: the index type of a direct sum lies in the module
universe, exactly as for the general statement, and `m` ranges over everything, so direct sums
are obtained in every module universe containing the site. The single-universe reading of the
source is the case `u = v = w = m`. Below the site there is nothing to state: a direct sum in
`SheafOfModules.{m} X.ringSheaf` is a colimit of a diagram indexed by the covers of the site, so
for `m` smaller than the site that category does not have the colimit in the first place.

**The two sheafification derivations are local copies.**
`SheafOfModules.DifferentialGradedModule.siteHasSheafifyAddCommGrpCat` and
`SheafOfModules.DifferentialGradedModule.siteWEqualsLocallyBijectiveAddCommGrpCat` repeat
`CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat` and
`CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat` of
`StacksFrontier/Cotangent/SheavesOfRings/CotangentComplex.lean`. They are repeated rather than
imported because that module is the cotangent complex of a morphism of sheaves of rings and has
no business in this chapter; they are kept `private`, and are not registered as instances, so
that importing both modules cannot leave two copies of the same instance in scope. Unifying them
is a repo-tier move.

**`apply`, not `exact`.** The two conditions are arguments of the general statement which come
before its explicit argument, so `exact HomotopyCategory.hasCoproducts A` synthesizes them while
the module universe is still a metavariable; the two conditions do hold outright in the universe
`max u v` of the site, that solution is found, and the universe of the conclusion is then wrong.
`apply` unifies the conclusion with the goal first, which pins the module universe, and the
local instances are then the ones that answer.

## References

* [Stacks Project, Tag 0FS2](https://stacks.math.columbia.edu/tag/0FS2)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v w a m

namespace SheafOfModules

namespace DifferentialGradedModule

/-- On a small site, abelian-group sheafification inverts exactly the locally bijective maps. -/
private theorem smallSiteWEqualsLocallyBijective {D : Type m} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective AddCommGrpCat.{m} := inferInstance

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Abelian groups in a universe containing the site admit sheafification, by transport from a
small model of the site. -/
private theorem siteHasSheafifyAddCommGrpCat :
    HasSheafify J AddCommGrpCat.{max u v m} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u v m, v, u} J

/-- In a universe containing the site, abelian-group sheafification inverts exactly the locally
bijective maps, by transport from a small model of the site. -/
private theorem siteWEqualsLocallyBijectiveAddCommGrpCat :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} := by
  let : ((equivSmallModel.{max u v m} C).inverse.inducedTopology J).WEqualsLocallyBijective
      AddCommGrpCat.{max u v m} := smallSiteWEqualsLocallyBijective _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max u v m} J

end Site

namespace HomotopyCategory

/-- The homotopy category of right differential graded modules over a sheaf of differential
graded algebras on a ringed site admits arbitrary direct sums.

No side condition is carried: the two sheafification conditions of
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.hasCoproducts` are discharged here
from the essential smallness of the site. -/
@[stacks 0FS2 "homotopy_direct_sums"]
instance hasCoproducts_ringedSite {X : AlgebraicGeometry.RingedSite.{u, v, w}}
    (A : DifferentialGradedAlgebra.{w, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    HasCoproducts.{max u v m} (HomotopyCategory.{w, a, max u v m} A) := by
  let : HasSheafify X.J AddCommGrpCat.{max u v m} :=
    siteHasSheafifyAddCommGrpCat.{u, v, m} X.J
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} :=
    siteWEqualsLocallyBijectiveAddCommGrpCat.{u, v, m} X.J
  apply HomotopyCategory.hasCoproducts

end HomotopyCategory

end DifferentialGradedModule

end SheafOfModules

end
