module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedZerothCohomologyDerived

/-!
# Zeroth cohomology on the derived category is a homological functor

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras. Zeroth
cohomology of a right differential graded `A`-module descends to the homotopy category
`K(Mod(A, d))` (tag 0FT2) and then, along the localization functor at the quasi-isomorphisms, to
the derived category `D(A, d)` (tag 0FT5); that descent is
`SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctor`. This file proves the
remaining assertion of tag 0FT7: the descended functor `H⁰ : D(A, d) ⥤ Mod(O)` is *homological*,
so a distinguished triangle of `D(A, d)` has an exact sequence of sheaves of `O`-modules at
`H⁰`.

## Main results

* `SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctor_isHomological`:
  **zeroth cohomology on `D(A, d)` is a homological functor.**
* Mathlib's instance `CategoryTheory.Triangulated.Localization.isTriangulated_functor`: the
  localization functor `K(Mod(A, d)) ⥤ D(A, d)` is exact.
* `SheafOfModules.DifferentialGradedModule.derivedCategory_isTriangulated`: `D(A, d)` is
  triangulated.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` and
  `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation`:
  the two properties of the quasi-isomorphisms that the pretriangulated structure on `D(A, d)`
  rests on, transported from the identification of the quasi-isomorphisms with `(acyclic A).trW`
  of tag 0FT4.

## Implementation notes

The source's proof is a one-line appeal to tag 05R7 (1), which is Mathlib's
`CategoryTheory.Functor.isHomological_of_localization`: a functor on a localized pretriangulated
category whose restriction along the localization functor is homological is itself homological,
provided the localization functor is exact and essentially surjective on arrows. The restriction
is zeroth cohomology on `K(Mod(A, d))`, homological by the second clause of tag 0FT2
(`SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor_isHomological`),
and the identification of the restriction with it is
`SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctorIso`, the factorization
clause of tag 0FT7.

What that appeal needs, and all it needs, is a pretriangulated structure on `D(A, d)`. Mathlib
puts one on a localization — `CategoryTheory.Triangulated.Localization.pretriangulated` — for a
class of morphisms admitting a left calculus of fractions and compatible with the triangulation
of the source. Both hold of the quasi-isomorphisms because they are the class `(acyclic A).trW`
attached to the triangulated subcategory of acyclic objects (tag 0FT3,
`SheafOfModules.DifferentialGradedModule.acyclic_isTriangulated`), for which Mathlib supplies
the two properties outright; that identification of the two classes is tag 0FT4,
`SheafOfModules.DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`, and
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` and
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isCompatibleWithTriangulation`
transport the two properties across it.

The base is a ringed site, as in the source, because that is the setting in which this
development has the pretriangulated structure on `K(Mod(A, d))` (tag 0FS7) and the triangulated
subcategory of acyclic objects. The hypotheses `HasSheafify X.J AddCommGrpCat.{w}` and
`X.J.WEqualsLocallyBijective AddCommGrpCat.{w}` are what make `SheafOfModules.{w} X.ringSheaf`
abelian, hence make cohomology of its cochain complexes available; they replace the source's
standing convention that a site admits sheafification.

## References

* [Stacks Project, Tag 0FT7](https://stacks.math.columbia.edu/tag/0FT7)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT3](https://stacks.math.columbia.edu/tag/0FT3)
* [Stacks Project, Tag 0FT2](https://stacks.math.columbia.edu/tag/0FT2)
* [Stacks Project, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The localization functor `K(Mod(A, d)) ⥤ D(A, d)` is essentially surjective on arrows: a
calculus of fractions presents every arrow of the localization by a fraction. -/
instance toDerivedCategory_mapArrow_essSurj :
    (toDerivedCategory.{u, v, w} A).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (toDerivedCategory.{u, v, w} A) (quasiIsomorphisms.{u, v, w} A)

/-- **Stacks Project, Tag 0FT7.** Zeroth cohomology on the derived category of `(A, d)` is a
homological functor: it takes a distinguished triangle of `D(A, d)` to an exact sequence of
sheaves of `O`-modules.

Zeroth cohomology on `D(A, d)` restricts along the localization functor to zeroth cohomology on
`K(Mod(A, d))`, which is homological by tag 0FT2, and that localization functor is exact and
essentially surjective on arrows. -/
@[stacks 0FT7 "H^0 on the derived category is a homological functor"]
instance derivedZerothCohomologyFunctor_isHomological :
    (derivedZerothCohomologyFunctor.{u, v, w} A).IsHomological :=
  Functor.isHomological_of_localization (toDerivedCategory.{u, v, w} A)
    (derivedZerothCohomologyFunctor.{u, v, w} A)
    (HomotopyCategory.zerothCohomologyFunctor.{u, v, w} A)
    (derivedZerothCohomologyFunctorIso.{u, v, w} A)

end SheafOfModules.DifferentialGradedModule

end
