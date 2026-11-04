module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFilteredColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The category of differential graded modules on a ringed site

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of differential graded
`R`-algebras. [Stacks, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ) collects the basic
categorical properties of the category `Mod(A, d)` of right differential graded `A`-modules:
it is abelian, it has

1. arbitrary direct sums,
2. arbitrary colimits,
3. exact filtered colimits,
4. arbitrary products,
5. arbitrary limits,

and the functor `Mod(A, d) ⥤ Mod(A)` sending a differential graded module to its underlying
graded module commutes with all limits and all colimits.

## Main results

* `SheafOfModules.differentialGradedModule_abelian_ab5_hasLimits_hasColimits_forget` is the
  whole of Tag 0FRJ: the seven assertions above about `Mod(A, d)`, together with the two
  commutation statements for the functor forgetting the differential.

## Implementation notes

Each clause is already available separately, and this file only assembles them:

* abelianness is `SheafOfModules.DifferentialGradedModule.abelian`, whose kernels and
  cokernels are degreewise and whose coimage-image comparison is checked after forgetting the
  differential;
* direct sums are `SheafOfModules.DifferentialGradedModule.hasCoproducts`, formed degreewise;
* colimits are `SheafOfModules.DifferentialGradedModule.hasColimitsOfSize`, direct sums
  together with the coequalizers of the abelian structure;
* exactness of filtered colimits is
  `SheafOfModules.differentialGradedModule_ab5`, transported from the graded case along the
  functor forgetting the differential;
* products are `SheafOfModules.DifferentialGradedModule.hasProducts`, formed degreewise, and
  limits follow from them with the equalizers of a preadditive category with kernels;
* the two commutation statements are
  `SheafOfModules.forgetToGradedModule_preservesLimitsOfSize` and
  `SheafOfModules.forgetToGradedModule_preservesColimitsOfSize`: forgetting the differential is
  simultaneously a left adjoint (to the cofree differential graded module) and a right adjoint
  (to the differential graded hull).

**Abelianness as a proposition.** `CategoryTheory.Abelian C` is data in Mathlib, a `Type`
rather than a `Prop`, so the assertion that a category is abelian is the inhabitedness
`Nonempty (Abelian C)`. This matches the differential graded algebra statement of Tag 09JJ,
`DifferentialGradedModule.differentialGradedModule_abelian`, which is the same sentence over a
ring rather than over a ringed site.

**Universes.** The site universes `u`, `v`, the ring universe `t`, the algebra universe `a` and
the module universe `m` are independent. Colimits, direct sums, products, limits and the
exactness of filtered colimits are stated at the size of the module universe, which is where
`SheafOfModules.{m} R` itself is cocomplete. The two commutation statements for the forgetful
functor hold at an arbitrary pair of size universes `s₁`, `s₂`, since they come from
adjunctions; they are stated that way rather than at `(m, m)`.

**Sheafification.** The sheafification of presheaves of abelian groups whose sections lie in
the module universe, and the identification of the local isomorphisms with the morphisms
becoming isomorphisms after sheafification, are what make `Mod(O)` cocomplete and abelian in
Mathlib's setting; they appear as the instance arguments `HasSheafify` and
`WEqualsLocallyBijective`, exactly as in the rest of the chapter. The Stacks Project obtains
them from Cohomology on Sites, Section 21.3. They are found by instance search whenever the
site is small and the module universe is the site's own, so for `C : Type u` with
`Category.{u} C` and `m := u` the theorem below reads with no instance argument left to supply;
the free module universe `m` is what keeps it more general than that case.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
* [Stacks Project, Tag 0FSK](https://stacks.math.columbia.edu/tag/0FSK)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe s₁ s₂ t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- **Stacks 0FRJ.** Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of
differential graded `R`-algebras. The category `Mod(A, d)` of right differential graded
`A`-modules is abelian and has

1. arbitrary direct sums,
2. arbitrary colimits,
3. exact filtered colimits,
4. arbitrary products,
5. arbitrary limits,

and the functor `Mod(A, d) ⥤ Mod(A)` forgetting the differential commutes with all limits and
with all colimits.

Abelianness is phrased as `Nonempty (Abelian _)` because `CategoryTheory.Abelian` is data; the
seven remaining clauses are propositions on the nose. -/
@[stacks 0FRJ]
theorem differentialGradedModule_abelian_ab5_hasLimits_hasColimits_forget
    (A : DifferentialGradedAlgebra.{t, a} R)
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    Nonempty (Abelian (DifferentialGradedModule.{t, a, m} A)) ∧
      HasCoproducts.{m} (DifferentialGradedModule.{t, a, m} A) ∧
      HasColimitsOfSize.{m, m} (DifferentialGradedModule.{t, a, m} A) ∧
      AB5OfSize.{m, m} (DifferentialGradedModule.{t, a, m} A) ∧
      HasProducts.{m} (DifferentialGradedModule.{t, a, m} A) ∧
      HasLimitsOfSize.{m, m} (DifferentialGradedModule.{t, a, m} A) ∧
      PreservesLimitsOfSize.{s₁, s₂} (forgetToGradedModule.{t, a, m} A) ∧
      PreservesColimitsOfSize.{s₁, s₂} (forgetToGradedModule.{t, a, m} A) := by
  have hEq : HasEqualizers (DifferentialGradedModule.{t, a, m} A) :=
    Preadditive.hasEqualizers_of_hasKernels
  exact ⟨⟨DifferentialGradedModule.abelian⟩, inferInstance, inferInstance,
    differentialGradedModule_ab5 A, inferInstance,
    has_limits_of_hasEqualizers_and_products, inferInstance, inferInstance⟩

end SheafOfModules

end
