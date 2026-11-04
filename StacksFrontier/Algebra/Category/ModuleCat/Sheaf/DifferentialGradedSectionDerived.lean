module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionHomotopy

/-!
# Derived sections on a chaotic site

Let `C` be a category, viewed as a site with the chaotic topology, let `O` be a sheaf of rings on
it and let `(A, d)` be a sheaf of differential graded `O`-algebras. Taking sections over an
object `U` of `C` descends to the derived categories: there is a functor

`RΓ(U, -) : D(A, d) ⥤ D(A(U), d)`

whose value on the class of a right differential graded `A`-module `M` is the class of the
differential graded `A(U)`-module `M(U)` of its sections.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedSections`: the derived sections functor
  `RΓ(U, -) : D(A, d) ⥤ D(A(U), d)`.
* `SheafOfModules.DifferentialGradedModule.derivedSectionsFactorization`: the canonical
  isomorphism exhibiting it as the descent of taking sections on the homotopy categories.
* `SheafOfModules.DifferentialGradedModule.derivedSectionsIsoSectionClass`: the value of
  `RΓ(U, -)` on the class of a right differential graded module is the class of its sections.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isInvertedBy_sectionHomotopyFunctor`:
  taking sections over `U` inverts the quasi-isomorphisms of the homotopy category.

## Implementation notes

The derived category is the localization of the homotopy category at the quasi-isomorphisms, and
`derivedSections` is the functor `CategoryTheory.Localization.lift` provides.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 09KX](https://stacks.math.columbia.edu/tag/09KX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ)

/-- On a chaotic site, taking sections over `U` followed by the localization functor to
`D(A(U), d)` inverts the quasi-isomorphisms of right differential graded `A`-modules. -/
theorem quasiIsomorphisms_isInvertedBy_sectionHomotopyFunctor :
    (quasiIsomorphisms.{t, a, a} A).IsInvertedBy
      (sectionHomotopyFunctor A U ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q) := by
  rintro ⟨M⟩ ⟨N⟩ φ hφ
  induction φ using Quot.inductionOn with
  | h g =>
      exact Localization.inverts
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)) _
        (quasiIsomorphisms_sectionMap g U (hφ g rfl))

/-- The derived sections functor `RΓ(U, -) : D(A, d) ⥤ D(A(U), d)` of a chaotic site: the
descent of taking sections over `U` through the localization of the homotopy category at the
quasi-isomorphisms. -/
def derivedSections : derivedCategory.{t, a, a} A ⥤
    _root_.DifferentialGradedModule.derivedCategory' (A.sectionAlgebra U) :=
  Localization.lift _ (quasiIsomorphisms_isInvertedBy_sectionHomotopyFunctor A U)
    (quasiIsomorphisms.{t, a, a} A).Q

/-- Derived sections are sections read through the localizations: the square of homotopy and
derived categories commutes up to this canonical isomorphism. -/
def derivedSectionsFactorization :
    (quasiIsomorphisms.{t, a, a} A).Q ⋙ derivedSections A U ≅
      sectionHomotopyFunctor A U ⋙
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q :=
  Localization.fac _ (quasiIsomorphisms_isInvertedBy_sectionHomotopyFunctor A U) _

/-- The derived sections of the class of a right differential graded module are the class of
its sections: `RΓ(U, M) = M(U)` on a chaotic site. -/
def derivedSectionsIsoSectionClass (M : DifferentialGradedModule.{t, a, a} A) :
    (derivedSections A U).obj
        ((toDerivedCategory.{t, a, a} A).obj ((HomotopyCategory.quotient A).obj M)) ≅
      Chaotic.sectionClass M U :=
  (derivedSectionsFactorization A U).app ((HomotopyCategory.quotient A).obj M) ≪≫
    (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q.mapIso
      ((sectionHomotopyFunctorIso A U).app M)

end DifferentialGradedModule

end SheafOfModules

end
