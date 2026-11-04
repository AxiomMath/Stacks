module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# A torsion abelian sheaf in degree zero has torsion cohomology sheaves

For a torsion abelian sheaf `F` on a site, the complex `F[0]` in the unbounded derived category
of abelian sheaves has torsion cohomology sheaves in every degree.

## Main results

* `Stacks.Torsion.torsionCohomologyProperty_singleFunctor`: the cohomology sheaves of a torsion
  abelian sheaf placed in degree zero of the derived category are torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Limits Opposite ZeroObject

universe w v u

open HomologicalComplex Opposite

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The category of abelian sheaves on `J` is abelian. -/
local instance : Abelian (Sheaf J AddCommGrpCat.{w}) :=
  CategoryTheory.sheafIsAbelian

attribute [local instance] HasDerivedCategory.standard

/-- The cohomology sheaves of a torsion abelian sheaf placed in degree zero of the unbounded
derived category are torsion. -/
public theorem torsionCohomologyProperty_singleFunctor (F : Sheaf J AddCommGrpCat.{w})
    (hF : torsionSheafProperty J F) :
    torsionCohomologyProperty J ((DerivedCategory.singleFunctor _ 0).obj F) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact (torsionSheafProperty J).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · refine (torsionSheafProperty J).prop_of_isZero ?_
    exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ i hi)
      ((DerivedCategory.homologyFunctor _ i).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app
          ((CochainComplex.singleFunctor _ 0).obj F))

end Stacks.Torsion

end
