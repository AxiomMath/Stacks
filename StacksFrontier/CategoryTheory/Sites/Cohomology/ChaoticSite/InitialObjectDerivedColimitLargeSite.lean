module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionLargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.InitialObjectDerivedColimit
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` is underived at a chaotic site with an initial object, with no smallness hypothesis

Let `C` be a category with an initial object `I`, carrying the chaotic topology, whose objects and
whose morphisms may live in different universes. The lower shriek `π_!` of Tag 08PF is the colimit
over `Cᵒᵖ`, and `Cᵒᵖ` has the terminal object `op I`, so `π_!` is evaluation at `I` and is
therefore exact. This file records the resulting

`Lπ_!(ℱ) = π_!(ℱ)`

in `D(Ab)`, for every abelian presheaf `ℱ` on `C`.

`Stacks.ChaoticSite.isZero_leftDerivedColimit_succ_of_isInitial` and
`Stacks.ChaoticSite.leftDerivedColimitZeroIsoColimit` say the same thing degreewise, but only for
a small `C`: they route through the degreewise form of the criterion of Tag 08Q9, which asks for a
small site. The derived-category form of that criterion carries no smallness hypothesis, so this
file's statement does not either.

## Main results

* `Stacks.ChaoticSite.AbelianValued.totalDerivedColimitSingleIsoOfIsInitial`: `Lπ_!(ℱ)` is the
  complex concentrated in degree zero on `π_!(ℱ) = colim ℱ`.

## Implementation notes

Nothing is reproved. The criterion of Tag 08Q9 applied to the constant cosimplicial object at `I`
-- a point resolution by `Stacks.ChaoticSite.isPointResolution_const_of_isInitial` -- presents
`Lπ_!(ℱ)` as the extended Moore complex of `ℱ(U_•)`, and that complex's augmentation to
`(π_!ℱ)[0]` is a quasi-isomorphism by
`Stacks.ChaoticSite.quasiIso_mooreCochainAugmentationConst`, which is where the initial object is
used twice: `ℱ(U_•)` is constant, so there is no positive homology, and the colimit injection at
`U_0 = I` is an isomorphism, hence a cokernel of the degree-one differential.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08QG](https://stacks.math.columbia.edu/tag/08QG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

universe v u

namespace Stacks.ChaoticSite.AbelianValued

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C]
  [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max v u})]

/-- **`Lπ_!(ℱ) = π_!(ℱ)` at a chaotic site with an initial object**, with no smallness hypothesis:
`Lπ_!(ℱ)` is the complex concentrated in degree zero on the colimit of `ℱ` over `Cᵒᵖ`, which is
`π_!(ℱ)` by Tag 08PF.

The objects of `C` and its morphisms may live in different universes; the coefficients are read at
`max v u`, the smallest universe in which `Cᵒᵖ` has colimits of abelian groups. The degreewise form
for a small site is `Stacks.ChaoticSite.leftDerivedColimitZeroIsoColimit` together with
`Stacks.ChaoticSite.isZero_leftDerivedColimit_succ_of_isInitial`. -/
def totalDerivedColimitSingleIsoOfIsInitial {I : C} (hI : IsInitial I)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v u}) :
    (totalDerivedColimit' C AddCommGrpCat.{max v u}).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{max v u})
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single AddCommGrpCat.{max v u} (ComplexShape.up ℤ) 0).obj
          (colimit F)) :=
  haveI := quasiIso_mooreCochainAugmentationConst hI F
  ((mooreCochainNatIsoDerivedColimitOfLarge ((Functor.const SimplexCategory).obj I)
      (isPointResolution_const_of_isInitial hI)).app F).symm ≪≫
    asIso (DerivedCategory.Q.map
      ((GeneralValued.mooreCochainAugmentation'
        ((Functor.const SimplexCategory).obj I)).app F))

end Stacks.ChaoticSite.AbelianValued

end
