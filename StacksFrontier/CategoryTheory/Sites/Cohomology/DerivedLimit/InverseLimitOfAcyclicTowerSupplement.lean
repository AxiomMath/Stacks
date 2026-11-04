module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomComplexAugmentation
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower

/-!
# Additions to `InverseLimitOfAcyclicTower`

Declarations extending the module above, kept in their own module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite

universe u v w z g

namespace Stacks.Cohomology.SiteInverseLimits

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, v, w})

section Instances

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- Sheaves of modules on a ringed site have enough injectives, being Grothendieck abelian. -/
local instance enoughInjectives_sheafOfModules_of_isGrothendieckAbelian :
    EnoughInjectives (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  IsGrothendieckAbelian.enoughInjectives.{g}

end Instances

section Cover

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

end Cover


section Cover2

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Placing modules in degree zero preserves a countable product of modules that are acyclic on
a covering class.** If every object of the site has a covering by members of `B` and each `Mₙ`
has no higher cohomology on the members of `B`, then the product `∏ Mₙ`, placed in degree zero,
is a product of the `Mₙ` placed in degree zero in the derived category: the ordinary product of
sheaves is the derived product. -/
theorem preservesLimit_singleFunctor_of_acyclic_cover
    (M : ℕ → SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hcoh : ∀ U, B U →
      letI : (SheafOfModules.evaluation.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).Additive :=
        Stacks.SheafOfModules.evaluationAdditive.{z}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (op U);
      ∀ n p : ℕ, 0 < p →
      IsZero (((sectionsFunctor.{u, v, w, z} X U).rightDerived p).obj (M n))) :
    PreservesLimit (Discrete.functor M)
      (DerivedCategory.singleFunctor
        (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) :=
  preservesProduct_single_of_acyclic_cover X M B hB hcoh

end Cover2


section Cover3

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

end Cover3

section Cover4

variable [HasSheafify X.J AddCommGrpCat.{z}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

end Cover4

end Stacks.Cohomology.SiteInverseLimits

end

