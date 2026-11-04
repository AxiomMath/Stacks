module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.UnitalGlobalCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The constraints of `⊗^𝐋_{𝒪_S}` on a ringed space are natural

For a ringed space `(S, 𝒪_S)` the unit constraint on the right and the commutativity constraint
of the derived tensor product of Tag 06YU on `D(𝒪_S)` are natural transformations, not merely
isomorphisms at a pair of objects.  This discharges the hypothesis
`Stacks.Cohomology.DerivedGlobalCupProduct.AreNaturalTensorConstraints` carried by the global
cup product of a unital one-point comparison.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.areNaturalTensorConstraints`: the two constraints
  are natural.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProduct_of_isUnitalWith`: **the global
  cup product of a unital one-point comparison is a unital global cup product**, with no
  hypothesis beyond the unitality of the comparison.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct_ne_zero_of_isUnitalWith`: it is
  nonzero as soon as derived global sections are nonzero at a single object.

## Implementation notes

The naturality is read off the ringed site attached to `S` from
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality` and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso_hom_naturality`; the only
work here is to turn the uncurried action of the derived tensor bifunctor on a pair of
morphisms into the composite of its two one-variable actions.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-- **The unit constraint on the right and the commutativity constraint of `⊗^𝐋_{𝒪_S}` are
natural.**  Each is the corresponding constraint of the derived tensor product on the ringed
site attached to `S`, whose naturality comes from the Koszul symmetry and the unit law of the
total tensor product of complexes through the localization of `D(𝒪_S)` by the K-flat
complexes. -/
theorem areNaturalTensorConstraints (S : RingedSpace.{u, u}) :
    AreNaturalTensorConstraints S where
  rightUnitor_naturality {_ V} f :=
    (congrArg (fun m ↦ m ≫ (sheafRightUnitor S V).hom)
        (uncurry_map_id_right (derivedTensorProductFunctor S.sheaf) f (unitSheaf S))).trans
      (DerivedTensorProduct.rightUnitIso_hom_naturality (baseSite S)
        (canonicalDerivedTensorProduct S.sheaf) f)
  comm_naturality {_ _ _ _} f g := by
    simp only [Functor.uncurry_obj_map, Category.assoc]
    exact DerivedTensorProduct.braidingIso_hom_naturality (baseSite S)
      (canonicalDerivedTensorProduct S.sheaf) f g

/-- **The global cup product of a unital one-point comparison is a unital global cup
product.**  This is
`Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProduct_globalCupProduct` with its
naturality hypothesis discharged. -/
theorem isGlobalCupProduct_of_isUnitalWith {S : RingedSpace.{u, u}}
    {c : OnePointComparison S} {u : c.pullback.obj (unitBase S) ⟶ unitSheaf S}
    (hu : c.IsUnitalWith u) : IsGlobalCupProduct (globalCupProduct c) :=
  isGlobalCupProduct_globalCupProduct hu (areNaturalTensorConstraints S)

/-- **The global cup product of a unital one-point comparison is nonzero** as soon as
`RΓ(S, -)` is nonzero at a single object of `D(𝒪_S)`. -/
theorem globalCupProduct_ne_zero_of_isUnitalWith {S : RingedSpace.{u, u}}
    {c : OnePointComparison S} {u : c.pullback.obj (unitBase S) ⟶ unitSheaf S}
    (hu : c.IsUnitalWith u)
    {U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (hU : ¬ IsZero ((baseSections S).obj U)) : globalCupProduct c ≠ 0 :=
  globalCupProduct_ne_zero hu (areNaturalTensorConstraints S) hU

end Stacks.Cohomology.DerivedGlobalCupProduct

end
