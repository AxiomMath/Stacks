module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero is left adjoint to restriction on derived categories

Let `(C, O)` be a ringed site and `U` an object of `C`. Extension by zero `j_!` and restriction
`j^*` to the slice site `C/U` are both exact, so they induce functors on unbounded derived
categories, and the adjunction `j_! ⊣ j^*` of Stacks 03DI descends to them. When the unit of
the abelian adjunction is an isomorphism — over a subterminal `U`, for instance over every open
of a topological space — so is the unit of the derived one: `j^* j_! = id` on `D(O_U)`.

## Main definitions

* `Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction`: the adjunction
  `j_! ⊣ j^*` on derived categories.

## Main results

* `StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_unit`: an adjunction of exact
  functors with invertible unit induces one with invertible unit on derived categories.
* `Stacks.DerivedTensor.ExtensionByZero.isIso_derivedAdjunction_unit`: the derived unit
  `Z ⟶ (j_! Z)|_U` is an isomorphism over a subterminal `U`.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DerivedTensor.RingedSite (Modules)

namespace StacksDraft.DerivedRingIso

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived unit is invertible when the abelian unit is.** On the class of a complex `X`
the unit of `mapDerivedCategoryAdjunction adj` is the class of the degreewise unit at `X`,
conjugated by the two factorization isomorphisms; every object of the derived category is
isomorphic to such a class. -/
theorem isIso_mapDerivedCategoryAdjunction_unit (adj : F ⊣ G) (hadj : IsIso adj.unit) :
    IsIso (mapDerivedCategoryAdjunction adj).unit := by
  have hQ : ∀ X : CochainComplex C ℤ,
      IsIso ((mapDerivedCategoryAdjunction adj).unit.app (DerivedCategory.Q.obj X)) := by
    intro X
    have h : (mapDerivedCategoryAdjunction adj).unit.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app X) ≫
          G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
      simp only [mapDerivedCategoryAdjunction, Adjunction.localization_unit_app]
      rfl
    have : IsIso ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app X) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (asIso adj.unit)
        (ComplexShape.up ℤ)).hom.app X))
    rw [h]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let e := DerivedCategory.Q.objObjPreimageIso Y
  have := hQ (DerivedCategory.Q.objPreimage Y)
  have : IsIso ((𝟭 (DerivedCategory C)).map e.hom ≫
      (mapDerivedCategoryAdjunction adj).unit.app Y) := by
    rw [(mapDerivedCategoryAdjunction adj).unit.naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((𝟭 (DerivedCategory C)).map e.hom) _

end StacksDraft.DerivedRingIso

namespace Stacks.DerivedTensor.ExtensionByZero

universe d u

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]

/-- **Extension by zero is left adjoint to restriction on unbounded derived categories**: the
adjunction `j_! ⊣ j^*` of Stacks 03DI, descended along the localizations at the
quasi-isomorphisms, both functors being exact. -/
@[sga "4 XVII 5.1.3" "special case"]
def derivedAdjunction :
    (extension X U).mapDerivedCategory ⊣ (restriction X U).mapDerivedCategory :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryAdjunction
    (Stacks.SheafOfModules.ExtensionByZero.extensionByZeroAdjunction X U)

/-- **`j^* j_! = id` on derived categories over a subterminal object**: the unit of
`Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction` is an isomorphism when `U` is
subterminal, which holds for every open of a topological space
(`Stacks.SheafOfModules.ExtensionByZero.isIso_forgetAdjStar_unit_opens`). -/
theorem isIso_derivedAdjunction_unit [HasBinaryProducts X.C]
    [IsIso (Over.forgetAdjStar U).unit] :
    IsIso (derivedAdjunction X U).unit :=
  StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_unit _
    (Stacks.SheafOfModules.ExtensionByZero.isIso_extensionByZeroAdjunction_unit X U)

end Stacks.DerivedTensor.ExtensionByZero
