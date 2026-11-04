module

public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# The cohomology group `Hⁿ(U, -)` is the `n`-th cohomology of derived sections

For a sheaf of rings `R` on a topological space and an open `U`, the abelian-group-valued
cohomology functor `Hfunctor R U n` of [Stacks, Tag 01E3] is identified with the degree-`n`
cohomology of the bounded below derived sections `RΓ(U, -)` of a module sheaf placed in degree
zero, read as an abelian group.

The identification is an isomorphism of *functors*, so it transports morphisms of module sheaves
and not only the vanishing of the groups: a statement proved about `RΓ(U, -)` in the derived
category becomes a statement about `Hgroup`, maps included.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.hfunctorIsoDerivedSectionsHomology`: the natural
  isomorphism, for a sheaf of rings on a topological space.
* `Stacks.Cohomology.ModuleComparison.hgroupIsoDerivedSectionsHomology`: its component at a
  module sheaf.
* `Stacks.Cohomology.ModuleComparison.hfunctorIsoDerivedSections` and
  `Stacks.Cohomology.ModuleComparison.hgroupIsoDerivedSections`: the same two statements for a
  scheme, phrased through `Stacks.Cohomology.derivedSections`.

## Implementation notes

Two existing comparisons are composed. `rightDerivedEvaluationForgetIso` replaces the
abelian-group-valued sections of [Stacks, Tag 01E3] by the module-valued ones, and
`Stacks.DerivedIndexing.rightDerivedIso` replaces Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived` by the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus`, which is by definition the composite of the degree-zero
single functor, the total right derived functor on `D⁺` and the degree-`n` cohomology functor.

For a scheme the total right derived functor occurring here *is*
`Stacks.Cohomology.derivedSections` and the ring of scalars *is* `Γ(X, U)`: both identifications
hold by definitional unfolding, which is why the scheme statements are proved by the same term as
the general ones.

## References

* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ModuleComparison

attribute [local instance] HasDerivedCategory.standard

/-! ### A sheaf of rings on a topological space -/

section Space

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U : Opens X)

/-- **`Hⁿ(U, -)` is the degree-`n` cohomology of derived sections over `U`.** The cohomology
functor of [Stacks, Tag 01E3] is the degree-`n` cohomology of the total right derived functor of
module-valued sections over `U`, applied to a module sheaf placed in degree zero and read as an
abelian group, naturally in the module sheaf. -/
def hfunctorIsoDerivedSectionsHomology (n : ℕ) :
    Hfunctor R U n ≅
      DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} R) 0 ⋙
        (SheafOfModules.evaluation R (op U)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R.obj.obj (op U))) (n : ℤ) ⋙
            forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} :=
  (rightDerivedEvaluationForgetIso R U n).symm ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso _ n) _

/-- The component of `hfunctorIsoDerivedSectionsHomology` at a module sheaf: the group
`Hⁿ(U, F)` is the degree-`n` cohomology of `RΓ(U, F)`. -/
def hgroupIsoDerivedSectionsHomology (n : ℕ) (F : SheafOfModules.{u} R) :
    Hgroup R U n F ≅
      (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R.obj.obj (op U))) (n : ℤ)).obj
          ((SheafOfModules.evaluation R (op U)).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} R) 0).obj F))) :=
  (hfunctorIsoDerivedSectionsHomology R U n).app F

/-- The comparison transports a morphism of module sheaves: the square relating the map induced
on `Hⁿ(U, -)` to the map induced on the cohomology of derived sections commutes. -/
theorem hgroupIsoDerivedSectionsHomology_hom_naturality (n : ℕ) {F G : SheafOfModules.{u} R}
    (φ : F ⟶ G) :
    (Hfunctor R U n).map φ ≫ (hgroupIsoDerivedSectionsHomology R U n G).hom =
      (hgroupIsoDerivedSectionsHomology R U n F).hom ≫
        (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} R) 0 ⋙
          (SheafOfModules.evaluation R (op U)).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (R.obj.obj (op U))) (n : ℤ) ⋙
              forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}).map φ :=
  (hfunctorIsoDerivedSectionsHomology R U n).hom.naturality φ

end Space

/-! ### A scheme -/

section Sch

variable (X : Scheme.{u}) (U : X.Opens)

/-- **`Hⁿ(U, -)` on a scheme is the degree-`n` cohomology of `RΓ(U, -)`.** The instance of
`hfunctorIsoDerivedSectionsHomology` at the structure sheaf of a scheme, where the total right
derived functor is `Stacks.Cohomology.derivedSections` and the scalars are `Γ(X, U)`. -/
def hfunctorIsoDerivedSections (i : ℕ) :
    Hfunctor X.ringCatSheaf U i ≅
      DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙ Stacks.Cohomology.derivedSections X U ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, U)) (i : ℤ) ⋙
          forget₂ (ModuleCat.{u} Γ(X, U)) AddCommGrpCat.{u} :=
  hfunctorIsoDerivedSectionsHomology X.ringCatSheaf U i

/-- The component of `hfunctorIsoDerivedSections` at a module on a scheme: the group `Hⁱ(U, F)`
is the degree-`i` cohomology of `RΓ(U, F)`. -/
def hgroupIsoDerivedSections (i : ℕ) (F : X.Modules) :
    Hgroup X.ringCatSheaf U i F ≅
      (forget₂ (ModuleCat.{u} Γ(X, U)) AddCommGrpCat.{u}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, U)) (i : ℤ)).obj
          ((Stacks.Cohomology.derivedSections X U).obj
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F))) :=
  (hfunctorIsoDerivedSections X U i).app F

end Sch

end Stacks.Cohomology.ModuleComparison

end
