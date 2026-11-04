module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleModuleInjectives
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03FD on the small étale site of a scheme

Let `S` be a scheme of a big étale site `B` and let `V` be an object of its small étale site.
The cohomology over `V` of a sheaf of `𝒪`-modules, computed by deriving sections over `V` in
sheaves of `𝒪`-modules and then forgetting the module structure, is the étale cohomology
`Hⁿ(V, 𝓕_ab)` of the underlying abelian sheaf, in Mathlib's spelling
`CategoryTheory.Sheaf.H'`.

This is [Stacks, Tag 03FD] for the small étale site, whose objects live in `Type (u + 1)` while
its morphisms, its structure rings and its modules live in `Type u`: it is `EssentiallySmall.{u}`
but not a `CategoryTheory.SmallCategory`.

## Main results

* `AlgebraicGeometry.SmallEtale.rightDerivedSectionsToSheafIso`: the comparison as an
  isomorphism of functors, hence natural in the module sheaf.
* `AlgebraicGeometry.SmallEtale.toRightDerivedZero_comp_rightDerivedSectionsToSheafIso`: its
  degree-zero normalisation.
* `AlgebraicGeometry.SmallEtale.rightDerivedSectionsIsoSheafCohomology`: the comparison with
  `CategoryTheory.Sheaf.H'`, pointwise in the module sheaf.
* `AlgebraicGeometry.SmallEtale.rightDerivedEvaluationIsoSheafCohomology`: the module-valued
  derived sections over `V`, forgotten to abelian groups, are the étale cohomology `Hⁿ(V, 𝓕_ab)`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/- With the module-universe-`max u v r w` instances in the import closure, instance search for
`Abelian` on the modules at module universe `u` commits to them and then fails on the universe
constraint; the priority raise makes it find `SheafOfModules.instAbelian` first. -/
attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Deriving sections over an object `V` of the small étale site of `S` in sheaves of `𝒪`-modules
and then forgetting the module structure agrees, in every degree and naturally in the module
sheaf, with forgetting first and deriving sections over `V` of abelian sheaves. -/
public def rightDerivedSectionsToSheafIso (V : SmallEtale B S hS) (n : ℕ) :
    (SheafOfModules.toSheaf.{u} (structureSheaf B S hS) ⋙
        (sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op V)).rightDerived n ≅
      SheafOfModules.toSheaf.{u} (structureSheaf B S hS) ⋙
        ((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op V)).rightDerived n :=
  Stacks.Cohomology.ObjectSections.rightDerivedSectionsToSheafIsoOfEssentiallySmall
    (topology B S hS) (structureSheaf B S hS) V n

/-- The degree-zero normalisation of `rightDerivedSectionsToSheafIso`: the comparison
intertwines the two canonical maps to the zeroth right derived functors. -/
public theorem toRightDerivedZero_comp_rightDerivedSectionsToSheafIso (V : SmallEtale B S hS) :
    (SheafOfModules.toSheaf.{u} (structureSheaf B S hS) ⋙
          (sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op V)).toRightDerivedZero ≫
        (rightDerivedSectionsToSheafIso B S hS V 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{u} (structureSheaf B S hS))
        ((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op V)).toRightDerivedZero :=
  Stacks.Cohomology.ObjectSections.toRightDerivedZero_comp_rightDerivedSectionsToSheafIsoOfEssentiallySmall
    (topology B S hS) (structureSheaf B S hS) V

/-- **The cohomology of a sheaf of modules over an object of the small étale site is the étale
cohomology of its underlying abelian sheaf.** -/
public def rightDerivedSectionsIsoSheafCohomology (V : SmallEtale B S hS) (n : ℕ)
    (F : SheafOfModules.{u} (structureSheaf B S hS)) :
    ((SheafOfModules.toSheaf.{u} (structureSheaf B S hS) ⋙
        (sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op V)).rightDerived n).obj F ≅
      Sheaf.H'.{u} ((SheafOfModules.toSheaf.{u} (structureSheaf B S hS)).obj F) n V :=
  Stacks.Cohomology.ObjectSections.rightDerivedSectionsIsoSheafCohomologyOfEssentiallySmall
    (topology B S hS) (structureSheaf B S hS) V n F

/-- **The module-valued cohomology over an object of the small étale site, forgotten to abelian
groups, is the étale cohomology of the underlying abelian sheaf.** -/
@[sga "4 V 3.5" "special case"]
public def rightDerivedEvaluationIsoSheafCohomology (V : SmallEtale B S hS) (n : ℕ)
    (F : SheafOfModules.{u} (structureSheaf B S hS)) :
    (forget₂ (ModuleCat.{u} ((structureSheaf B S hS).obj.obj (op V))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation (structureSheaf B S hS) (op V)).rightDerived n).obj F) ≅
      Sheaf.H'.{u} ((SheafOfModules.toSheaf.{u} (structureSheaf B S hS)).obj F) n V :=
  ((Functor.rightDerivedCompIso (SheafOfModules.evaluation (structureSheaf B S hS) (op V))
          (forget₂ (ModuleCat.{u} ((structureSheaf B S hS).obj.obj (op V)))
            AddCommGrpCat.{u}) n).app F).symm ≪≫
    rightDerivedSectionsIsoSheafCohomology B S hS V n F

end AlgebraicGeometry.SmallEtale

end
