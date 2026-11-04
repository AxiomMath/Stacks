module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSource
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafFromStructureSheaf

/-!
# Evaluation at the unit section, for the structure sheaf placed in degree zero

Let `O_X` be a sheaf of commutative rings on a topological space and write `O_X[0]` for the
structure sheaf, as a module over itself, placed in degree zero. There are two identifications
of the internal Hom complex `SheafHom(O_X[0], O_X[0])` with `O_X[0]`:

* `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation`, evaluation at the unit section,
  available for an arbitrary target;
* the collapse `AlgebraicGeometry.RingedSite.sheafHomComplexSingleIso` of the internal Hom
  complex of two single complexes, followed by `Hom_{O_X}(O_X, O_X) ≅ O_X` placed in degree
  zero.

They agree. This is the complex-level input to the trace description of the duality
isomorphism of an effective Cartier divisor, where the first identification is what the derived
statement `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` unwinds to and the second
is what the comparison of triangles is built from.

## Main results

* `Stacks.SheafOfModules.structureSheafHomEvaluation_eq_sheafHomComplexSingleIso`: the two
  identifications of `SheafHom(O_X[0], O_X[0])` with `O_X[0]` are equal.
* `Stacks.SheafOfModules.internalHomSheafUnitIso_hom_val_app_internalHomSheafHom`: the comparison
  `Hom_{O_X}(O_X, G) ≅ G` reads a local section of the internal Hom sheaf as the value, at the
  unit section over the terminal object of the slice site, of the morphism it names.

## Implementation notes

Both sides are morphisms into a complex concentrated in degree zero, so
`HomologicalComplex.to_single_hom_ext` reduces the statement to degree zero, the other degrees
being handled by the vanishing of the target. In degree zero both sides evaluate, at the unit
section over the terminal object of the slice site over `U`, the single possibly nonzero
component of the cochain attached to a local section of the internal Hom complex: on the left
this is the definition of `AlgebraicGeometry.RingedSite.applyHomSection`, on the right it is
`AlgebraicGeometry.RingedSite.homComponent` followed by the comparison
`Stacks.SheafOfModules.internalHomSheafUnitIso`. So the degree-zero identity is
`internalHomSheafUnitIso_hom_val_app_internalHomSheafHom` and nothing else.

That lemma is in turn the characterising property of
`SheafHom.objIso`: the comparison of two objects satisfying [Stacks, Tag 01CO] acts on sections
as postcomposition with the identity, and the section identification of
`Stacks.SheafOfModules.unitSheafHom` is evaluation at the unit section.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)

/-- **The comparison `Hom_{O_X}(O_X, G) ≅ G` is evaluation at the unit section.** A local
section `t` of the internal Hom sheaf out of the structure sheaf over `U` is a morphism
`O_U ⟶ G|_U`, and the comparison sends it to the value of that morphism at the unit section
over the terminal object of the slice site over `U`. -/
theorem internalHomSheafUnitIso_hom_val_app_internalHomSheafHom
    (G : SheafOfModules.{u} (structureSheaf Rc)) (U : Opens Y)
    (t : (RingedSite.internalHomSheaf (ringedSite Rc)
      (SheafOfModules.unit (structureSheaf Rc)) G).val.obj (op U)) :
    (internalHomSheafUnitIso Rc G).hom.val.app (op U) t =
      ((internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G).sectionsEquiv U
        t).val.app (op (Over.mk (𝟙 U))) (1 : (structureSheaf Rc).obj.obj (op U)) := by
  have h : (unitOverAddEquiv Rc G U).symm
        ((internalHomSheafUnitIso Rc G).hom.val.app (op U) t) =
      (internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G).sectionsEquiv U t := by
    refine (SheafHom.isPostcomp_postcomp (𝟙 G)
      (internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G)
      (unitSheafHom Rc G) U t).trans ?_
    rw [show SheafOfModules.Hom.over (𝟙 G) U = 𝟙 (G.over U) from
      (SheafOfModules.overFunctor (structureSheaf Rc) U).map_id G]
    exact Category.comp_id _
  exact (unitOverAddEquiv Rc G U).symm_apply_eq.mp h

/-- **Evaluation at the unit section is the collapse of the Hom complex of two single
complexes, followed by `Hom_{O_X}(O_X, O_X) ≅ O_X`.** Both morphisms of complexes identify
`SheafHom(O_X[0], O_X[0])` with `O_X[0]`, and they are the same morphism. -/
theorem structureSheafHomEvaluation_eq_sheafHomComplexSingleIso :
    RingedSite.structureSheafHomEvaluation (ringedSite Rc)
        (RingedSite.structureSheafComplex (ringedSite Rc)) =
      (RingedSite.sheafHomComplexSingleIso (ringedSite Rc)
          (SheafOfModules.unit (structureSheaf Rc))
          (SheafOfModules.unit (structureSheaf Rc))).hom ≫
        (HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O))
            (ComplexShape.up ℤ) 0).map
          (internalHomSheafUnitIso Rc (SheafOfModules.unit (structureSheaf Rc))).hom := by
  apply HomologicalComplex.to_single_hom_ext
  ext U s
  exact (internalHomSheafUnitIso_hom_val_app_internalHomSheafHom Rc
    (SheafOfModules.unit (structureSheaf Rc)) U.unop ((RingedSite.homComponent (ringedSite Rc)
      (E := RingedSite.structureSheafComplex (ringedSite Rc))
      (F := RingedSite.structureSheafComplex (ringedSite Rc)) 0 0).val.app U s)).symm

end Stacks.SheafOfModules

end
