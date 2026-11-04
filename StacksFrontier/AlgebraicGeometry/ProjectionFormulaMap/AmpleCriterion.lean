module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Consequence
public import StacksFrontier.AlgebraicGeometry.ClopenLift.Cohomology

/-!
# The cohomological ampleness criterion from the projection formula morphism

`Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X` says: for a morphism `i : Z ⟶ X` of
schemes and an invertible `𝒪_X`-module `P`, surjectivity of `Γ(X, 𝒪_X ⊗ P) ⟶ Γ(X, i_* 𝒪_Z ⊗ P)`
implies surjectivity of `Γ(X, P) ⟶ Γ(Z, i^* P)`. It holds as soon as global sections take the
projection formula morphism `i_* 𝒪_Z ⊗ P ⟶ i_*(𝒪_Z ⊗ i^* P)` to an epimorphism, and then the
cohomological ampleness criterion follows.

## Main results

* `Stacks.ProjectionFormula.projectionFormulaConsequence_of_epi`:
  `Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X` holds as soon as, for every
  `i : Z ⟶ X` and every invertible `P`, the evaluation at `⊤` of
  `Stacks.ProjectionFormula.projectionFormulaMap' i.toLRSHom.toShHom 𝒪_Z P` is epimorphic.
* `Stacks.ProjectionFormula.isAmple_of_hasEventuallyVanishingH1_of_epi`: on a quasi-compact
  scheme, an invertible module whose positive twists eventually kill the first cohomology of every
  quasi-coherent ideal sheaf is ample, under the same hypothesis.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

/-- Acting by a bifunctor on a morphism in the first variable and the identity in the second is
acting by the induced "tensor on the right" functor: `(uncurry.obj F).map (f ×ₘ 𝟙 W)` is
`(F.flip.obj W).map f`. -/
private lemma uncurry_obj_map_prod_id {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D ⥤ E) {A B : C} (f : A ⟶ B) (W : D) :
    (Functor.uncurry.obj F).map (f ×ₘ 𝟙 W) = (F.flip.obj W).map f := by
  simp only [Functor.uncurry_obj_obj, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    Category.comp_id, Functor.flip_obj_map]

/-- If, for every morphism of schemes `i : Z ⟶ X` and every invertible `𝒪_X`-module `P`, global
sections take `Stacks.ProjectionFormula.projectionFormulaMap' i 𝒪_Z P` to an epimorphism, then
`Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X` holds. -/
theorem projectionFormulaConsequence_of_epi (X : Scheme.{u})
    (h : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) (P : X.Modules)
      [Stacks.Ample.IsInvertibleModule X P],
      Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (projectionFormulaMap' i.toLRSHom.toShHom
          (SheafOfModules.unit (structureRingSheaf Z.toRingedSpace)) P))) :
    Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X := by
  intro Z i P _ h₁
  refine epi_map_unit_of_epi _ P _ ?_ (h i P)
  exact Eq.mp (congrArg (fun m => Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map m))
    (uncurry_obj_map_prod_id (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) P).symm) h₁

/-- On a quasi-compact scheme, an invertible `𝒪_X`-module whose positive twists eventually kill
the first cohomology of every quasi-coherent ideal sheaf (`hH1`) is ample, given the hypothesis
`h` that global sections take the projection formula morphism at the structure sheaf to an
epimorphism. -/
theorem isAmple_of_hasEventuallyVanishingH1_of_epi (X : Scheme.{u}) [CompactSpace X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (h : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) (P : X.Modules)
      [Stacks.Ample.IsInvertibleModule X P],
      Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        (projectionFormulaMap' i.toLRSHom.toShHom
          (SheafOfModules.unit (structureRingSheaf Z.toRingedSpace)) P)))
    (hH1 : Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1 X L) :
    Stacks.Ample.IsAmple X L :=
  Stacks.Tag0B5PClopenLift.isAmple_of_hasEventuallyVanishingH1 X L
    (projectionFormulaConsequence_of_epi X h) hH1

end Stacks.ProjectionFormula

end
