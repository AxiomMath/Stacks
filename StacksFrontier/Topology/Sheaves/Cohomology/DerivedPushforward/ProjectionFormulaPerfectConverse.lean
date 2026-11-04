module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect

/-!
# The projection-formula map upstairs from its derived pullback downstairs

The square of [Stacks, Tag 0B6B] relates the projection-formula morphism of a morphism of ringed
spaces and that of its base change along an open immersion.
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap` reads
the square in one direction; this file reads it in the other.

## Main results

* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_of_comp_eq'`: invertibility read off a
  commuting square of composites, with the two unknowns of `isIso_of_comp_eq` exchanged.
*
`isIso_projectionFormulaMap_of_isIso_derivedPullback_map`:
  the projection-formula morphism upstairs is invertible as soon as the derived pullback along an
  open immersion of the base of the morphism downstairs is.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaPerfect

attribute [local instance] HasDerivedCategory.standard

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Invertibility read off a commuting square of composites, in the other orientation.**  If
`a ≫ b = c ≫ d` with `a`, `c` and `d` invertible, then `b` is invertible.

This is `isIso_of_comp_eq` with the two unknowns exchanged, and for the same reason its three
invertibility hypotheses are explicit arguments rather than instances. -/
theorem isIso_of_comp_eq' {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y}
    {c : W ⟶ Z} {d : Z ⟶ Y} (hab : a ≫ b = c ≫ d)
    (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b := by
  have hcd : IsIso (c ≫ d) := @IsIso.comp_isIso _ _ _ _ _ _ _ hc hd
  have hab' : IsIso (a ≫ b) := hab ▸ hcd
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ha hab'

/-- **The projection-formula morphism of [Stacks, Tag 0B53] upstairs is invertible as soon as the
derived pullback along an open immersion of the base of the morphism downstairs is.**  This is the
converse of `isIso_derivedPullback_map_projectionFormulaMap`, read off the same square of
[Stacks, Tag 0B6B]: five of its six arrows are invertible — the two comparisons of
[Stacks, Tag 079U], the two derived base-change maps, and now `Lg^*` of the morphism for `f` —
so the sixth, the morphism for `f'`, is invertible too.

There is no boundedness, flatness, quasi-coherence or perfectness hypothesis on `E` or `K`.  It
is what lets a statement proved for the whole of `Y` be fed to a dévissage carried out over an
open of `Y`. -/
theorem isIso_projectionFormulaMap_of_isIso_derivedPullback_map
    [SheafedSpace.IsOpenImmersion g'] [SheafedSpace.IsOpenImmersion g]
    (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso ((derivedPullback g).map (projectionFormulaMap f E K))) :
    IsIso (projectionFormulaMap f' ((derivedPullback g').obj E)
      ((derivedPullback g).obj K)) := by
  have hbcE : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq.w E) :=
    Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions
      g' f' f g sq E
  have key : _ = _ := projectionFormulaMap_derivedBaseChangeMap g' f' f g sq.w E K
  refine @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ?_
    (isIso_of_comp_eq' key
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g).app _).isIso_hom
      h ?_)
  · refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    exact ⟨⟨Prod.mkHom (inv (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      g' f' f g sq.w E)) (𝟙 _), by ext <;> simp, by ext <;> simp⟩⟩
  · refine @IsIso.comp_isIso _ _ _ _ _ _ _
      (Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions
        g' f' f g sq _) ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @IsIso.comp_isIso _ _ _ _ _ _ _
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g').app _).isIso_hom ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    exact ⟨⟨Prod.mkHom (𝟙 _) ((derivedPullbackSquareIso g' f' f g sq.w).hom.app K),
      by ext <;> simp, by ext <;> simp⟩⟩

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
