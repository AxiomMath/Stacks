module

/-
Copyright (c) 2026 the Stacks in Lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.GeneratedSubfunctorColimit

/-!
# A functor to types is a filtered colimit of lifted small-valued functors

Composing the diagram of finitely generated subfunctors of `P : A ⥤ Type (max u w)` with the
shrinking of `ShrunkGeneratedDiagram` presents `P` as a filtered colimit of a diagram of functors
landing in `Type u`, lifted objectwise along `uliftFunctor`.

## Main results

* `generatedShrunkDiagram`: the diagram of shrunken finitely generated subfunctors, in
  `A ⥤ Type u`.
* `generatedShrunkDiagramIso`: its objectwise lift is isomorphic to the diagram of subfunctors.
* `generatedShrunkCocone`, `isColimitGeneratedShrunkCocone`: `P` is its colimit.

## References

* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Sites.UniverseBridge

variable {A : Type u} [SmallCategory A] (P : A ⥤ Type (max u w))

/-- The diagram of the finitely generated subfunctors of `P`, shrunk to `Type u`. -/
public def generatedShrunkDiagram : Finset (Σ a, P.obj a) ⥤ (A ⥤ Type u) where
  obj s := generatedShrunk P s
  map {s t} h := FunctorToTypes.shrinkMap (Subfunctor.homOfLe (generated_monotone (leOfHom h)))
  map_id s := by
    rw [homOfLe_self, shrinkMap_id]
  map_comp {s t r} h h' := by
    rw [← shrinkMap_comp, homOfLe_comp]

/-- Lifting the shrunken diagram objectwise along `uliftFunctor` recovers the diagram of
subfunctors of `P`. -/
public def generatedShrunkDiagramIso :
    generatedShrunkDiagram P ⋙ (Functor.whiskeringRight A (Type u) (Type (max u w))).obj
      uliftFunctor.{w, u} ≅ generatedDiagram P :=
  NatIso.ofComponents (fun s => generatedShrunkUliftIso P s) fun {s t} h =>
    whiskerRight_shrinkMap_comp_shrinkUliftIso_hom
      (F := (generated P s).toFunctor) (G := (generated P t).toFunctor)
      (Subfunctor.homOfLe (generated_monotone (leOfHom h)))

/-- The cocone presenting `P` as the colimit of the lifted shrunken diagram. -/
public def generatedShrunkCocone :
    Cocone (generatedShrunkDiagram P ⋙ (Functor.whiskeringRight A (Type u) (Type (max u w))).obj
      uliftFunctor.{w, u}) :=
  (Cocone.precompose (generatedShrunkDiagramIso P).hom).obj (generatedCocone P)

/-- **`P` is the filtered colimit of the lifts of its shrunken finitely generated
subfunctors.** -/
public def isColimitGeneratedShrunkCocone : IsColimit (generatedShrunkCocone P) :=
  (IsColimit.precomposeHomEquiv _ _).symm (isColimitGeneratedCocone P)

end Stacks.Sites.UniverseBridge

end
