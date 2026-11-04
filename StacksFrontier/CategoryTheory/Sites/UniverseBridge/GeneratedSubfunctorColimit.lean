module

/-
Copyright (c) 2026 the Stacks in Lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.ShrunkGeneratedDiagram
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# A functor to types is the filtered colimit of its finitely generated subfunctors

The finite sets of sections of `P : A ⥤ Type (max u w)` index a filtered diagram of subfunctors
whose colimit is `P` itself. This is the density half of the universe bridge of Stacks 0GN2: with
`GeneratedSubfunctorShrink.small_generated_obj`, it presents an arbitrary `P` as a filtered colimit
of functors with `u`-small values.

The colimit is checked pointwise — `evaluationJointlyReflectsColimits` — and at each object by
`Types.FilteredColimit.isColimitOf'`. Both of its hypotheses are degenerate here: surjectivity is
`exists_generated_mem` at the singleton, and injectivity holds already at the index itself, since
the cocone leg is the inclusion of a subtype, so no filtered-equalisation step is needed.

## Main results

* `generatedDiagram`: the diagram of finitely generated subfunctors.
* `generatedCocone`: its cocone into `P`, given by the inclusions.
* `isColimitGeneratedCocone`: that cocone is a colimit.

## References

* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Sites.UniverseBridge

variable {A : Type u} [SmallCategory A] (P : A ⥤ Type (max u w))

/-- The diagram of the finitely generated subfunctors of `P`, indexed by the finite sets of
sections ordered by inclusion. -/
public def generatedDiagram : Finset (Σ a, P.obj a) ⥤ (A ⥤ Type (max u w)) where
  obj s := (generated P s).toFunctor
  map {s t} h := Subfunctor.homOfLe (generated_monotone (leOfHom h))
  map_id s := by ext a x; rfl
  map_comp {s t r} h h' := by ext a x; rfl

/-- The inclusions of the finitely generated subfunctors of `P` form a cocone over `P`. -/
public def generatedCocone : Cocone (generatedDiagram P) where
  pt := P
  ι :=
    { app s := (generated P s).ι
      naturality {s t} h := by simp [generatedDiagram] }

/-- **`P` is the filtered colimit of its finitely generated subfunctors.** -/
public def isColimitGeneratedCocone : IsColimit (generatedCocone P) := by
  haveI := isFiltered_finsetGens P
  refine evaluationJointlyReflectsColimits _ fun a => ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨s, hs⟩ := exists_generated_mem (P := P) a x
    exact ⟨s, ⟨x, hs⟩, rfl⟩
  · intro s x y h
    exact ⟨s, 𝟙 s, by rw [Subtype.ext h]⟩

end Stacks.Sites.UniverseBridge

end
