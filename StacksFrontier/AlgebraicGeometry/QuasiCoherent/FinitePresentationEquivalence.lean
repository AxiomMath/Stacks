module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.CompactObjects

/-!
# An equivalence of quasi-coherent modules preserves finite presentation

Let `X` and `Y` be quasi-compact and quasi-separated schemes.  Any equivalence
`QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` carries modules of finite presentation to modules of finite
presentation.

## Main results

* `AlgebraicGeometry.isFinitePresentation_map_of_equivalence` — the image of a finitely
  presented quasi-coherent module under the functor of an equivalence of the categories of
  quasi-coherent modules is again finitely presented.
* `AlgebraicGeometry.isFinitePresentation_map_equivalence_iff` — the same statement as an
  equivalence, by applying the above to the inverse equivalence.

## Implementation notes

The content is entirely in [Stacks, Tag 0GPE]
(`AlgebraicGeometry.isFinitelyPresentable_iff_isFinitePresentation`), which identifies finite
presentation of a quasi-coherent module on such a scheme with the purely categorical property
`CategoryTheory.IsFinitelyPresentable` of the corresponding object of `QCoh(𝒪_X)`.  A
categorical property is transported by an equivalence of categories; for finite presentability
that transport is Mathlib's `CategoryTheory.isCardinalPresentable_of_equivalence`.  So one
applies [Stacks, Tag 0GPE] on `X`, transports, and applies it backwards on `Y`.

## References

* [Stacks Project, Tag 0GPE](https://stacks.math.columbia.edu/tag/0GPE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **An equivalence of categories of quasi-coherent modules preserves finite presentation.**
Finite presentation is categorical compactness by [Stacks, Tag 0GPE], and compactness is
transported by any equivalence of categories. -/
theorem isFinitePresentation_map_of_equivalence {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj] :
    SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) (e.functor.obj G).obj := by
  have : IsFinitelyPresentable.{u} G :=
    (isFinitelyPresentable_iff_isFinitePresentation X G).2 ‹_›
  exact (isFinitelyPresentable_iff_isFinitePresentation Y (e.functor.obj G)).1 inferInstance

/-- **An equivalence of categories of quasi-coherent modules preserves and reflects finite
presentation.**  Rewriting both sides by [Stacks, Tag 0GPE] turns the statement into
`CategoryTheory.isCardinalPresentable_iff_of_isEquivalence`. -/
theorem isFinitePresentation_map_equivalence_iff {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) (e.functor.obj G).obj ↔
      SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj := by
  have := Cardinal.fact_isRegular_aleph0
  rw [← isFinitelyPresentable_iff_isFinitePresentation Y (e.functor.obj G),
    ← isFinitelyPresentable_iff_isFinitePresentation X G]
  exact isCardinalPresentable_iff_of_isEquivalence G _ e.functor

end AlgebraicGeometry

end
