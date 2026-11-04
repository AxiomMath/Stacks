module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBase

/-!
# An algebraic stack with quasi-compact absolute diagonal is decent

An algebraic stack whose absolute diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is quasi-compact is decent. Here
quasi-compactness of the diagonal is quasi-compactness of a 1-morphism of algebraic stacks in the
sense of Stacks 050U; this is weaker than quasi-separatedness of `𝒳`, which also asks the
represented base changes of the diagonal to be quasi-separated.

## Main results

* `isQuasiCompact_relativeDiagonal_structureMorphism_of_changeBase`: quasi-compactness of the
  relative diagonal of a structure morphism descends along a change of base.
* `isQuasiCompact_relativeDiagonal_structureMorphism_of_absolute`: if the absolute diagonal of `𝒳`
  is quasi-compact, so is the relative diagonal of its structure morphism over `S`.
* `isDecent_of_isQuasiCompact_diagonal`: an algebraic stack with quasi-compact absolute diagonal
  is decent.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050Y](https://stacks.math.columbia.edu/tag/050Y)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Quasi-compactness of the relative diagonal of a structure morphism descends along a change
of base.** If the relative diagonal of the structure morphism of Construction A of `𝒳` along
`g : S ⟶ S'` is quasi-compact in the sense of Properties of Stacks, Section 04XB, then so is the
relative diagonal of the structure morphism of `𝒳`. -/
theorem isQuasiCompact_relativeDiagonal_structureMorphism_of_changeBase
    (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsQuasiCompact B S' hS'
      (relativeDiagonalAlgebraicStacks B S' hS'
        (structureMorphism B S' hS'
          (changeBaseAlgebraicStack B S S' hS hS' g 𝒳))).hom) :
    IsQuasiCompact B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)).hom := by
  rintro U y hy F hF ⟨e⟩
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_absolute
    𝒳.val.val.p g U
    (structureMorphism B S hS 𝒳).hom.hom.w
    (structureMorphism B S' hS' (changeBaseAlgebraicStack B S S' hS hS' g 𝒳)).hom.hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  exact Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
    U.hom S' hS' g _ rfl F hF (h𝒳 (Over.mk (U.hom ≫ g)) y' hy' F hF he')

/-- If the absolute diagonal of `𝒳` — the relative diagonal of the structure morphism of `𝒳`
viewed over the terminal scheme `Spec ℤ` — is quasi-compact in the sense of Properties of Stacks,
Section 04XB, then so is the relative diagonal of the structure morphism of `𝒳` over its own
base `S`. -/
theorem isQuasiCompact_relativeDiagonal_structureMorphism_of_absolute
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsQuasiCompact B (⊤_ Scheme.{u}) hZ
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) hZ
        (structureMorphism B (⊤_ Scheme.{u}) hZ
          (AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳))).hom) :
    IsQuasiCompact B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)).hom :=
  isQuasiCompact_relativeDiagonal_structureMorphism_of_changeBase B S hS (⊤_ Scheme.{u}) hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 h𝒳

/-- **An algebraic stack whose absolute diagonal is quasi-compact is decent.** -/
@[stacks 0GW2 "quasi-compact diagonal"]
theorem isDecent_of_isQuasiCompact_diagonal
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hΔ : IsQuasiCompactMorphism.{u, w} B (⊤_ Scheme.{u}) hZ
      (relativeDiagonalAlgebraicStacks B (⊤_ Scheme.{u}) hZ
        (structureMorphism B (⊤_ Scheme.{u}) hZ
          (AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳)))) :
    IsDecent B S hS 𝒳.val := by
  have hΔS : IsQuasiCompact B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)).hom :=
    isQuasiCompact_relativeDiagonal_structureMorphism_of_absolute B S hS hZ 𝒳
      ((isQuasiCompactMorphism_relativeDiagonal_iff B (⊤_ Scheme.{u}) hZ
        (structureMorphism B (⊤_ Scheme.{u}) hZ
          (AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳))).1 hΔ)
  intro x
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  refine ⟨p, rfl,
    (isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒳 p).2 ?_⟩
  refine isQuasiCompactMorphism_of_comp_of_isQuasiCompact_relativeDiagonal B S hS
    (fieldValuedPointStackMorphism B S hS 𝒳 p) (structureMorphism B S hS 𝒳) ?_ hΔS
  rw [comp_structureMorphism B S hS (fieldValuedPointStackMorphism B S hS 𝒳 p)]
  exact isQuasiCompactMorphism_structureMorphism_fieldValuedPointBase B S hS p

end AlgebraicGeometry.Stack

end
