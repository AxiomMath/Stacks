module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated

/-!
# The sheaf condition and the diagonal of the space of sections

Let `Z ⟶ U` be a finite morphism of the big fppf site of `U` and let `w : W ⟶ h_Z` be an étale
morphism of presheaves on that site with `W` an algebraic space. The comparison of the space of
sections of `W_T ⟶ Z_T` with the finite part `(W/U)_fin` of the structure morphism `W ⟶ U`,
`AlgebraicGeometry.Space.sectionSpaceToFinitePart`, is an open immersion, with no separatedness
hypothesis on `w`.

The finite part of an arbitrary morphism of algebraic spaces is an fppf sheaf, Stacks 04PE
part (1), and has representable absolute diagonal, Stacks 04PK. Both properties pass to the
space of sections across that open immersion: a representable transformation into a sheaf has a
sheaf as its source (Stacks 02WD), and the diagonal of a subobject is the base change of the
diagonal of the ambient object.

## Main results

* `AlgebraicGeometry.Space.isSheaf_sectionSpace`: the space of sections is an fppf sheaf.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_sectionSpace`: the absolute diagonal of
  the space of sections is representable by schemes.

## Implementation notes

These are two of the three conditions of Stacks 025Y for the space of sections, and they hold
with no separatedness hypothesis on `w`, whereas
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isSeparated` produces all three at
once and only for `w` separated. The remaining condition is the one separatedness is for: a
surjective étale chart of the space of sections is obtained from a chart of the finite part, and
the finite part has one only for a morphism which is separated and locally of finite type,
Stacks 04QH.

The diagonal is the absolute diagonal `CategoryTheory.Limits.diag`, as in the
`diagonal_representable` field of `AlgebraicGeometry.IsAlgebraicSpace`.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02WD](https://stacks.math.columbia.edu/tag/02WD)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PK](https://stacks.math.columbia.edu/tag/04PK)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}

/-- **The space of sections of an étale `w : W ⟶ h_Z` over a finite `Z ⟶ U` is an fppf
sheaf.** -/
theorem isSheaf_sectionSpace (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    Presheaf.IsSheaf (BigFppfOver.topology B U hU) (sectionSpace B U hU Z W w) :=
  _root_.AlgebraicGeometry.Space.isSheaf_of_relativelyRepresentable B U hU
    (sectionSpaceToFinitePart hW hw hZfin)
    (isOpenImmersion_sectionSpaceToFinitePart hW hw hZfin).1
    (isSheaf_finiteOpenSubspacePresheaf B U hU (toTerminalPresheaf B U hU hW))

/-- **The absolute diagonal of the space of sections is representable by schemes.** -/
theorem relativelyRepresentable_diag_sectionSpace (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    yoneda.relativelyRepresentable (diag (sectionSpace B U hU Z W w)) := by
  have := mono_sectionSpaceToFinitePart hW hw hZfin
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_diag_of_mono (sectionSpaceToFinitePart hW hw hZfin))
    (relativelyRepresentable_diag_finiteOpenSubspacePresheaf B U hU
      (toTerminalPresheaf B U hU hW))

end AlgebraicGeometry.Space

end
