module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsSiteSize
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.SectionSpaceFiniteLocallyFree

/-!
# The space of sections along a cover finite locally free of a fixed rank

Let `Z` be an object of the big fppf site of a scheme `U` whose structure morphism to `U` is
finite locally free of rank `d`, let `W` be an algebraic space over `U` and let
`w : W ⟶ yoneda.obj Z`. This file proves that the functor of sections of `W_T → Z_T` is an
algebraic space over `U`.

`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_hom`
(`StacksFrontier/AlgebraicGeometry/Stacks/Criteria/SectionSpaceFiniteLocallyFree.lean`) has one
hypothesis left,
`hrepresentable`: Stacks 05Y6 for algebraic spaces at the targets of the site, over the final
algebraic space of the site of `U` as base. In the site of `U` the final algebraic space is the
presheaf represented by the object `U` itself
(`AlgebraicGeometry.Space.baseTerminal_yonedaIsTerminal`), so both the base and the source of
that relative morphism functor are representable by objects of the site, and so is its target:
`hrepresentable` is exactly the statement that
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'`
proves at a representable base, source and target. That is what this file joins up.

The rank is where it enters. The relative morphism functor at a representable target is proved
algebraic from finite local freeness of the morphism of *schemes* underlying the structure
morphism of `Z` — the reading of Section 03HA — whereas the space of sections consumes finite
local freeness in the sense of Stacks 03ZV; the rank form of the passage between them is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank`, which
is unconditional, and it is what the hypothesis on `Z` below is stated with.

## Main results

* `AlgebraicGeometry.Space.toBase_hom_eq_yoneda_map`: the structure morphism of `Z` to the final
  algebraic space of the site of `U` is the Yoneda image of the structure morphism of `Z` to the
  final object of the site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank`: the
  functor of sections of `w : W ⟶ yoneda.obj Z` is an algebraic space over `U` when the morphism
  of schemes underlying the structure morphism of `Z` is finite locally free of rank `d`.
* `isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFreeOfRank`:
  in the namespace `AlgebraicGeometry.Space`, the same for the restriction of scalars the space
  of sections is identified with.

## Implementation notes

No `@[stacks]` attribute is placed here. The hypothesis on `Z` fixes a rank, which the source's
Stacks 05YF does not, so these statements are not the tag; the attribute for Stacks 05YF stays on
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_source`.

## References

* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open SectionSpaceRestriction

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)
    (Z : BigFppfOver B U hU)

/-- The morphism of schemes underlying the structure morphism of `Z` to the final object of the
big fppf site of `U` is the structure morphism of `Z` over `U`. -/
theorem toScheme_map_from_baseTerminal :
    (BigFppfOver.toScheme B U hU).map (Over.mkIdTerminal.from Z) = B.inclusion.map Z.hom := by
  have h : (Over.mkIdTerminal.from Z).left = Z.hom := by
    simp
  show B.inclusion.map (Over.mkIdTerminal.from Z).left = B.inclusion.map Z.hom
  exact congrArg B.inclusion.map h

/-- **The structure morphism of `Z` to the final algebraic space of the site of `U` is a Yoneda
image.** The presheaf underlying the final algebraic space is the presheaf represented by the
final object `U` of the site, so both morphisms into it from `yoneda.obj Z` are the unique one. -/
theorem toBase_hom_eq_yoneda_map :
    (toBase B U hU Z).hom = yoneda.map (Over.mkIdTerminal.from Z) :=
  (terminalSpaceObjIsTerminal B U hU).hom_ext _ _

variable (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)

/-- **The space of sections along a cover finite locally free of rank `d` is an algebraic
space.** Let `Z` be an object of the big fppf site of a scheme `U` whose structure morphism over
`U` is finite locally free of rank `d`, let `W` be an algebraic space over `U` and let
`w : W ⟶ yoneda.obj Z`. Then the functor of sections of `W_T → Z_T` is an algebraic space
over `U`.

The one hypothesis of
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_hom` is
discharged by
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'`:
in the site of `U` the base of that relative morphism functor is the presheaf represented by `U`,
its source is represented by `Z` and its target by an object of the site, which is the situation
that theorem covers. -/
theorem isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank
    (hW : IsAlgebraicSpace B U hU W) (d : ℕ)
    [hzr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B U hU).map (Over.mkIdTerminal.from Z)) d] :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) := by
  have hpre : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
      (BigFppfOver.toScheme B U hU)).presheaf
        (yoneda.map (Over.mkIdTerminal.from Z)) :=
    presheaf_yoneda_map_of_inverseImage B U hU inferInstance (Over.mkIdTerminal.from Z) hzr
  have hpre' : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
      (BigFppfOver.toScheme B U hU)).presheaf (toBase B U hU Z).hom := by
    rw [toBase_hom_eq_yoneda_map]; exact hpre
  have hz : IsFiniteLocallyFree B U hU (toBase B U hU Z) :=
    (isFiniteLocallyFreeOfRank_of_presheaf_isFiniteLocallyFreeOfRank B U hU
        (toBase B U hU Z)
        (by rw [toBase_hom_eq_yoneda_map]
            exact Functor.relativelyRepresentable.map yoneda (Over.mkIdTerminal.from Z))
        d hpre').isFiniteLocallyFree
  refine isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_hom B U hU Z W w hW hz
    fun V u => ?_
  exact (iff_of_eq (congrArg (fun m => IsAlgebraicSpace B U hU
      (relativeHom B U hU (yoneda.obj Z) (yoneda.obj V) (terminalSpace B U hU).obj m u
        (isAlgebraicSpace_yoneda B U hU Z) (isAlgebraicSpace_yoneda B U hU V)
        (terminalSpace B U hU).property))
    (toBase_hom_eq_yoneda_map B U hU Z))).mpr
    (isAlgebraicSpace_relativeHom_yonedaObj_of_isFiniteLocallyFreeOfRank'
      (Over.mkIdTerminal.from Z) u d)

/-- **The restriction of scalars of `w` over the final algebraic space of the site of `U` is an
algebraic space**, when the structure morphism of `Z` over `U` is finite locally free of
rank `d`. This is
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank` carried
back along `AlgebraicGeometry.Space.restrictionOfScalarsIsoSectionSpace`. -/
theorem isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFreeOfRank
    (hW : IsAlgebraicSpace B U hU W) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B U hU).map (Over.mkIdTerminal.from Z)) d] :
    IsAlgebraicSpace B U hU
      (restrictionOfScalars B U hU (toCover B U hU Z W hW w) (toBase B U hU Z)).presheaf :=
  isAlgebraicSpace_of_iso B U hU
    (restrictionOfScalarsIsoSectionSpace B U hU Z W hW w).symm
    (isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFreeOfRank B U hU Z W w hW d)

end AlgebraicGeometry.Space

end
