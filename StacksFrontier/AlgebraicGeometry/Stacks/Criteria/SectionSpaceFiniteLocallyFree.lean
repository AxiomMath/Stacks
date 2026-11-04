module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeIsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IsFibreSectionsGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsSectionSpace

/-!
# Stacks 05YF with its Stacks 05XR and Stacks 05XQ inputs supplied

Stacks 05YF — the restriction of scalars `Res_{Z/Q}(X)` along a finite locally free `z : Z ⟶ Q`
is an algebraic space — is in this library
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree`, and it
takes three hypotheses besides finite local freeness of `z`: the predicate
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale` at two morphisms, and Stacks 05Y6 for a
representable target.

The two predicates hold for a *finite* `z`, by
`AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale_of_isFinite` and
`AlgebraicGeometry.Space.isFibreSectionsSurjective_of_isFinite`.  A finite locally free morphism
of algebraic spaces is finite, by
`AlgebraicGeometry.Space.isFinite_of_isFiniteLocallyFree`, so both hold under the hypothesis
Stacks 05YF already makes on `z`.  This file supplies them for the space of sections of
`StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsSectionSpace`.

## Main results

* `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale_of_isFiniteLocallyFree` and
  `AlgebraicGeometry.Space.isFibreSectionsSurjective_of_isFiniteLocallyFree`: the two
  predicate-shaped inputs of Stacks 05YD hold for a finite locally free `z`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_hom`:
  Stacks 05YF for the space of sections, with `hrepresentable` its one remaining hypothesis.
  The corresponding statement for the restriction of scalars is
  `isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_of_representable` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FibreSectionsAlgebraicEtale.lean`.

## Implementation notes

The statement of this file whose conclusion is algebraicity keeps the hypothesis
`hrepresentable`, which asks for Stacks 05Y6 at a target representable by an object of the site;
it depends only on `z`, and the library has Stacks 05Y6 for algebraic spaces at representable
data, as
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_yoneda_of_representableBy`.
No `@[stacks]` attribute is placed here: Stacks 05YF is registered on
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_source`.

## References

* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
* [Stacks Project, Tag 05YD](https://stacks.math.columbia.edu/tag/05YD)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The two predicate-shaped inputs of Stacks 05YD for a finite locally free morphism -/

section FibreSections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Z Q : AlgebraicSpaces B S hS}

/-- **The input Stacks 05YD takes from Stacks 05XR holds for a finite locally free `z`.** -/
theorem isFibreSectionsAlgebraicEtale_of_isFiniteLocallyFree (g : X' ⟶ X) (z : Z ⟶ Q)
    (hz : IsFiniteLocallyFree B S hS z) : IsFibreSectionsAlgebraicEtale B S hS g z :=
  isFibreSectionsAlgebraicEtale_of_isFinite g z (isFinite_of_isFiniteLocallyFree B S hS z hz)

/-- **The input Stacks 05YD takes from Stacks 05XQ holds for a finite locally free `z`.** -/
theorem isFibreSectionsSurjective_of_isFiniteLocallyFree (g : X' ⟶ X) (z : Z ⟶ Q)
    (hz : IsFiniteLocallyFree B S hS z) : IsFibreSectionsSurjective B S hS g z :=
  isFibreSectionsSurjective_of_isFinite g z (isFinite_of_isFiniteLocallyFree B S hS z hz)

end FibreSections

/-! ### Stacks 05YF for the space of sections -/

section SectionSpace

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)
    (Z : BigFppfOver B U hU) (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u)
    (w : W ⟶ yoneda.obj Z)

open SectionSpaceRestriction in
/-- **Stacks 05YF for the space of sections, with the Stacks 05XR input
supplied.** Let `Z` be an object of the big fppf site of a scheme `U` whose structure morphism to
the final algebraic space is finite locally free, let `W` be an algebraic space over `U` and let
`w : W ⟶ yoneda.obj Z`. Then the functor of sections of `W_T → Z_T` is an algebraic space over
`U` as soon as Stacks 05Y6 holds for that structure morphism at the targets representable by
objects of the site. -/
theorem isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_hom
    (hW : IsAlgebraicSpace B U hU W)
    (hz : IsFiniteLocallyFree B U hU (toBase B U hU Z))
    (hrepresentable : ∀ (V : BigFppfOver B U hU)
      (u : yoneda.obj V ⟶ (terminalSpace B U hU).obj),
      IsAlgebraicSpace B U hU
        (relativeHom B U hU (yoneda.obj Z) (yoneda.obj V) (terminalSpace B U hU).obj
          (toBase B U hU Z).hom u (isAlgebraicSpace_yoneda B U hU Z)
          (isAlgebraicSpace_yoneda B U hU V) (terminalSpace B U hU).property)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) :=
  isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree_of_fibreSections B U hU Z W hW w hz
    (fun _ _ => isFibreSectionsAlgebraicEtale_of_isFiniteLocallyFree _ (toBase B U hU Z) hz)
    (fun _ _ => isFibreSectionsAlgebraicEtale_of_isFiniteLocallyFree _ (toBase B U hU Z) hz)
    hrepresentable

end SectionSpace

end AlgebraicGeometry.Space

end
