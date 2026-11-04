module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Cancelling the second factor out of a quasi-separated or proper composite

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. This file proves the two cancellation statements that
the separation axioms for 1-morphisms of algebraic stacks (**Stacks 050M**) reduce to and that
the library does not already have.

**Stacks 03KR** says that if `g ∘ f` is separated, resp. locally separated, resp.
quasi-separated, then so is `f`. The first two are in the library, as
`AlgebraicGeometry.Space.isSeparated_of_comp` and
`AlgebraicGeometry.Space.isLocallySeparated_of_comp`; the third is proved here, by the same
argument: the relative diagonal of `f` is a base change of the relative diagonal of `g ∘ f`
along the comparison map of the two fibre products
(`CategoryTheory.Limits.pullback.diagonal_comp_isPullback`), and quasi-separatedness is
quasi-compactness of the relative diagonal (**Stacks 03HL**, part (3)), which is stable under
base change.

**Stacks 04NX** says that if `g ∘ f` is universally closed, resp. proper, and `g` is separated,
then so is `f`. Part (1), universal closedness, is
`AlgebraicGeometry.Space.universallyClosed_of_comp_of_isSeparated`. Part (2) is proved here:
properness is separatedness together with being of finite type and universally closed
(**Stacks 03ZM**), and being of finite type is being locally of finite type together with
quasi-compactness (**Stacks 03XF**, part (3)), so part (2) is the conjunction of four
cancellations, each already available:

* separatedness, by Stacks 03KR, which needs no hypothesis on `g`;
* being locally of finite type, by **Stacks 0462**
  (`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp`), which needs none either;
* quasi-compactness, by **Stacks 03KS**
  (`AlgebraicGeometry.Space.isQuasiCompact_of_comp_of_isQuasiSeparated`), which needs `g`
  quasi-separated — and a separated morphism is quasi-separated by **Stacks 03KK**;
* universal closedness, by part (1) of Stacks 04NX.

Separatedness packaged as a `CategoryTheory.MorphismProperty` of the category of algebraic
spaces over `S`, together with its stability under base change, is
`AlgebraicGeometry.Space.separatedProperty` and
`AlgebraicGeometry.Space.separatedProperty_isStableUnderBaseChange` in
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties`, which this file imports;
that is the form the relative-property statements of Stacks 03YK and Stacks 04XB are stated at.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_of_comp`: **Stacks 03KR**, quasi-separated.
* `AlgebraicGeometry.Space.separatedMorphismProperty_isStableUnderBaseChange`: separatedness, as
  a property of morphisms of the category of algebraic spaces over `S`, is stable under base
  change.
* `AlgebraicGeometry.Space.isProper_of_comp_of_isSeparated`: **Stacks 04NX**, part (2).

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03KR, quasi-separated.** If a composite of morphisms of algebraic spaces over `S`
is quasi-separated, then so is its first factor.

Quasi-separatedness is quasi-compactness of the relative diagonal, and the relative diagonal of
`f` is a base change of that of `f ≫ g`. -/
theorem isQuasiSeparated_of_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hfg : IsQuasiSeparated B S hS (f ≫ g)) :
    IsQuasiSeparated B S hS f :=
  isQuasiCompact_of_isPullback B S hS (Limits.pullback.diagonal_comp_isPullback f g) hfg

/-- Separatedness of a morphism of algebraic spaces over `S` is stable under base change, stated
for an arbitrary cartesian square in the category of algebraic spaces over `S`.

Separatedness is the relative diagonal being a closed immersion (**Stacks 03HL**, part (1)),
that is the `CategoryTheory.MorphismProperty.diagonal` of being a closed immersion, and being a
closed immersion is stable under base change
(`AlgebraicGeometry.Space.isClosedImmersion_isStableUnderBaseChange`). -/
instance separatedMorphismProperty_isStableUnderBaseChange :
    (separatedProperty B S hS).IsStableUnderBaseChange := by
  let _ := isClosedImmersion_isStableUnderBaseChange B S hS
  exact
    { of_isPullback := fun sq hg =>
        (MorphismProperty.IsStableUnderBaseChange.diagonal
          (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)))).of_isPullback
              (AlgebraicSpaces.isPullback_hom B S hS sq) hg }

/-- **Stacks 04NX, part (2).** If a composite of morphisms of algebraic spaces over `S` is proper
and its second factor is separated, then its first factor is proper.

Properness is separatedness, finite type and universal closedness (**Stacks 03ZM**). The first
cancels by **Stacks 03KR** and the universal closedness by part (1) of Stacks 04NX; finite type
is local finite type, which cancels by **Stacks 0462**, together with quasi-compactness, which
cancels by **Stacks 03KS** against a quasi-separated second factor — and the second factor is
quasi-separated, being separated (**Stacks 03KK**). -/
@[stacks 04NX "part (2): properness"]
theorem isProper_of_comp_of_isSeparated {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsProper B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsProper B S hS f :=
  ⟨isSeparated_of_comp B S hS f g hfg.1,
    ⟨isLocallyOfFiniteType_of_comp B S hS hX hY hZ f g hfg.2.1.1,
      isQuasiCompact_of_comp_of_isQuasiSeparated B S hS f g hX hZ hfg.2.1.2
        (isQuasiSeparated_of_isSeparated B S hS hg)⟩,
    universallyClosed_of_comp_of_isSeparated B S hS hX hY hZ f g hfg.2.2 hg⟩

end AlgebraicGeometry.Space

end
