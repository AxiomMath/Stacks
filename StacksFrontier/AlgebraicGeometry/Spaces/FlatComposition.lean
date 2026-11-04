module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Composition of flat morphisms of algebraic spaces (Stacks 03MN)

A composition of flat morphisms of algebraic spaces over a scheme `S` is flat.

Flatness of a morphism of algebraic spaces is the chartwise predicate
`AlgebraicGeometry.Space.IsFlat` of **Stacks 03ML**, part (1), so this is the chart-level
composition lemma `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp` applied to flatness of
morphisms of schemes, which is étale local on the source and target by
`AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget` (**Stacks 04R3**, flat case) and stable
under composition in Mathlib.

## Main results

* `AlgebraicGeometry.Space.isFlat_comp`: **Stacks 03MN**.
* `AlgebraicGeometry.Space.isFlat_comp_of_etale_chart`: an étale chart followed by a flat
  morphism is flat, which is the form a descent along affine étale charts consumes.
* `AlgebraicGeometry.Space.isFlat_isStableUnderComposition`: the same packaged as a
  `CategoryTheory.MorphismProperty.IsStableUnderComposition` instance on the category
  `AlgebraicGeometry.AlgebraicSpaces` of **Stacks 02X2**, which is the form the fpqc locality
  results consume.

## Implementation notes

Stacks 03MN lives in *Morphisms of Algebraic Spaces* (Chapter 67). It is proved in this
directory, as is `AlgebraicGeometry.Space.isFlat_of_isSmooth` (**Stacks 04TA**, same chapter,
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothFlat.lean`): it is a *theorem*, it introduces no
notion, and it is stated in the shape Tag 03MN gives it, as
`AlgebraicGeometry.Space.isFlat_comp`. It is used for Stacks 041W and hence for the flat-fppf
site of **Stacks 0787**/**0788**.

The companion `AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` (**Stacks 03MO**) is
proved in `StacksFrontier/AlgebraicGeometry/Descent/EtaleLocal/FlatLocalAtSource.lean`, from the
same chart-level lemma family; this file is its composition counterpart.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MN](https://stacks.math.columbia.edu/tag/03MN)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03MN.** A composition of flat morphisms of algebraic spaces over `S` is flat. -/
@[stacks 03MN]
theorem isFlat_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsFlat B S hS f) (hg : IsFlat B S hS g) :
    IsFlat B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS (@Flat.{u} : MorphismProperty Scheme.{u})
    Flat.isEtaleLocalOnSourceAndTarget hF hG hH f g hf hg

/-- **An étale chart of an algebraic space followed by a flat morphism is flat.** An étale
morphism of algebraic spaces over `S` is flat (**Stacks 0467**), and flatness is stable under
composition (**Stacks 03MN**); the source of the chart is algebraic by **Stacks 025Z**. -/
theorem isFlat_comp_of_etale_chart
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {T : BigFppfOver B S hS} (e : yoneda.obj T ⟶ F)
    (he : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf e)
    (a : F ⟶ G) (ha : IsFlat B S hS a) : IsFlat B S hS (e ≫ a) :=
  isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS T) hF hG e a
    (isFlat_of_isEtale B S hS ((isEtale_iff_presheaf_of_yoneda B S hS e).2 he)) ha

/-- Flatness, as a property of morphisms of the category of algebraic spaces over `S`, is stable
under composition. This is `AlgebraicGeometry.Space.isFlat_comp` with the algebraicity of the
three objects supplied by the objects themselves. -/
instance isFlat_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFlat B S hS f.hom) where
  comp_mem {X Y Z} f g hf hg :=
    isFlat_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

end AlgebraicGeometry.Space

end
