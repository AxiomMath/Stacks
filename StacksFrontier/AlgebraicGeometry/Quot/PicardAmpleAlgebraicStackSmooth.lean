module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardAmpleOpenLocus
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModelOpenSubstack

/-!
# The relatively ample locus of the Picard stack is an open substack, smooth over the base

Let `f : X ⟶ B` be a proper morphism of algebraic spaces over a scheme `S` of a big fppf site,
the standing data of **Stacks 0D25**. Relative ampleness of the invertible module of an object of
`Picardstack_{X/B}` has an open locus — that is
`AlgebraicGeometry.Space.hasOpenObjectPropertyLocus_picardAmple` on **Stacks 0D3D**, which is a
theorem of this library, so the locus is available with no hypothesis beyond properness of `f`.

Given **Stacks 0D04**, that `Picardstack_{X/B}` is an algebraic stack, it is presented as an
object of the 2-category of algebraic stacks of **Stacks 03YP** by
`AlgebraicGeometry.Space.picardAlgebraicStackOfPicardSituation`, and the ample locus becomes an
open substack of that object in the sense of **Stacks 04YM**
(`AlgebraicGeometry.Stack.exists_smallModelOpenSubstack_property_eq`). Then, given **Stacks
0DPJ**, that `Picardstack_{X/B} ⟶ 𝒮_B` is smooth, the ample open substack is smooth over `𝒮_B`:
its inclusion is an open immersion, hence smooth, and smooth 1-morphisms compose
(**Stacks 075V**).

This is the second half of the source's proof of the smoothness clause of **Stacks 0DQ0**: *"this
is an open substack by Descent on Spaces, Lemma 0D3D. Since `Picardstack_{X/S} ⟶ S` is smooth by
Moduli Stacks, Lemma 0DPJ we win."* What it does not contain is the first half, the
identification of the base change `PolarizedCurves ×_{𝒞urves} S` with that ample open substack.

No tag is registered in this file. **Stacks 0DPJ** and **Stacks 0D04** are not
yet proved here; each appears only as a binder, `h0DPJ` and `h0D04`. Nothing
else is assumed: properness of `f` is part of the standing data of Stacks 0D25, and Stacks 0D3D
is discharged from
`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`.

## Main results

* `AlgebraicGeometry.Space.hasOpenObjectPropertyLocus_picardAmple_of_isProper`: the relatively
  ample locus of the Picard stack is open, with Stacks 0D3D discharged.
* `AlgebraicGeometry.Space.exists_openSubstack_picardAmple`: it is an open substack of
  `AlgebraicGeometry.Space.picardAlgebraicStackOfPicardSituation`.
* `AlgebraicGeometry.Space.exists_openSubstack_picardAmple_isSmooth`: that open substack is
  smooth over `𝒮_B`, given Stacks 0DPJ.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)

/-- **The relatively ample locus of the Picard stack is open**, with **Stacks 0D3D** discharged.
This is `AlgebraicGeometry.Space.hasOpenObjectPropertyLocus_picardAmple` with its `h0D3D` input
supplied by
`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`, the
library's Stacks 0D3D. -/
theorem hasOpenObjectPropertyLocus_picardAmple_of_isProper (hproper : IsProper B S hS s.f.hom) :
    Stack.HasOpenObjectPropertyLocus B S hS (picardCFG hc s).val (picardAmple hc s) := by
  refine hasOpenObjectPropertyLocus_picardAmple hc s hproper ?_
  intro X Y f hf L hL
  exact exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper B S hS hf hL

/-- **The relatively ample locus is an open substack of `Picardstack_{X/B}`** read as an object of
the 2-category of algebraic stacks of Stacks 03YP. The binder `h0D04` is the statement of
**Stacks 0D04**.

The property of the objects of the small model is
`AlgebraicGeometry.Stack.smallModelObjectProperty` at
`AlgebraicGeometry.Space.picardAmple`: an object of the small model lies in the substack exactly
when the object of `Picardstack_{X/B}` it names has relatively ample invertible module. -/
theorem exists_openSubstack_picardAmple
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS (picardCFG hc s).val)
    (hproper : IsProper B S hS s.f.hom) :
    ∃ W : Stack.OpenSubstack (picardAlgebraicStackOfPicardSituation.{u, w} hc s h0D04),
      W.property = Stack.smallModelObjectProperty B S hS h0D04 (picardAmple hc s) :=
  Stack.exists_smallModelOpenSubstack_property_eq B S hS h0D04 (picardAmple hc s)
    (fun m h => picardAmple_of_hom m h)
    (hasOpenObjectPropertyLocus_picardAmple_of_isProper hc s hproper)

/-- **The relatively ample open substack of `Picardstack_{X/B}` is smooth over `𝒮_B`.** The
binders are the statements of **Stacks 0D04** (`h0D04`) and of **Stacks 0DPJ** (`h0DPJ`, that
`AlgebraicGeometry.Space.picardToBaseAlgebraic` is smooth in the sense of Stacks 075U); the
openness of the ample locus is Stacks 0D3D, a theorem of this library, and the passage from it to
smoothness is `AlgebraicGeometry.Stack.OpenSubstack.isSmooth_inclusion_comp`, i.e. Stacks 075V at
an open immersion.

This is the clause *"this is an open substack by Stacks 0D3D; since `Picardstack_{X/S} ⟶ S` is
smooth by Stacks 0DPJ we win"* of the source's proof of the smoothness half of **Stacks 0DQ0**. -/
theorem exists_openSubstack_picardAmple_isSmooth
    (h0D04 : Stack.IsAlgebraicStack.{u, w} B S hS (picardCFG hc s).val)
    (hproper : IsProper B S hS s.f.hom)
    (h0DPJ : Stack.AlgebraicStacks.IsSmooth B S hS (picardToBaseAlgebraic.{u, w} hc s h0D04)) :
    ∃ W : Stack.OpenSubstack (picardAlgebraicStackOfPicardSituation.{u, w} hc s h0D04),
      W.property = Stack.smallModelObjectProperty B S hS h0D04 (picardAmple hc s) ∧
        Stack.AlgebraicStacks.IsSmooth B S hS
          (W.inclusion ≫ picardToBaseAlgebraic.{u, w} hc s h0D04) := by
  obtain ⟨W, hW⟩ := exists_openSubstack_picardAmple.{u, w} hc s h0D04 hproper
  exact ⟨W, hW, Stack.OpenSubstack.isSmooth_inclusion_comp B S hS W _ h0DPJ⟩

end AlgebraicGeometry.Space

end
