module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Finite type points and surjective 1-morphisms locally of finite type (Stacks 06G1)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is locally of finite type
(**Stacks 06FS**, part (1)) and surjective (**Stacks 04ZS**) carries the set `𝒳_{ft-pts}` of
finite type points of `𝒳` (**Stacks 06FY**) *onto* `𝒴_{ft-pts}`.

One inclusion is **Stacks 06G0**. For the other, a finite type point `y` of `𝒴` is represented by
a field-valued point `p` whose 1-morphism `q : Spec k ⟶ 𝒴` is locally of finite type, and the
2-fibre product `𝒳_k = Spec k ×_𝒴 𝒳` of **Stacks 04T2** is considered. Its projection to `Spec k`
is surjective by **Stacks 04ZU**, so `𝒳_k` is nonempty and therefore has a finite type point; its
projection to `𝒳` is locally of finite type by **Stacks 06FU**, so the image of that point is a
finite type point of `𝒳` by Stacks 06G0. The spectrum of a field has one point, so the image of
that finite type point in `|𝒴|` is `y`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.subsingleton_points_fieldValuedPointBaseStack`: the algebraic stack of
  the base of a field-valued point has at most one point.
* `AlgebraicGeometry.Stack.mem_image_finiteTypePoints_of_subsingleton`: a point of `|𝒴|` in the
  image of a 1-morphism locally of finite type whose source has at most one point is the image of
  a finite type point of `𝒳`.
* `AlgebraicGeometry.Stack.image_finiteTypePoints_of_isSurjective`: **Stacks 06G1**.

## Implementation notes

The equality is stated for the map on points of **Stacks 04XG** formed with the fibredness witness
read off the underlying category fibred in groupoids, as `AlgebraicGeometry.Stack.finiteTypePoints`
and **Stacks 06G0** (`AlgebraicGeometry.Stack.mapsTo_finiteTypePoints`) are. The witness carried by
`AlgebraicGeometry.Stack.AlgebraicStacks.points` is instead chosen from the algebraic-stack
condition; the two agree because fibredness in groupoids is a proposition, and the two spellings
are used interchangeably in the proof.

The reverse inclusion is proved for an arbitrary 1-morphism out of an algebraic stack with at most
one point, in `AlgebraicGeometry.Stack.mem_image_finiteTypePoints_of_subsingleton`; the only
property of the spectrum of a field it uses is that it has one point.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
* [Stacks Project, Tag 06G1](https://stacks.math.columbia.edu/tag/06G1)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The algebraic stack of the base of a field-valued point has at most one point: that base is
the spectrum of a field, which has a unique prime ideal. -/
theorem subsingleton_points_fieldValuedPointBaseStack
    {𝒞 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (p : FieldValuedPoint B S hS 𝒞) :
    Subsingleton (AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS p.base)) :=
  subsingleton_points_schemeStack.{u, w} B S hS p.base
    (Scheme.homeoOfIso p.isSpec).injective.subsingleton

/-- Let `f : 𝒳 ⟶ 𝒴` be a surjective 1-morphism of algebraic stacks over `S` and let
`q : 𝒦 ⟶ 𝒴` be a 1-morphism locally of finite type whose source has at most one point. Then every
point of `|𝒴|` in the image of `q` is the image of a finite type point of `𝒳`.

The 2-fibre product `𝒦 ×_𝒴 𝒳` has a point above the given one because `f` is surjective
(**Stacks 04ZU**), hence has a finite type point; its projection to `𝒳` is locally of finite type
as a base change of `q` (**Stacks 06FU**), so the image of that finite type point in `|𝒳|` is of
finite type (**Stacks 06G0**). Its image in `|𝒴|` is computed with the 2-commutativity of the
square, the second projection landing at the only point of `|𝒦|`. -/
theorem mem_image_finiteTypePoints_of_subsingleton
    {𝒳 𝒴 𝒦 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (q : 𝒦 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hq : AlgebraicStacks.IsLocallyOfFiniteType B S hS q)
    (hsub : Subsingleton (AlgebraicStacks.points B S hS 𝒦))
    (z : AlgebraicStacks.points B S hS 𝒦) :
    AlgebraicStacks.pointsMap B S hS q z ∈
      AlgebraicStacks.pointsMap B S hS f '' finiteTypePoints B S hS 𝒳 := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS f q
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f q
  have hfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.fst :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS q f P hP hq
  have hsnd : IsSurjective B S hS P.snd :=
    isSurjective_of_isTwoFibreProduct B S hS P hP hsurj
  obtain ⟨z₀, -⟩ := hsnd z
  obtain ⟨x, hx⟩ := exists_isFiniteTypePoint_of_nonempty.{u, w} B S hS P.pt ⟨z₀⟩
  refine ⟨AlgebraicStacks.pointsMap B S hS P.fst x,
    mapsTo_finiteTypePoints.{u, w} B S hS P.fst hfst hx, ?_⟩
  have hcomp₁ := congrFun (AlgebraicStacks.pointsMap_comp B S hS P.fst f) x
  have hcomp₂ := congrFun (AlgebraicStacks.pointsMap_comp B S hS P.snd q) x
  have hsq := congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS P.iso.hom) x
  simp only [Function.comp_apply] at hcomp₁ hcomp₂
  rw [← hcomp₁, hsq, hcomp₂, hsub.elim (AlgebraicStacks.pointsMap B S hS P.snd x) z]

/-- **Stacks 06G1.** A surjective 1-morphism of algebraic stacks over `S` which is locally of
finite type maps the set of finite type points of its source *onto* the set of finite type points
of its target.

That the image is contained in `𝒴_{ft-pts}` is **Stacks 06G0**. Conversely a finite type point of
`𝒴` is represented by a field-valued point whose 1-morphism out of the algebraic stack of the
spectrum of a field is locally of finite type, and that spectrum has a single point, so
`AlgebraicGeometry.Stack.mem_image_finiteTypePoints_of_subsingleton` applies to it. -/
@[stacks 06G1]
theorem image_finiteTypePoints_of_isSurjective {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hsurj : IsSurjective B S hS f) :
    Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom ''
        finiteTypePoints B S hS 𝒳 = finiteTypePoints B S hS 𝒴 := by
  refine Set.Subset.antisymm
    (Set.MapsTo.image_subset (mapsTo_finiteTypePoints.{u, w} B S hS f hf)) fun y hy => ?_
  obtain ⟨p, hpy, hplft⟩ := hy
  have himg := mem_image_finiteTypePoints_of_subsingleton.{u, w} B S hS f
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒴 p) hsurj hplft
    (subsingleton_points_fieldValuedPointBaseStack.{u, w} B S hS p)
    (pointClass B S hS (schemeStack.{u, w} B S hS p.base).val.val
      (Classical.choose (schemeStack.{u, w} B S hS p.base).property) p.atBase)
  have hkey : AlgebraicStacks.pointsMap B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒴 p)
      (pointClass B S hS (schemeStack.{u, w} B S hS p.base).val.val
        (Classical.choose (schemeStack.{u, w} B S hS p.base).property) p.atBase) = y :=
    (pointClass_fieldValuedPointMap_atBase B S hS 𝒴.val p).trans hpy
  exact hkey ▸ himg

end AlgebraicGeometry.Stack

end
