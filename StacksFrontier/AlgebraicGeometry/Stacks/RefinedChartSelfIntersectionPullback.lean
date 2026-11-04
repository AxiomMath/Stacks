module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDimensionFibre

/-!
# The self-intersection of a refined chart, on representing presheaves (Stacks 0DS9)

Let `f : U ⟶ 𝒳` be a chart of an algebraic stack, `sq` a 2-fibre product square for the cospan
`(f, f)` — so its apex is the relation `R = U ×_𝒳 U`, with target map `t` the first leg and
source map `s` the second — and let `h : U' ⟶ U` refine the chart. The self-intersection of the
refined chart `U' ⟶ U ⟶ 𝒳` is then the pasted rectangle
`AlgebraicGeometry.Stack.refinedSelfIntersectionSquare`, built in two steps: first the base
change `U' ×_{h, U, t} R` of the relation along the refinement, then the base change
`(U' ×_{h, U, t} R) ×_{s, U} U'` of that along the source map.

This file pushes those two steps down to representing presheaves: each is a *pullback square of
presheaves* on the big fppf site, which is the form in which the chart comparison of Stacks 0DS9
consumes them.

## Main results

* `AlgebraicGeometry.Stack.isPullback_representingMap_refinementTargetBaseChange`: the first
  step, `U' ×_{h, U, t} R`, as a pullback of `yoneda.map h` and the target map `t`.
* `AlgebraicGeometry.Stack.isPullback_representingMap_refinementSourceBaseChange`: the second
  step, `(U' ×_{h, U, t} R) ×_{s, U} U'`, as a pullback of the composite leg `pr ≫ s` and
  `yoneda.map h`.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_underlying_of_algebraicStacks`: the transfer of the
  2-fibre product property from the 2-category of algebraic stacks down to the ambient
  2-category of categories fibred in groupoids, which both of the above run on.

## Implementation notes

The two squares are squares of **algebraic stacks**, while
`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct` — Stacks 04SD at a
recognised 2-fibre product — asks for a square of **categories fibred in groupoids**. Passing to
the underlying square is a re-wrapping, but transferring the 2-fibre product property down is
not: `CategoryTheory.Bicategory.isTwoFibreProduct_underlying` needs a *closure witness*, a second
square over the same cospan whose underlying square is already known to be a 2-fibre product,
because without one a terminal object among the squares whose apex is an algebraic stack says
nothing about the squares whose apex is not.

Here that witness is available for *every* cospan of algebraic stacks at once, and that is the
content of `AlgebraicGeometry.Stack.isTwoFibreProduct_underlying_of_algebraicStacks`: the
2-category of algebraic stacks is closed under 2-fibre products (**Stacks 04T2**), so
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` is a square over the cospan whose
underlying square is the canonical one of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, a 2-fibre product
unconditionally. So each of the two squares gets its own closure witness, but both are instances
of one lemma rather than two separate arguments.

**The orientation of the first step is over the target map `t = `** `sq.fst`, not over the source
map. The source map `AlgebraicGeometry.Stack.selfIntersectionSourceMap` is built from `sq.snd`,
so the refinement is pulled back along the *other* leg; the composite leg of the second step is
then `pr ≫ s`, which is where the source map appears. Exchanging the two legs gives a statement
about the opposite cospan which still typechecks, since the cospan of `sq` is `(f, f)`, and which
is not what the chart comparison needs.

Both statements fix the comparison equivalences of `U` and `U'` to be
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, the identification of the
slice over a scheme of the site with the category of elements of the presheaf it represents.
That is forced by the shape asked of them: reading the leg over `h` as `yoneda.map h` is
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`, which holds at those
equivalences, and at any others the leg acquires a transport on each side.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descending a 2-fibre product of algebraic stacks to the ambient 2-category -/

/-- **A 2-fibre product of algebraic stacks is a 2-fibre product of categories fibred in
groupoids.** If a 2-commutative square over a cospan of algebraic stacks is a 2-fibre product in
the 2-category of algebraic stacks, then the square of categories fibred in groupoids underlying
it is a 2-fibre product there.

This is the converse direction of **Stacks 003Q** for the full sub-2-category of algebraic
stacks, and `CategoryTheory.Bicategory.isTwoFibreProduct_underlying` gives it only in the
presence of a closure witness: some square over the same cospan whose underlying square is
already a 2-fibre product. The witness is
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, whose existence is **Stacks
04T2** — the 2-category of algebraic stacks is closed under 2-fibre products — and whose
underlying square is the canonical square of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`. -/
noncomputable def isTwoFibreProduct_underlying_of_algebraicStacks
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}
    {P : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P) :
    Bicategory.IsTwoFibreProduct P.underlying :=
  Bicategory.isTwoFibreProduct_underlying (twoFibreProductSquareAlgebraicStacks B S hS f g) hP
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom g.hom)

/-! ### The two base changes of the refined self-intersection -/

/-- **The first step of the self-intersection of a refined chart, on representing presheaves.**
Let `sq` be a 2-fibre product square for the cospan `(f, f)` of a chart `f : U ⟶ 𝒳`, so that its
apex is the relation `R = U ×_𝒳 U` and its first leg is the target map `t : R ⟶ U`, and let
`h : U' ⟶ U` refine the chart. For a 2-fibre product square `Q` over the cospan
`(schemeStackMap h, t)` — the base change `U' ×_{h, U, t} R` — the induced square of morphisms
of representing presheaves

  `P ⟶ h_{U'}`, `P ⟶ R`, `yoneda.map h`, `t`

is a pullback square of presheaves on the big fppf site.

This is `AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct` after
descending the 2-fibre product property to categories fibred in groupoids with
`AlgebraicGeometry.Stack.isTwoFibreProduct_underlying_of_algebraicStacks`; the presheaf
representing the canonical apex that lemma asks for exists because the target map has
representable source and target, so **Stacks 04ZP** applies to the canonical square. -/
theorem isPullback_representingMap_refinementTargetBaseChange
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    {Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst}
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hR : IsAlgebraicSpace B S hS R)
    (eR : StacksRepresentableCFG.EquivalenceOver sq.pt.val.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    IsPullback
      (representingMap B S hS Q.pt.val (schemeStack.{u, w} B S hS U').val P (yoneda.obj U')
        eP (PresheafOfCategories.sliceElementsEquivalenceOver U') Q.fst.hom)
      (representingMap B S hS Q.pt.val sq.pt.val P R eP eR Q.snd.hom)
      (yoneda.map h)
      (representingMap B S hS sq.pt.val (schemeStack.{u, w} B S hS U).val R (yoneda.obj U)
        eR (PresheafOfCategories.sliceElementsEquivalenceOver U) sq.fst.hom) := by
  obtain ⟨C, -, ⟨eC⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS sq.pt.val (schemeStack.{u, w} B S hS U).val (schemeStack.{u, w} B S hS U').val
    sq.fst.hom (schemeStackMap.{u, w} B S hS h).hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeStackMap.{u, w} B S hS h).hom sq.fst.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeStackMap.{u, w} B S hS h).hom sq.fst.hom)
    (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS sq.fst.hom
      ⟨R, hR, ⟨eR⟩⟩ (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U))
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U')
  have key := isPullback_representingMap_of_isTwoFibreProduct B S hS
    (isTwoFibreProduct_underlying_of_algebraicStacks B S hS hQ)
    (yoneda.obj U') R (yoneda.obj U) P C
    (PresheafOfCategories.sliceElementsEquivalenceOver U') eR
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eP eC
  rw [← representingMap_schemeStackMap.{u, w} B S hS h]
  exact key

/-- **The second leg of the pasted rectangle induces the composite of the two morphisms of
representing presheaves.** The second leg of `sq.pasteFst Q` is `Q.snd ≫ sq.snd`, so the morphism
of representing presheaves of **Stacks 04SW** it induces is the morphism induced by `Q.snd`
followed by the source map `s` of the relation, by functoriality
(`AlgebraicGeometry.Stack.representingMap_comp`).

This is the splitting the second base change of the refined self-intersection is read through. It
is stated separately, and proved by rewriting rather than by applying functoriality to the
assembled statement, because the two sides are matched there against a leg written as a
projection of the pasted rectangle: at that shape the unifier abandons the comparison of the two
`AlgebraicGeometry.Stack.representingMap` applications argument by argument and unfolds both,
which does not terminate within the heartbeat budget. Rewriting the leg first, with the
definitional identity `(sq.pasteFst Q).snd.hom = Q.snd.hom ≫ sq.snd.hom`, keeps the comparison
first-order. -/
theorem representingMap_pasteFst_snd
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver sq.pt.val.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    representingMap B S hS Q.pt.val (schemeStack.{u, w} B S hS U).val P
        (yoneda.obj U) eP (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (sq.pasteFst Q).snd.hom =
      representingMap B S hS Q.pt.val sq.pt.val P R eP eR Q.snd.hom ≫
        selfIntersectionSourceMap B S hS U f sq R
          (PresheafOfCategories.sliceElementsEquivalenceOver U) eR := by
  have hleg : (sq.pasteFst Q).snd.hom = Q.snd.hom ≫ sq.snd.hom := rfl
  rw [hleg, representingMap_comp B S hS P R (yoneda.obj U) eP eR
    (PresheafOfCategories.sliceElementsEquivalenceOver U) Q.snd.hom sq.snd.hom]

/-- **The second step of the self-intersection of a refined chart, on representing presheaves.**
Continuing from
`AlgebraicGeometry.Stack.isPullback_representingMap_refinementTargetBaseChange`, let `T` be a
2-fibre product square over the cospan `((sq.pasteFst Q).snd, schemeStackMap h)` — the base
change `(U' ×_{h, U, t} R) ×_{s, U} U'` of the first step along the source map `s : R ⟶ U`.
Then the induced square of morphisms of representing presheaves

  `W ⟶ P`, `W ⟶ h_{U'}`, `pr ≫ s`, `yoneda.map h`

is a pullback square of presheaves on the big fppf site, where `pr : P ⟶ R` is the morphism
induced by the second leg of `Q`.

The leg over which the second base change is taken is the second leg `Q.snd ≫ sq.snd` of the
rectangle `sq.pasteFst Q`, and
`AlgebraicGeometry.Stack.representingMap_comp` — functoriality of Stacks 04SW — is what splits
the morphism it induces as `pr ≫ s`, the composite with
`AlgebraicGeometry.Stack.selfIntersectionSourceMap`. The apex of the pasted rectangle
`AlgebraicGeometry.Stack.refinedSelfIntersectionSquare` is the apex `T.pt` of this square, so
together the two pullbacks present the self-intersection of the refined chart as the iterated
fibre product. -/
theorem isPullback_representingMap_refinementSourceBaseChange
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    {T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h)}
    (hT : Bicategory.IsTwoFibreProduct T)
    (R P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eR : StacksRepresentableCFG.EquivalenceOver sq.pt.val.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver T.pt.val.val.p
      (presheafOfCategories (W ⋙ typeToCat)).p) :
    IsPullback
      (representingMap B S hS T.pt.val Q.pt.val W P eW eP T.fst.hom)
      (representingMap B S hS T.pt.val (schemeStack.{u, w} B S hS U').val W (yoneda.obj U')
        eW (PresheafOfCategories.sliceElementsEquivalenceOver U') T.snd.hom)
      (representingMap B S hS Q.pt.val sq.pt.val P R eP eR Q.snd.hom ≫
        selfIntersectionSourceMap B S hS U f sq R
          (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
      (yoneda.map h) := by
  obtain ⟨C, -, ⟨eC⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS (schemeStack.{u, w} B S hS U').val (schemeStack.{u, w} B S hS U).val Q.pt.val
    (schemeStackMap.{u, w} B S hS h).hom (sq.pasteFst Q).snd.hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (sq.pasteFst Q).snd.hom (schemeStackMap.{u, w} B S hS h).hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (sq.pasteFst Q).snd.hom (schemeStackMap.{u, w} B S hS h).hom)
    (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (schemeStackMap.{u, w} B S hS h).hom
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U')
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U))
    ⟨P, hP, ⟨eP⟩⟩
  have key := isPullback_representingMap_of_isTwoFibreProduct B S hS
    (isTwoFibreProduct_underlying_of_algebraicStacks B S hS hT)
    P (yoneda.obj U') (yoneda.obj U) W C
    eP (PresheafOfCategories.sliceElementsEquivalenceOver U')
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eW eC
  rw [← representingMap_pasteFst_snd.{u, w} B S hS sq Q R P eR eP,
    ← representingMap_schemeStackMap.{u, w} B S hS h]
  exact key

end AlgebraicGeometry.Stack

end
