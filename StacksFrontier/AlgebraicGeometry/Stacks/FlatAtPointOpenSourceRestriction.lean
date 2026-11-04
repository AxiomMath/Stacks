module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAtPointChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatLocusOpenImmersionSource
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionOpenSourceRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery

/-!
# Restricting the source of a 1-morphism to an open subspace does not change flatness at a point

Let `f : U ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space `U` to an
algebraic stack `𝒳` over `S`, and let `ι : W ⟶ U` be an open immersion of algebraic spaces. This
file proves that `f` is flat at the image in `|U|` of a point of `|W|`, in the sense of
**Stacks 0CID**, exactly when the restriction `W ⟶ 𝒳` is flat at that point, and draws the
consequence a consumer needs: if `f` is flat at every point of `|U|` in the image of `|W|`, then
`W ⟶ 𝒳` is flat.

This is the stack-level counterpart of the source-locality
`AlgebraicGeometry.Space.isFlatAt_iff_of_isOpenSubspace`. The base change of flatness at a point
along a chart, `isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct`, moves the chart of the
*target*; what is moved here is the source.

## Main results

* `isFlatAt_comp_algebraicSpaceStackMap_iff_of_isOpenImmersion`: the equivalence.
* `isFlat_comp_algebraicSpaceStackMap_of_forall_isFlatAt`: the restriction is flat as soon as `f`
  is flat at every point in the image.

## How it is proved

Both sides are read on one and the same smooth chart `V ⟶ 𝒳` of the target, by an algebraic
space, which `Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation` produces.
For `f` the base change is the canonical 2-fibre product `U ×_𝒳 V` of **Stacks 04T2**; for the
restriction it is the iterated product `(U ×_𝒳 V) ×_U W`, which **Stacks 02XD** in the
2-category of algebraic stacks recognises as a 2-fibre product of the restriction and the chart.
Those are the squares `AlgebraicGeometry.Stack.restrictionInnerSquare` and
`AlgebraicGeometry.Stack.restrictionSquare` of
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDimensionOpenSourceRestriction.lean`, where they
are used for the same purpose at the relative dimension of **Stacks 0DRG**.

On representing algebraic spaces the projection of the restricted base change onto the chart is
the inner projection followed by the projection of `U ×_𝒳 V`
(`AlgebraicGeometry.Stack.representingMap_restrictionSquare_fst`), and the inner projection is a
base change of `ι`, hence an open immersion
(`AlgebraicGeometry.Stack.isOpenImmersion_representingMap_restrictionInnerSquare_fst`). So the
two readings differ by precomposition with an open immersion, and
`AlgebraicGeometry.Space.isFlatAt_comp_iff_of_isOpenImmersion` identifies them.

What remains is that the two marked points correspond: the point of `|U|` that the chart of the
big square sees above a point of the representing space of the small one is the image under `ι`
of the point the chart of the small square sees. That is naturality of the canonical map of
**Stacks 04XL** in the chart (`AlgebraicGeometry.Stack.spacePointMap_representing_naturality`)
together with the filler of the inner square, 2-isomorphic 1-morphisms inducing the same map on
points.

## Implementation notes

The chart is taken by an *algebraic space* rather than by a scheme of the site, because that is
the shape `isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct` is written in;
`AlgebraicGeometry.Stack.restrictionSquare` is stated for a 1-morphism out of an arbitrary
algebraic stack, so no new square is needed.

No `@[stacks]` attribute is attached. **Stacks 0CID** is the definition of flatness at a point
and **Stacks 0CIC** its chart independence, both formalized in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatAtAPoint.lean`; the chapter carries no separate
source-locality assertion for it.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0CIC](https://stacks.math.columbia.edu/tag/0CIC)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  (U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
  (ι : W ⟶ U)
  (f : Stack.algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
  (a : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳)
  (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
      (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).pt.val.val.p
    (presheafOfCategories (Q ⋙ typeToCat)).p)

/-- The marked point of the chart of a 2-fibre product square, read through the representing
equivalence of its apex, is the point of the right-hand factor the square's second projection
sends the tautological chart point to. -/
theorem spacePointMap_equivalenceOverInvMap_comp_eq
    {𝒜 ℬ : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒜 ⟶ ℬ)
    (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eA : StacksRepresentableCFG.EquivalenceOver 𝒜.val.val.p
      (presheafOfCategories (A ⋙ typeToCat)).p)
    (t : Space.points B S hS A) :
    Stack.spacePointMap B S hS A ℬ.val
        (Stack.equivalenceOverInvMap B S hS A eA ≫ g.hom).hom t =
      pointsMap B S hS g
        (Stack.spacePointMap B S hS A 𝒜.val
          (Stack.representingEquivalence B S hS A 𝒜.val eA).functor t) :=
  congrFun (Stack.spacePointMap_comp B S hS A 𝒜.val ℬ.val
    (Stack.equivalenceOverInvMap B S hS A eA).hom g.hom.hom) t

/-- **The chart of the restricted base change sees the restricted point.** The point of `|U|`
which the chart of `U ×_𝒳 V` reads off a point of the representing space of `(U ×_𝒳 V) ×_U W`,
pushed along the inner projection, is the image under `ι` of the point of `|W|` which the chart
of `(U ×_𝒳 V) ×_U W` reads off it. -/
theorem spacePointMap_restrictionSquare_snd_eq (q : Space.points B S hS Q) :
    Stack.spacePointMap B S hS P (Stack.algebraicSpaceStack.{u, w} B S hS U hU).val
        (Stack.equivalenceOverInvMap B S hS P eP ≫
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom).hom
        (Space.pointsMap B S hS Q
          (Stack.representingMap B S hS
            (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
              (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).pt.val
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val Q P eQ eP
            (Stack.restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
              (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).fst.hom) q) =
      pointsMap B S hS (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι)
        (Stack.spacePointMap B S hS Q (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
          (Stack.equivalenceOverInvMap B S hS Q eQ ≫
            (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
              (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).snd.hom).hom q) := by
  rw [spacePointMap_equivalenceOverInvMap_comp_eq B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).snd P eP,
    spacePointMap_equivalenceOverInvMap_comp_eq B S hS
      (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).snd Q eQ]
  refine Eq.trans (congrArg
    (pointsMap B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).snd)
    (Stack.spacePointMap_representing_naturality B S hS Q P
      (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).pt.val
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val eQ eP
      (Stack.restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).fst.hom q)) ?_
  exact (congrFun (pointsMap_comp B S hS
        (Stack.restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
          (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).fst
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).snd) _).symm.trans
    ((congrFun (pointsMap_eq_of_hom₂ B S hS
        (Stack.restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
          (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).iso.hom) _).trans
      (congrFun (pointsMap_comp B S hS
        (Stack.restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
          (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).snd
        (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι)) _))

include hP hQ in
/-- **Flatness at a point, compared on one chart upstairs and downstairs.** On the two base
changes along one smooth chart of `𝒳`, flatness of the restriction `W ⟶ 𝒳` at the point a point
of the representing space of `(U ×_𝒳 V) ×_U W` marks is flatness of `f` at the point the inner
projection marks on `U ×_𝒳 V`. -/
theorem isFlatAt_restrictionSquare_iff (hι : Space.IsOpenImmersion B S hS ι)
    (hasm : Stack.IsRelativelySmooth B S hS a.hom) (q : Space.points B S hS Q) :
    IsFlatAt B S hS (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f)
        (Stack.spacePointMap B S hS Q (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
          (Stack.equivalenceOverInvMap B S hS Q eQ ≫
            (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
              (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).snd.hom).hom q) ↔
      IsFlatAt B S hS f
        (Stack.spacePointMap B S hS P (Stack.algebraicSpaceStack.{u, w} B S hS U hU).val
          (Stack.equivalenceOverInvMap B S hS P eP ≫
            (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom).hom
          (Space.pointsMap B S hS Q
            (Stack.representingMap B S hS
              (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
                (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).pt.val
              (Stack.twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val Q P eQ eP
              (Stack.restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
                (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a).fst.hom) q)) := by
  have hmOpen := Stack.isOpenImmersion_representingMap_restrictionInnerSquare_fst.{u, w}
    B S hS 𝒳 U W hU hW ι f (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a P Q hP hQ eP hι eQ
  have hfst := Stack.representingMap_restrictionSquare_fst.{u, w}
    B S hS 𝒳 U W hU hW ι f (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a P Q eP V
    (StacksRepresentableCFG.EquivalenceOver.refl _) eQ
  have hrest := isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct B S hS
    (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) hQ hV eQ hasm
    (Bicategory.isTwoFibreProduct_underlying
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS a
        (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f))
      (Stack.isTwoFibreProduct_restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (Stack.algebraicSpaceStack.{u, w} B S hS V hV) a)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        a.hom (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f).hom)) q
  refine hrest.trans (Iff.trans ?_
    (isFlatAt_spacePointMap_iff_of_representedTwoFibreProduct B S hS f hP hV eP hasm
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        a.hom f.hom) _).symm)
  exact (iff_of_eq (congrArg (Space.IsFlatAt B S hS · q) hfst)).trans
    (Space.isFlatAt_comp_iff_of_isOpenImmersion B S hS hP hQ hV _ hmOpen _ q)

end Chart

/-! ### The equivalence -/

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  (U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
  (ι : W ⟶ U) (hι : Space.IsOpenImmersion B S hS ι)
  (f : Stack.algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

include hι in
/-- **Restricting the source of a 1-morphism to an open subspace does not change flatness at a
point.** Let `f : U ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space `U` to an
algebraic stack over `S` and let `ι : W ⟶ U` be an open immersion of algebraic spaces. Then the
restriction `W ⟶ 𝒳` is flat at a point `y` of `|W|`, in the sense of **Stacks 0CID**, exactly
when `f` is flat at the image of `y` in `|U|`.

Both sides are read on one and the same smooth chart of `𝒳` by an algebraic space; the two base
changes differ by an open immersion of representing algebraic spaces, and flatness at a point of
a morphism of algebraic spaces is unchanged by one,
`AlgebraicGeometry.Space.isFlatAt_comp_iff_of_isOpenImmersion`. The chart is surjective on
points, so every point of `|W|` is reached. -/
theorem isFlatAt_comp_algebraicSpaceStackMap_iff_of_isOpenImmersion
    (y : points B S hS (Stack.algebraicSpaceStack.{u, w} B S hS W hW)) :
    IsFlatAt B S hS (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) y ↔
      IsFlatAt B S hS f
        (pointsMap B S hS (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι) y) := by
  classical
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒳.property
  have hPtrep : IsRepresentableByAlgebraicSpace B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Bicategory.InducedBicategory.mkHom b :
          Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳) f).pt.val :=
    Stack.isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
      (Stack.algebraicSpaceStack.{u, w} B S hS V hV).val
      (Stack.algebraicSpaceStack.{u, w} B S hS U hU).val b.hom f.hom.hom
      (Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source.{u, w}
        B S hS 𝒳 U hU f)
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  obtain ⟨P, hP, ⟨eP⟩⟩ := id hPtrep
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (Stack.algebraicSpaceStack.{u, w} B S hS V hV)
        (Bicategory.InducedBicategory.mkHom b)).pt.val :=
    Stack.isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (Stack.algebraicSpaceStack.{u, w} B S hS U hU).val
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Bicategory.InducedBicategory.mkHom b :
          Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳) f).pt.val
      (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Bicategory.InducedBicategory.mkHom b :
          Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳) f).snd.hom.hom
      (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι).hom.hom
      (Stack.isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion.{u, w}
        B S hS hW hU hι).1
      hPtrep
  have hbsurj : Stack.IsSurjective B S hS (Bicategory.InducedBicategory.mkHom b :
      Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒳) :=
    Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS
      (𝒳 := Stack.algebraicSpaceStack.{u, w} B S hS V hV) (𝒴 := 𝒳)
      (Bicategory.InducedBicategory.mkHom b) hbsu
  obtain ⟨t, ht⟩ : ∃ t : Space.points B S hS Q,
      Stack.spacePointMap B S hS Q (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
        (Stack.equivalenceOverInvMap B S hS Q eQ ≫
          (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
            (Stack.algebraicSpaceStack.{u, w} B S hS V hV)
            (Bicategory.InducedBicategory.mkHom b)).snd.hom).hom t = y := by
    obtain ⟨s, hs⟩ := (Stack.bijective_spacePointMap_representing B S hS W
      (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
      (StacksRepresentableCFG.EquivalenceOver.refl _)).surjective y
    obtain ⟨t, htt⟩ := Stack.surjective_representingMap_restrictionInnerSquare_snd.{u, w}
      B S hS 𝒳 U W hU hW ι f (Stack.algebraicSpaceStack.{u, w} B S hS V hV)
      (Bicategory.InducedBicategory.mkHom b) Q
      hbsurj eQ s
    refine ⟨t, ?_⟩
    rw [spacePointMap_equivalenceOverInvMap_comp_eq B S hS
      (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (Stack.algebraicSpaceStack.{u, w} B S hS V hV)
        (Bicategory.InducedBicategory.mkHom b)).snd Q eQ]
    exact (Stack.spacePointMap_representing_naturality B S hS Q W
        (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
          (Stack.algebraicSpaceStack.{u, w} B S hS V hV)
          (Bicategory.InducedBicategory.mkHom b)).pt.val
        (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val eQ
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (Stack.restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
          (Stack.algebraicSpaceStack.{u, w} B S hS V hV)
          (Bicategory.InducedBicategory.mkHom b)).snd.hom t).symm.trans
      ((congrArg
        (Stack.spacePointMap B S hS W (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
          (Stack.representingEquivalence B S hS W
            (Stack.algebraicSpaceStack.{u, w} B S hS W hW).val
            (StacksRepresentableCFG.EquivalenceOver.refl _)).functor) htt).trans hs)
  rw [← ht, ← spacePointMap_restrictionSquare_snd_eq B S hS 𝒳 U W hU hW ι f V hV
    (Bicategory.InducedBicategory.mkHom b) P Q eP eQ t]
  exact isFlatAt_restrictionSquare_iff B S hS 𝒳 U W hU hW ι f V hV
    (Bicategory.InducedBicategory.mkHom b) P Q hP hQ eP eQ hι hbsm t

include hι in
/-- **The restriction of a 1-morphism to an open subspace of its source is flat as soon as the
1-morphism is flat at every point in the image.** Flatness of a 1-morphism of algebraic stacks is
flatness at every point of its source
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_forall_isFlatAt`), and at each such point
the hypothesis and `isFlatAt_comp_algebraicSpaceStackMap_iff_of_isOpenImmersion` supply it. -/
theorem isFlat_comp_algebraicSpaceStackMap_of_forall_isFlatAt
    (hflat : ∀ y : points B S hS (Stack.algebraicSpaceStack.{u, w} B S hS W hW),
      IsFlatAt B S hS f
        (pointsMap B S hS (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι) y)) :
    IsFlat B S hS (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) :=
  (isFlat_iff_forall_isFlatAt B S hS
    (Stack.algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f)).2 fun y =>
    (isFlatAt_comp_algebraicSpaceStackMap_iff_of_isOpenImmersion B S hS 𝒳 U W hU hW ι hι f
      y).2 (hflat y)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
