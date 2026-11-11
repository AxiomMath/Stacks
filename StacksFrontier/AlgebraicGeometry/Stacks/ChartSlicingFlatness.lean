module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulaySlice
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingLiftedFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAtPointOpenSourceRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatLocusAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat

/-!
# Slicing a flat chart of an algebraic stack by a regular sequence (Stacks 06MD)

This file completes **Stacks 06MD**: let `𝒳` be an algebraic stack over `S`, let `U` be an
algebraic space with a 1-morphism `f : U ⟶ 𝒳` which is flat and locally of finite presentation,
let `Spec k ⟶ 𝒳` be a field-valued point and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`.
If global functions `f₁, …, f_r ∈ Γ(U, 𝒪_U)` map to a regular sequence in the étale local ring
`𝒪_{F, z̄}` at a geometric point `z` of `F`, then after replacing `U` by an open subspace
containing `p(z)` the zero locus `V(f₁, …, f_r) ⟶ 𝒳` is **flat and locally of finite
presentation**.

## Main results

* `exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`:
  **Stacks 06MD**, both conjuncts, at the hypotheses the source states.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_isFlat_chartVanishingSubfunctor`: the flatness
  half of **Stacks 06LW**, applied on a chart of `𝒳` — the open subspace of `U ×_𝒳 𝒲` it returns,
  with the marked point of `|U|` in the image.
* `AlgebraicGeometry.Stack.isFlatAt_chartZeroLocusToStack_of_isFlatAt_vanishingSubfunctor` and
  `AlgebraicGeometry.Stack.isFlatAt_chartZeroLocusToStack_of_mem_image`: the pointwise step —
  flatness of `V(g^*f₁, …, g^*f_r) ⟶ 𝒲` at a point of the chart base change is flatness of
  `V(f₁, …, f_r) ⟶ 𝒳` at the point of `|V(f₁, …, f_r)|` below it.
* `AlgebraicGeometry.Stack.isFlat_zeroLocusOnOpenToStack_of_range_subset`: the resulting flatness
  of `V(f₁, …, f_r) ∩ V ⟶ 𝒳` for an open subspace `V ⊆ U` swept out by the chart base change.
* `AlgebraicGeometry.Stack.isFlat_chartBaseChangeSpaceProjection`,
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_chartBaseChangeSpaceProjection` and
  `AlgebraicGeometry.Stack.isOpenMap_pointsMap_chartBaseChangeSpaceProjection`: the projection
  `U ×_𝒳 𝒲 ⟶ U` along a smooth chart is flat and locally of finite presentation, hence open on
  points — which is what makes the swept-out subspace open.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_algebraicSpaceChartBaseChange`:
  **Stacks 0300** at a chart by an algebraic space.
* `AlgebraicGeometry.Stack.algebraicSpaceStackMap_comp`: the 1-morphism of algebraic stacks
  attached to a composite of morphisms of algebraic spaces is the composite of the two.

## How it is proved

The locally-of-finite-presentation conjunct is
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_zeroLocusOnOpenToStack`, which holds for
*every* open subspace and needs neither a chart nor the regular sequence.

For flatness the source base changes `U ⟶ 𝒳` along a smooth surjective chart `𝒲 ⟶ 𝒳` and applies
the flatness half of **Stacks 06LW** to the morphism of algebraic spaces `U ×_𝒳 𝒲 ⟶ 𝒲`. The data
that application needs — a field-valued point of `𝒲` over the given one of `𝒳`, a cartesian
square presenting the fibre over it, a geometric point of that fibre over `p(z)`, and the
regularity of the pulled-back functions there — is
`AlgebraicGeometry.Stack.exists_chartFibre_isPullback_isRegular`. Stacks 06LW then returns an
open subspace `W' ⊆ U ×_𝒳 𝒲` containing the marked point over which
`V(g^*f₁, …, g^*f_r) ∩ W' ⟶ 𝒲` is flat.

The open subspace of `U` is the image of `W'` under the projection `U ×_𝒳 𝒲 ⟶ U`, which is open
because that projection is a base change of the smooth chart, hence flat and locally of finite
presentation, hence open on points
(`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation`); the
open subspace with that point set is
`AlgebraicGeometry.Space.openSubspaceOfPoints` (**Stacks 03BZ**).

Flatness of `V(f₁, …, f_r) ∩ V ⟶ 𝒳` is then read point by point. Restricting the *source* of a
1-morphism to an open subspace does not change flatness at a point
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp_algebraicSpaceStackMap_of_forall_isFlatAt`),
so it suffices to prove that `V(f₁, …, f_r) ⟶ 𝒳` is flat at every point of `|V(f₁, …, f_r)| ∩ V`.
Such a point lies under *some* point of `|W'|`, because `V` is the image of `|W'|`; that point
lies in `V(g^*f₁, …, g^*f_r)`, because the base change of the zero locus along the projection is
the zero locus of the pulled-back functions
(`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`, with
`AlgebraicGeometry.Space.range_pointsMap_preimage_ι` on points); and over `W'` flatness holds. The
descent of flatness at a point from a chart of the target back to `𝒳` is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_isFlatAt_representingMap` (**Stacks 0CIC**),
applied at the square of
`AlgebraicGeometry.Stack.restrictionSquare` whose representing algebraic space is the zero locus
of the pulled-back functions
(`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange`). Chart independence is
what makes *one* point of the fibre enough.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 0CIC](https://stacks.math.columbia.edu/tag/0CIC)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of the 1-morphism attached to a morphism of algebraic spaces -/

/-- **Stacks 0458 read in the 2-category of algebraic stacks.** The 1-morphism of algebraic
stacks attached to a composite of morphisms of algebraic spaces over `S` is the composite of the
two 1-morphisms, on the nose. This is
`AlgebraicGeometry.Stack.associatedMap_comp`, the 1-morphisms and 2-morphisms of a full
sub-2-category being those of the ambient one. -/
theorem algebraicSpaceStackMap_comp {T G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (m : T ⟶ G) (n : G ⟶ H) :
    algebraicSpaceStackMap.{u, w} B S hS hT hG m ≫
        algebraicSpaceStackMap.{u, w} B S hS hG hH n =
      algebraicSpaceStackMap.{u, w} B S hS hT hH (m ≫ n) :=
  (congrArg (fun x => (Bicategory.InducedBicategory.mkHom x :
    algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS H hH))
    (associatedMap_comp B S hS m n)).symm

/-! ### The chart base change along a chart by an algebraic space -/

/-- **Stacks 0300 at a chart by an algebraic space.** The 2-fibre product of a 1-morphism out of
an algebraic space with a 1-morphism out of another algebraic space is representable by an
algebraic space: the first is representable by algebraic spaces because its source is
representable by one and the target is an algebraic stack (**Stacks 045G**), and the second's
source is representable by one.

This is `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_chartBaseChange` with the chart
taken by an algebraic space rather than by a scheme of the site, which is the shape that the
chart independence of flatness at a point,
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_isFlatAt_representingMap`, is written
in. -/
theorem isRepresentableByAlgebraicSpace_algebraicSpaceChartBaseChange
    (𝒳₀ : AlgebraicStacks.{u, w} B S hS)
    (U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU₀ : IsAlgebraicSpace B S hS U₀)
    (f₀ : algebraicSpaceStack.{u, w} B S hS U₀ hU₀ ⟶ 𝒳₀)
    (W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₀ : IsAlgebraicSpace B S hS W₀)
    (c₀ : algebraicSpaceStack.{u, w} B S hS W₀ hW₀ ⟶ 𝒳₀) :
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS c₀ f₀).pt.val :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳₀.val
    (algebraicSpaceStack.{u, w} B S hS W₀ hW₀).val
    (algebraicSpaceStack.{u, w} B S hS U₀ hU₀).val c₀.hom.hom f₀.hom.hom
    (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source.{u, w} B S hS 𝒳₀ U₀ hU₀ f₀)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS W₀ hW₀)

/-! ### Flatness of the zero locus at a point, from flatness on a chart -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)

variable {r : ℕ}
  (a : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)

variable (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (Wv : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hWv : IsAlgebraicSpace B S hS Wv)
  (chart : algebraicSpaceStack.{u, w} B S hS Wv hWv ⟶ 𝒳)
  (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS chart f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)

include hP hWv in
/-- **Flatness of the zero locus over `𝒳` at a point, read on a chart.** Let `f : U ⟶ 𝒳` be a
1-morphism from an algebraic space, let `f₁, …, f_r` be global regular functions on `U`, let
`chart : Wv ⟶ 𝒳` be a relatively smooth 1-morphism from an algebraic space and let `P` represent
`U ×_𝒳 Wv`, with projections `π : P ⟶ U` and `pW : P ⟶ Wv`. If the zero locus
`V(g^*f₁, …, g^*f_r) ⊆ P` of the pulled-back functions is flat over `Wv` at a point `e₂`, then
`V(f₁, …, f_r) ⟶ 𝒳` is flat at the point of `|V(f₁, …, f_r)|` which `π(e₂)` names.

This is **Stacks 0CIC** — the chart independence of flatness at a point,
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_isFlatAt_representingMap` — at the square of
`AlgebraicGeometry.Stack.restrictionSquare`, whose representing algebraic space is
`V(g^*f₁, …, g^*f_r)` by
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange`. Because chart
independence is an equivalence, *one* point of the fibre over the marked point is enough: nothing
is asked of the other points of `|P|` above `π(e₂)`. -/
theorem isFlatAt_chartZeroLocusToStack_of_isFlatAt_vanishingSubfunctor
    (hbsm : IsRelativelySmooth B S hS chart.hom)
    (e₂ : Space.points B S hS (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).toFunctor)
    (hflat : Space.IsFlatAt B S hS
      ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
          (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).ι ≫
        chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
          (StacksRepresentableCFG.EquivalenceOver.refl _) P eP) e₂)
    (xs : Space.points B S hS (chartZeroLocus B S hS U hU a).toFunctor)
    (hxs : Space.pointsMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (chartZeroLocus B S hS U hU a).ι xs =
      Space.pointsMap B S hS P
        (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom
        (Space.pointsMap B S hS (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
          (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).toFunctor
          (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
            (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
              (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).ι e₂)) :
    AlgebraicStacks.IsFlatAt B S hS
      (algebraicSpaceStackMap.{u, w} B S hS
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
        (chartZeroLocus B S hS U hU a).ι ≫ f)
      (spacePointMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
        (representingEquivalence B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
          (StacksRepresentableCFG.EquivalenceOver.refl _)).functor xs) := by
  classical
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (restrictionSquare.{u, w} B S hS 𝒳 U (chartZeroLocus B S hS U hU a).toFunctor hU
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (chartZeroLocus B S hS U hU a).ι f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU).val
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).pt.val
      (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd.hom.hom
      (algebraicSpaceStackMap.{u, w} B S hS
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
        (chartZeroLocus B S hS U hU a).ι).hom.hom
      (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source.{u, w} B S hS
        (algebraicSpaceStack.{u, w} B S hS U hU) (chartZeroLocus B S hS U hU a).toFunctor
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (algebraicSpaceStackMap.{u, w} B S hS
          (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
          (chartZeroLocus B S hS U hU a).ι))
      ⟨P, hP, ⟨eP⟩⟩
  obtain ⟨e, he⟩ := exists_iso_vanishingSubfunctor_chartBaseChange B S hS 𝒳 U hU a f
    (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P Q hP eP eQ
  have hpt : Space.pointsMap B S hS Q e.hom
      (Space.pointsMap B S hS _ e.inv e₂) = e₂ :=
    ((Space.pointsMap_comp_apply B S hS e.inv e.hom e₂).symm.trans
      (congrArg (fun mm : (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).toFunctor ⟶
        (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
          (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).toFunctor =>
        Space.pointsMap B S hS _ mm e₂) e.inv_hom_id)).trans
      (congrFun (Space.pointsMap_id B S hS _) e₂)
  have hw0 := (isPullback_representingMap_restrictionInnerSquare B S hS 𝒳 U hU
    (chartZeroLocus B S hS U hU a)
    (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 f
    (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P Q eP eQ).w
  refine AlgebraicStacks.isFlatAt_of_isFlatAt_representingMap B S hS
    (algebraicSpaceStackMap.{u, w} B S hS
      (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
      (chartZeroLocus B S hS U hU a).ι ≫ f) hQ hWv eQ hbsm
    (Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS chart
        (algebraicSpaceStackMap.{u, w} B S hS
          (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
          (chartZeroLocus B S hS U hU a).ι ≫ f))
      (isTwoFibreProduct_restrictionSquare.{u, w} B S hS 𝒳 U
        (chartZeroLocus B S hS U hU a).toFunctor hU
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (chartZeroLocus B S hS U hU a).ι f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        chart.hom (algebraicSpaceStackMap.{u, w} B S hS
          (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
          (chartZeroLocus B S hS U hU a).ι ≫ f).hom))
    (Space.pointsMap B S hS _ e.inv e₂) _ ?_ ?_
  · -- the marked point of `|V(f₁, …, f_r)|` is the one `π(e₂)` names
    refine Eq.trans (AlgebraicStacks.spacePointMap_equivalenceOverInvMap_comp_eq B S hS
      (restrictionSquare.{u, w} B S hS 𝒳 U (chartZeroLocus B S hS U hU a).toFunctor hU
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (chartZeroLocus B S hS U hU a).ι f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart).snd Q eQ
      (Space.pointsMap B S hS _ e.inv e₂)) ?_
    refine Eq.trans (spacePointMap_representing_naturality B S hS Q
      (chartZeroLocus B S hS U hU a).toFunctor
      (restrictionSquare.{u, w} B S hS 𝒳 U (chartZeroLocus B S hS U hU a).toFunctor hU
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (chartZeroLocus B S hS U hU a).ι f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart).pt.val
      (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val eQ
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (restrictionSquare.{u, w} B S hS 𝒳 U (chartZeroLocus B S hS U hU a).toFunctor hU
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (chartZeroLocus B S hS U hU a).ι f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart).snd.hom
      (Space.pointsMap B S hS _ e.inv e₂)).symm ?_
    refine congrArg (spacePointMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
      (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
      (representingEquivalence B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
        (StacksRepresentableCFG.EquivalenceOver.refl _)).functor) ?_
    refine Space.pointsMap_injective_of_mono B S hS (chartZeroLocus B S hS U hU a).ι ?_
    refine Eq.trans ?_ hxs.symm
    have hmor : e.inv ≫ (representingMap B S hS
          (restrictionSquare.{u, w} B S hS 𝒳 U (chartZeroLocus B S hS U hU a).toFunctor hU
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
            (chartZeroLocus B S hS U hU a).ι f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart).pt.val
          (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val Q
          (chartZeroLocus B S hS U hU a).toFunctor eQ
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (restrictionSquare.{u, w} B S hS 𝒳 U (chartZeroLocus B S hS U hU a).toFunctor hU
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
            (chartZeroLocus B S hS U hU a).ι f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart).snd.hom ≫
          (chartZeroLocus B S hS U hU a).ι) =
        (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
            (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
              (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).ι ≫
          (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom :=
      (congrArg (fun mm : Q ⟶ U => e.inv ≫ mm)
        (((congrArg (fun mm : Q ⟶ P => mm ≫ (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom) he).trans
          hw0).symm)).trans (by simp)
    simp only [← Space.pointsMap_comp_apply]
    exact congrArg (fun mm : (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).toFunctor ⟶ U =>
      Space.pointsMap B S hS _ mm e₂) hmor
  · -- flatness on the chart
    refine (iff_of_eq (congrArg (fun mm : Q ⟶ Wv =>
      Space.IsFlatAt B S hS mm (Space.pointsMap B S hS _ e.inv e₂))
      (representingMap_restrictionSquare_fst.{u, w} B S hS 𝒳 U
        (chartZeroLocus B S hS U hU a).toFunctor hU
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
        (chartZeroLocus B S hS U hU a).ι f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P Q eP Wv
        (StacksRepresentableCFG.EquivalenceOver.refl _) eQ))).2 ?_
    refine (iff_of_eq (congrArg (fun mm : Q ⟶ P =>
      Space.IsFlatAt B S hS (mm ≫ chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
          (StacksRepresentableCFG.EquivalenceOver.refl _) P eP)
        (Space.pointsMap B S hS _ e.inv e₂)) he)).1 ?_
    refine (iff_of_eq (congrArg (fun mm : Q ⟶ Wv =>
      Space.IsFlatAt B S hS mm (Space.pointsMap B S hS _ e.inv e₂))
      (Category.assoc e.hom _ _))).2 ?_
    refine (Space.isFlatAt_comp_iff_of_isOpenImmersion B S hS
      (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).1 hQ hWv e.hom
      (Space.isOpenImmersion_of_isIso B S hS e.hom) _ _).2 ?_
    exact (iff_of_eq (congrArg (Space.IsFlatAt B S hS
      ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
          (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).ι ≫
        chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
          (StacksRepresentableCFG.EquivalenceOver.refl _) P eP)) hpt)).2 hflat

/-! ### Flatness of the zero locus at a point of the swept-out open subspace -/

/-- The base change of a subspace `Z ⊆ X` to an open subspace `V ⊆ X` is an open immersion into
`Z`. -/
private theorem isOpenImmersion_fromPreimage_of_isOpenSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (Z : Subfunctor X) (hZ : IsAlgebraicSpace B S hS Z.toFunctor)
    (V : Subfunctor X) (hV : Space.IsOpenSubspace B S hS V)
    (hZV : IsAlgebraicSpace B S hS (Z.preimage V.ι).toFunctor) :
    Space.IsOpenImmersion B S hS (Z.fromPreimage V.ι) :=
  Space.isOpenImmersion_of_isPullback B S hS
    (show IsPullback
      (ObjectProperty.homMk
        (X := (⟨(Z.preimage V.ι).toFunctor, hZV⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS)) (Z.preimage V.ι).ι)
      (ObjectProperty.homMk
        (X := (⟨(Z.preimage V.ι).toFunctor, hZV⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces B S hS)) (Z.fromPreimage V.ι))
      (ObjectProperty.homMk (X := (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) V.ι)
      (ObjectProperty.homMk (X := (⟨Z.toFunctor, hZ⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) Z.ι) from
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS T))
        (Subfunctor.isPullback_preimage V.ι Z).flip)
    hV.2


include hP hWv in
/-- **Flatness of the zero locus over `𝒳` at a point swept out by an open subspace of the chart
base change.** Let `W' ⊆ U ×_𝒳 𝒲` be an open subspace over which `V(g^*f₁, …, g^*f_r) ⟶ 𝒲` is
flat, as the flatness half of **Stacks 06LW** produces. Then `V(f₁, …, f_r) ⟶ 𝒳` is flat at every
point of `|V(f₁, …, f_r)|` whose image in `|U|` lies in the image of `|W'|`.

Such a point of `|U|` is the image of a point of `|W'|`, and that point lies in
`V(g^*f₁, …, g^*f_r)` because the base change of the zero locus along the projection is the zero
locus of the pulled-back functions
(`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`, on points
`AlgebraicGeometry.Space.range_pointsMap_preimage_ι`). Flatness holds there, and restricting the
source to the open subspace `W'` does not see it
(`AlgebraicGeometry.Space.isFlatAt_comp_iff_of_isOpenImmersion`), so
`AlgebraicGeometry.Stack.isFlatAt_chartZeroLocusToStack_of_isFlatAt_vanishingSubfunctor`
applies. -/
theorem isFlatAt_chartZeroLocusToStack_of_mem_image
    (hbsm : IsRelativelySmooth B S hS chart.hom)
    (W' : Subfunctor P) (hW' : Space.IsOpenSubspace B S hS W')
    (hflatW' : Space.IsFlat B S hS
      (((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
            (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
              (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).preimage W'.ι).ι ≫
        W'.ι ≫ chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
          (StacksRepresentableCFG.EquivalenceOver.refl _) P eP))
    (xs : Space.points B S hS (chartZeroLocus B S hS U hU a).toFunctor)
    (hxs : Space.pointsMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (chartZeroLocus B S hS U hU a).ι xs ∈
      Space.pointsMap B S hS P
          (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom ''
        Set.range (Space.pointsMap B S hS W'.toFunctor W'.ι)) :
    AlgebraicStacks.IsFlatAt B S hS
      (algebraicSpaceStackMap.{u, w} B S hS
        (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1 hU
        (chartZeroLocus B S hS U hU a).ι ≫ f)
      (spacePointMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
        (representingEquivalence B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1).val
          (StacksRepresentableCFG.EquivalenceOver.refl _)).functor xs) := by
  classical
  obtain ⟨p₁, ⟨w₁, hw₁⟩, hp₁⟩ := hxs
  have hAW : IsAlgebraicSpace B S hS ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).preimage W'.ι).toFunctor :=
    (Space.isClosedSubspace_preimage B S hS W'.ι
      (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)) hP hW'.1
      (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨P, hP⟩ _)).1
  -- the point of `|W'|` lies in the zero locus of the pulled-back functions
  have hmem : w₁ ∈ Set.range (Space.pointsMap B S hS
      ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).preimage W'.ι).toFunctor
      ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).preimage W'.ι).ι) := by
    rw [Space.range_pointsMap_preimage_ι B S hS W'.ι]
    refine Set.mem_preimage.2 ?_
    have hrange := congrArg (fun Z' : Subfunctor P =>
      Set.range (Space.pointsMap B S hS Z'.toFunctor Z'.ι))
      (Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage B S hS
        (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP) a)
    rw [hrange, Space.range_pointsMap_preimage_ι B S hS
      (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom]
    exact Set.mem_preimage.2 (hw₁ ▸ hp₁ ▸ Set.mem_range_self xs)
  obtain ⟨eA, heA⟩ := hmem
  -- flatness of the zero locus over the chart at that point
  have hZP : IsAlgebraicSpace B S hS (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).toFunctor :=
    (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨P, hP⟩ _).1
  have hoi := isOpenImmersion_fromPreimage_of_isOpenSubspace B S hS hP
    (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)) hZP W' hW' hAW
  have hfp2 := Subfunctor.fromPreimage_ι (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
    (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
      (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)) W'.ι
  have hflatA : Space.IsFlatAt B S hS
      (((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
          (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).fromPreimage W'.ι) ≫
        ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
            (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
              (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).ι ≫
          chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
            (StacksRepresentableCFG.EquivalenceOver.refl _) P eP)) eA := by
    have := (Space.isFlat_iff_forall_isFlatAt B S hS _).1 hflatW' eA
    rwa [← Category.assoc, ← hfp2, Category.assoc] at this
  refine isFlatAt_chartZeroLocusToStack_of_isFlatAt_vanishingSubfunctor.{u, w} B S hS 𝒳 U hU a f
    Wv hWv chart P hP eP hbsm
    (Space.pointsMap B S hS _ ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).fromPreimage W'.ι) eA)
    ((Space.isFlatAt_comp_iff_of_isOpenImmersion B S hS hZP hAW hWv _ hoi _ eA).1
      hflatA) xs ?_
  -- the marked point of `|U|`
  have h1 : Space.pointsMap B S hS _ (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).ι
      (Space.pointsMap B S hS _ ((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).fromPreimage W'.ι) eA) =
      Space.pointsMap B S hS W'.toFunctor W'.ι w₁ := by
    rw [← Space.pointsMap_comp_apply, hfp2, Space.pointsMap_comp_apply, heA]
  rw [h1, hw₁, hp₁]

/-! ### The open subspace swept out by the chart -/

variable (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

include hU hP hWv hFsp in
/-- **The flatness half of Stacks 06LW, applied on a chart of `𝒳`.** Let `chart : Wv ⟶ 𝒳` be a
surjective 1-morphism from an algebraic space and let `P` represent `U ×_𝒳 Wv`. Under the three
hypotheses of **Stacks 06MD** there is an open subspace `W' ⊆ P` whose image in `|U|` contains
`p(z)` and over which the zero locus of the pulled-back functions is flat over `Wv`.

The fibre over a lifted field-valued point of the chart, with the regular sequence transported
into it, is `AlgebraicGeometry.Stack.exists_chartFibre_isPullback_isRegular`; the projection
`P ⟶ Wv` is flat and locally of finite presentation by base change
(`AlgebraicGeometry.Stack.isFlat_representingMap_chartBaseChange_fst` and its companion); and
`Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_geometricFiber` is
Stacks 06LW. -/
theorem exists_isOpenSubspace_isFlat_chartVanishingSubfunctor
    (hchartsurj : IsSurjective B S hS chart)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (z : Space.GeometricPoint B S hS Fsp)
    (hreg : FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z) :
    ∃ (W' : Subfunctor P) (_ : Space.IsOpenSubspace B S hS W'),
      Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z.image ∈
        Space.pointsMap B S hS P
            (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
              (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom ''
          Set.range (Space.pointsMap B S hS W'.toFunctor W'.ι) ∧
      Space.IsFlat B S hS
        (((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
              (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
                (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).preimage W'.ι).ι ≫
          W'.ι ≫ chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
            (StacksRepresentableCFG.EquivalenceOver.refl _) P eP) := by
  classical
  obtain ⟨k', _, hk', b', t, G, hG, ξ, πG, zG, hsqG, hzG, hregG⟩ :=
    exists_chartFibre_isPullback_isRegular.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF
      (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
      (StacksRepresentableCFG.EquivalenceOver.refl _) P hP eP hchartsurj z hreg
  obtain ⟨W', hW', hmemW', hflatW'⟩ :=
    Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_geometricFiber B S hS
      ⟨P, hP⟩ ⟨Wv, hWv⟩ ⟨G, hG⟩
      (chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
        (StacksRepresentableCFG.EquivalenceOver.refl _) P eP)
      (isFlat_representingMap_chartBaseChange_fst.{u, w} B S hS 𝒳
        (algebraicSpaceStack.{u, w} B S hS U hU) (algebraicSpaceStack.{u, w} B S hS Wv hWv) f
        chart P Wv hP hWv eP (StacksRepresentableCFG.EquivalenceOver.refl _) hflat)
      (isLocallyOfFinitePresentation_representingMap_chartBaseChange_fst.{u, w} B S hS 𝒳
        (algebraicSpaceStack.{u, w} B S hS U hU) (algebraicSpaceStack.{u, w} B S hS Wv hWv) f
        chart P Wv hP hWv eP (StacksRepresentableCFG.EquivalenceOver.refl _) hfp)
      (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)
      hk' b' t (ObjectProperty.homMk ξ) hsqG zG hregG
  refine ⟨W', hW', ?_, hflatW'⟩
  refine ⟨Space.pointsMap B S hS G ξ zG.image, hmemW', ?_⟩
  exact (Space.pointsMap_comp_apply B S hS ξ _ zG.image).symm.trans hzG

include hU hP hWv in
/-- **The projection of the chart base change onto `U` is flat.** It is the base change of the
chart along `f`, so **Stacks 06FQ** applies at the smooth chart, read on representing algebraic
spaces by **Stacks 06FM**. -/
theorem isFlat_chartBaseChangeSpaceProjection
    (hchartsm : AlgebraicStacks.IsSmooth B S hS chart) :
    Space.IsFlat B S hS (representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).pt.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p)
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd.hom) := by
  have h : AlgebraicStacks.IsFlat B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd :=
    AlgebraicStacks.isFlat_baseChange B S hS chart f
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS chart f))
      (AlgebraicStacks.isFlat_of_isSmooth B S hS _ hchartsm)
  exact isFlat_representingMap_of_isFlat.{u, w} B S hS P U hP hU eP
    (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p)
    (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd h

include hU hP hWv in
/-- **The projection of the chart base change onto `U` is locally of finite presentation**, the
companion of `AlgebraicGeometry.Stack.isFlat_chartBaseChangeSpaceProjection` through
**Stacks 06Q4**. -/
theorem isLocallyOfFinitePresentation_chartBaseChangeSpaceProjection
    (hchartsm : AlgebraicStacks.IsSmooth B S hS chart) :
    Space.IsLocallyOfFinitePresentation B S hS (representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).pt.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
      (StacksRepresentableCFG.EquivalenceOver.refl
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p)
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd.hom) := by
  have h : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd :=
    AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS chart f
      (twoFibreProductSquareAlgebraicStacks B S hS chart f).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS chart f))
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _ hchartsm)
  exact isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w}
    B S hS P U hP hU eP (StacksRepresentableCFG.EquivalenceOver.refl
      (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p)
    (twoFibreProductSquareAlgebraicStacks B S hS chart f).snd h

include hU hP hWv in
/-- **The projection of the chart base change onto `U` is open on points**, a flat morphism of
algebraic spaces locally of finite presentation being open on points. -/
theorem isOpenMap_pointsMap_chartBaseChangeSpaceProjection
    (hchartsm : AlgebraicStacks.IsSmooth B S hS chart) :
    IsOpenMap (Space.pointsMap B S hS P
      (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
        (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom) :=
  Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hP hU _
    (isFlat_chartBaseChangeSpaceProjection.{u, w} B S hS 𝒳 U hU f Wv hWv chart P hP eP hchartsm)
    (isLocallyOfFinitePresentation_chartBaseChangeSpaceProjection.{u, w} B S hS 𝒳 U hU f
      Wv hWv chart P hP eP hchartsm)

/-! ### Flatness of the zero locus on the swept-out open subspace -/

include hU hP hWv in
/-- **The zero locus is flat over `𝒳` on an open subspace swept out by the chart base change.**
Let `W' ⊆ U ×_𝒳 𝒲` be an open subspace over which the zero locus of the pulled-back functions is
flat over the chart, and let `V ⊆ U` be an open subspace whose points all lie in the image of
`|W'|`. Then `V(f₁, …, f_r) ∩ V ⟶ 𝒳` is flat.

Flatness of a 1-morphism is flatness at every point of its source
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_forall_isFlatAt`), and restricting the source
of `V(f₁, …, f_r) ⟶ 𝒳` to the open subspace `V(f₁, …, f_r) ∩ V` does not change flatness at a
point, which is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp_algebraicSpaceStackMap_of_forall_isFlatAt`;
at each point in the image
`AlgebraicGeometry.Stack.isFlatAt_chartZeroLocusToStack_of_mem_image` supplies it. -/
theorem isFlat_zeroLocusOnOpenToStack_of_range_subset
    (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V)
    (hbsm : IsRelativelySmooth B S hS chart.hom)
    (W' : Subfunctor P) (hW' : Space.IsOpenSubspace B S hS W')
    (hflatW' : Space.IsFlat B S hS
      (((Space.vanishingSubfunctor B S hS ⟨P, hP⟩
            (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU a f
              (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP)).preimage W'.ι).ι ≫
        W'.ι ≫ chartBaseChangeChartProjection.{u, w} B S hS 𝒳 U hU f
          (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart Wv
          (StacksRepresentableCFG.EquivalenceOver.refl _) P eP))
    (hVrange : Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
      Space.pointsMap B S hS P
          (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
            (algebraicSpaceStack.{u, w} B S hS Wv hWv) chart P hP eP).hom ''
        Set.range (Space.pointsMap B S hS W'.toFunctor W'.ι)) :
    AlgebraicStacks.IsFlat B S hS
      (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) := by
  classical
  have hZ : IsAlgebraicSpace B S hS (chartZeroLocus B S hS U hU a).toFunctor :=
    (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a).1
  have hZV : IsAlgebraicSpace B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor :=
    (isClosedSubspace_zeroLocusOnOpen B S hS U hU a V hV).1
  have hoiV := isOpenImmersion_fromPreimage_of_isOpenSubspace B S hS hU
    (chartZeroLocus B S hS U hU a) hZ V hV hZV
  have hforall : ∀ y : AlgebraicStacks.points B S hS
      (algebraicSpaceStack.{u, w} B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor hZV),
      AlgebraicStacks.IsFlatAt B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hZ hU (chartZeroLocus B S hS U hU a).ι ≫ f)
        (AlgebraicStacks.pointsMap B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hZV hZ
            ((chartZeroLocus B S hS U hU a).fromPreimage V.ι)) y) := by
    intro y
    obtain ⟨ys, hys⟩ := (bijective_spacePointMap_representing B S hS
      (zeroLocusOnOpen B S hS U hU a V).toFunctor
      (algebraicSpaceStack.{u, w} B S hS
        (zeroLocusOnOpen B S hS U hU a V).toFunctor hZV).val
      (StacksRepresentableCFG.EquivalenceOver.refl _)).surjective y
    have hnat := spacePointMap_representing_naturality B S hS
      (zeroLocusOnOpen B S hS U hU a V).toFunctor (chartZeroLocus B S hS U hU a).toFunctor
      (algebraicSpaceStack.{u, w} B S hS
        (zeroLocusOnOpen B S hS U hU a V).toFunctor hZV).val
      (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor hZ).val
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (algebraicSpaceStackMap.{u, w} B S hS hZV hZ
        ((chartZeroLocus B S hS U hU a).fromPreimage V.ι)).hom ys
    have hconv2 := congrArg (fun mm : (zeroLocusOnOpen B S hS U hU a V).toFunctor ⟶
        (chartZeroLocus B S hS U hU a).toFunctor =>
      spacePointMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
        (algebraicSpaceStack.{u, w} B S hS (chartZeroLocus B S hS U hU a).toFunctor hZ).val
        (representingEquivalence B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (algebraicSpaceStack.{u, w} B S hS
            (chartZeroLocus B S hS U hU a).toFunctor hZ).val
          (StacksRepresentableCFG.EquivalenceOver.refl _)).functor
        (Space.pointsMap B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor mm ys))
      (representingMap_associatedMap B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor
        (chartZeroLocus B S hS U hU a).toFunctor
        ((chartZeroLocus B S hS U hU a).fromPreimage V.ι))
    have hkey : AlgebraicStacks.pointsMap B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hZV hZ
          ((chartZeroLocus B S hS U hU a).fromPreimage V.ι)) y =
        spacePointMap B S hS (chartZeroLocus B S hS U hU a).toFunctor
          (algebraicSpaceStack.{u, w} B S hS
            (chartZeroLocus B S hS U hU a).toFunctor hZ).val
          (representingEquivalence B S hS (chartZeroLocus B S hS U hU a).toFunctor
            (algebraicSpaceStack.{u, w} B S hS
              (chartZeroLocus B S hS U hU a).toFunctor hZ).val
            (StacksRepresentableCFG.EquivalenceOver.refl _)).functor
          (Space.pointsMap B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor
            ((chartZeroLocus B S hS U hU a).fromPreimage V.ι) ys) := by
      rw [← hys]
      exact hnat.symm.trans hconv2
    rw [hkey]
    refine isFlatAt_chartZeroLocusToStack_of_mem_image.{u, w} B S hS 𝒳 U hU a f Wv hWv chart
      P hP eP hbsm W' hW' hflatW' _ (hVrange ?_)
    rw [← Space.pointsMap_comp_apply, Subfunctor.fromPreimage_ι, Space.pointsMap_comp_apply]
    exact Set.mem_range_self _
  have hconv : algebraicSpaceStackMap.{u, w} B S hS hZV hZ
        ((chartZeroLocus B S hS U hU a).fromPreimage V.ι) ≫
      (algebraicSpaceStackMap.{u, w} B S hS hZ hU (chartZeroLocus B S hS U hU a).ι ≫ f) =
        zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV := by
    rw [← Category.assoc, algebraicSpaceStackMap_comp, Subfunctor.fromPreimage_ι]
  exact (iff_of_eq (congrArg (AlgebraicStacks.IsFlat B S hS) hconv)).1
    (AlgebraicStacks.isFlat_comp_algebraicSpaceStackMap_of_forall_isFlatAt B S hS 𝒳
      (chartZeroLocus B S hS U hU a).toFunctor (zeroLocusOnOpen B S hS U hU a V).toFunctor
      hZ hZV ((chartZeroLocus B S hS U hU a).fromPreimage V.ι) hoiV
      (algebraicSpaceStackMap.{u, w} B S hS hZ hU (chartZeroLocus B S hS U hU a).ι ≫ f)
      hforall)

/-! ### Stacks 06MD -/

include hU hFsp in
/-- **Stacks 06MD.** Let `𝒳` be an algebraic stack over `S`, let `U` be an algebraic space with a
1-morphism `f : U ⟶ 𝒳` which is flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a
field-valued point, and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`. Let
`f₁, …, f_r ∈ Γ(U, 𝒪_U)` and let `z` be a geometric point of `F` at which the `f_i` map to a
regular sequence in the étale local ring `𝒪_{F, z̄}`. Then, after replacing `U` by an open
subspace containing `p(z)`, the 1-morphism `V(f₁, …, f_r) ⟶ 𝒳` is **flat and locally of finite
presentation**.

Nothing is carried. Local finite presentation holds over *every* open subspace,
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_zeroLocusOnOpenToStack`. For flatness the
proof is the source's: base change along a smooth chart of `𝒳` by an algebraic space surjective
on objects, apply the flatness half of **Stacks 06LW** to the morphism of algebraic spaces
`U ×_𝒳 𝒲 ⟶ 𝒲` at the fibre which
`AlgebraicGeometry.Stack.exists_chartFibre_isPullback_isRegular` produces, take the open subspace
of `U` swept out by the open subspace Stacks 06LW returns — open because the projection
`U ×_𝒳 𝒲 ⟶ 𝒲` is a base change of the smooth chart, hence flat and locally of finite
presentation, hence open on points — and read flatness back point by point through the chart
independence of **Stacks 0CIC**. -/
@[stacks 06MD "the full statement: an open V ∋ p(z) with V(f₁,…,f_r) ∩ V ⟶ 𝒳 flat and locally of \
  finite presentation"]
theorem exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (z : Space.GeometricPoint B S hS Fsp)
    (hreg : FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z.image ∈
        Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
      AlgebraicStacks.IsFlat B S hS
          (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) ∧
        AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
          (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) := by
  classical
  -- a smooth chart of `𝒳` by an algebraic space, surjective on objects
  obtain ⟨Wa, hWa, ba, hbsma, hbsua⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒳.property
  obtain ⟨Pa, hPa, ⟨ePa⟩⟩ :=
    isRepresentableByAlgebraicSpace_algebraicSpaceChartBaseChange.{u, w} B S hS 𝒳 U hU f
      Wa hWa (Bicategory.InducedBicategory.mkHom ba)
  -- the flatness half of Stacks 06LW on that chart
  obtain ⟨W', hW', hmem, hflatW'⟩ :=
    exists_isOpenSubspace_isFlat_chartVanishingSubfunctor.{u, w} B S hS 𝒳 U hU a f Wa hWa
      (Bicategory.InducedBicategory.mkHom ba) Pa hPa ePa k hk toBase g Fsp hFsp eF
      (pointsMap_surjective_of_isSurjectiveOnObjects B S hS
        (𝒳 := algebraicSpaceStack.{u, w} B S hS Wa hWa) (𝒴 := 𝒳)
        (Bicategory.InducedBicategory.mkHom ba) hbsua)
      hflat hfp z hreg
  -- the projection onto `U` is open on points, being a base change of the smooth chart
  have hchartsm : AlgebraicStacks.IsSmooth B S hS
      (Bicategory.InducedBicategory.mkHom ba :
        algebraicSpaceStack.{u, w} B S hS Wa hWa ⟶ 𝒳) :=
    hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ ba Wa hWa
      (StacksRepresentableCFG.EquivalenceOver.refl _) hbsma (Space.isSmooth_id B S hS hWa)
  have hopen := isOpenMap_pointsMap_chartBaseChangeSpaceProjection.{u, w} B S hS 𝒳 U hU f
    Wa hWa (Bicategory.InducedBicategory.mkHom ba) Pa hPa ePa hchartsm
  refine ⟨Space.openSubspaceOfPoints B S hS U (Space.pointsMap B S hS Pa
      (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f
        (algebraicSpaceStack.{u, w} B S hS Wa hWa) (Bicategory.InducedBicategory.mkHom ba)
        Pa hPa ePa).hom '' Set.range (Space.pointsMap B S hS W'.toFunctor W'.ι)),
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hU _
      (hopen _ (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS W'.ι hW'.2)), ?_, ?_, ?_⟩
  · rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
    exact hmem
  · exact isFlat_zeroLocusOnOpenToStack_of_range_subset.{u, w} B S hS 𝒳 U hU a f Wa hWa
      (Bicategory.InducedBicategory.mkHom ba) Pa hPa ePa _ _ hbsma W' hW' hflatW'
      (le_of_eq (Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _))
  · exact isLocallyOfFinitePresentation_zeroLocusOnOpenToStack.{u, w} B S hS U hU a 𝒳 f hfp
      (Space.isLocallyOfFinitePresentation_ι_vanishingSubfunctor B S hS
        ⟨U, hU⟩ a) _ _

end AlgebraicGeometry.Stack

end
