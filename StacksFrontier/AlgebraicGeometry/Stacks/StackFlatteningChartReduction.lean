module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFlatteningChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedImmersionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatClosedSubstackOverCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.StackFlatteningByBlowup
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty

/-!
# Flattening an algebraic stack by flattening an affine smooth chart (towards Stacks 0CQ4)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an
open subspace. Let `c : U ⟶ 𝒳` be a smooth surjective chart by an affine scheme, with
`φ : U ⟶ Y` the induced morphism, and let `b : Y' ⟶ Y` be a `V`-admissible blowup, with centre
`Z`, such that the strict transform `U'` of `U` is flat and of finite presentation over `Y'`.
If `f` is quasi-compact and quasi-separated, then there is a closed substack `𝒳' ⊆ 𝒳_{Y'}`
containing every object over `b⁻¹V` (so `𝒳'_V = 𝒳_V`) which is flat and of finite presentation
over `Y'`.

This is the whole of the proof of [Stacks, Tag 0CQ4] after the application of
[Stacks, Tag 087E] to `U ⟶ Y`: the strict transform `R'` of `R = U ×_𝒳 U` is the inverse image
of `U'` along both projections (Stacks 0865, since they are flat), so `U'` is `R`-invariant and
cuts out a closed substack (Stacks 0507), flat and locally of finite presentation over `Y'`
because `U'` is, and quasi-compact quasi-separated over `Y'` because `f` is and closed immersions
are.

## Main results

* `exists_isClosedSubstack_isFlat_isFinitePresentation_of_flatteningBlowup`: the closed
  substack cut out by a flattening blowup of an affine smooth chart.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flattening an algebraic stack by flattening an affine smooth chart.** Let
`f : 𝒳 ⟶ Y` be a quasi-compact quasi-separated 1-morphism from an algebraic stack to an algebraic
space, `V ⊆ Y` an open subspace, `c : U ⟶ 𝒳` a smooth surjective chart by an affine scheme with
`c ≫ f ≅ φ`, and `b : Y' ⟶ Y` the blowup of `Y` along a closed subspace `Z` of finite
presentation disjoint from `V`, such that the strict transform of `U` along `b` is flat and of
finite presentation over `Y'`. Then there is a closed substack `𝒳' ⊆ 𝒳_{Y'}` containing every
object over `b⁻¹V`, flat and of finite presentation over `Y'`.

This is the proof of [Stacks, Tag 0CQ4] after its appeal to [Stacks, Tag 087E]: the two inverse
images of `U'` along the projections of the self-intersection of a chart of `𝒳_{Y'}` are flat
over `Y'` and contain the complement of the exceptional divisor, hence agree, so `U'` cuts out a
closed substack (Stacks 0507), flat and of finite presentation over `Y'` because `U'` is. -/
theorem exists_isClosedSubstack_isFlat_isFinitePresentation_of_flatteningBlowup
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hfqc : Stack.IsQuasiCompactMorphism B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    {U : BigFppfOver B S hS}
    (c : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (φ : yoneda.obj U ⟶ Y) (hcsm : AlgebraicStacks.IsSmooth B S hS c)
    (hcsu : IsSurjective B S hS c)
    (ec : c ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS U) hY φ)
    {Y' : AlgebraicSpaces B S hS} (b : Y' ⟶ ⟨Y, hY⟩) (Z : Space.ClosedSubspaces B S hS Y)
    (hdisj : Disjoint (Space.subspacePointSet B S hS Y V) (Space.subspacePointSet B S hS Y Z.1))
    (hb : Space.IsBlowupAlong B S hS Z b)
    (hU'fl : Space.IsFlat B S hS (Space.strictTransformSpaceToBlowUp B S hS
      (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (ObjectProperty.homMk φ) b
        (Z.1.preimage b.hom)).hom)
    (hU'fp : Space.IsFinitePresentation B S hS (Space.strictTransformSpaceToBlowUp B S hS
      (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (ObjectProperty.homMk φ) b
        (Z.1.preimage b.hom)).hom) :
    ∃ P : ObjectProperty (twoFibreProductSquare B S hS
        (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).pt.val.val.obj,
      IsClosedSubstack _ P ∧
      (∀ x, ((twoFibreProductSquare B S hS
          (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
            x).fiber.as ∈ (V.preimage b.hom).obj (Opposite.op ((twoFibreProductSquare B S hS
              (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst.hom.hom.obj
                x).base) →
        P x) ∧
      ∀ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased _ P),
        IsFlat B S hS (fullSubcategoryInclusion _ P hP ≫ (twoFibreProductSquare B S hS
          (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) ∧
        IsFinitePresentation B S hS (fullSubcategoryInclusion _ P hP ≫
          (twoFibreProductSquare B S hS
            (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) := by
  classical
  have hUsp := isAlgebraicSpace_yoneda B S hS U
  let A : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hUsp⟩
  let g : X ⟶ A := ObjectProperty.homMk φ
  -- the chart `U_{Y'} ⟶ 𝒳_{Y'}`
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_twoFibreProductSquare B S hS _ f
  let P := Space.strictTransformPullback B S hS g b
  obtain ⟨c', hc'sm, hc'su, ⟨ec'⟩, -⟩ := Stack.exists_smooth_surjective_baseChangedChart B S hS
    hY Y'.2 hUsp P.2 f b.hom c φ ec (IsPullback.of_hasPullback φ b.hom).flip Q hQ
  -- the closed substack cut out by the strict transform `U'`
  obtain ⟨Qp, hQc, hQV, hQfl⟩ :=
    Stack.exists_isClosedSubstack_isFlat_isLocallyOfFinitePresentation_of_openComplement_le
      Q.fst c' (hc'sm hcsm) (hc'su hcsu) (Space.strictTransformPullbackToBlowUp B S hS g b)
      ⟨ec'⟩ (Space.preimageClosedSubspace b Z) hb.isPullbackDefined
      (Space.strictTransform B S hS g b (Z.1.preimage b.hom))
      (Space.exceptionalPreimageComplement_le_strictTransformSubfunctor B S hS g b Z hb)
      hU'fl hU'fp.1
  refine ⟨Qp, hQc, fun x hx => hQV x
    (Space.preimage_le_openComplement_preimage_of_disjoint B S hS b ⟨V, hV⟩ Z hdisj _ hx),
    fun hP => ?_⟩
  obtain ⟨-, hP', hci⟩ := hQc
  obtain ⟨hqc, hqs'⟩ := isQuasiCompactMorphism_isQuasiSeparated_comp_fst_of_isClosedImmersion
    B S hS f _ hfqc hqs _ hci
  exact ⟨(hQfl hP).1, (hQfl hP).2, hqc, hqs'⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
