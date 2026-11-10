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
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty

/-!
# Flattening an algebraic stack over an algebraic space by blowing up (Stacks 0CQ4)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an
open subspace, with `Y` quasi-compact and quasi-separated, `f` of finite type and
quasi-separated, `V` quasi-compact and `𝒳_V ⟶ V` flat and locally of finite presentation.
[Stacks, Tag 0CQ4] produces a `V`-admissible blowup `Y' ⟶ Y` and a closed substack
`𝒳' ⊆ 𝒳_{Y'}` with `𝒳'_V = 𝒳_V` which is flat and of finite presentation over `Y'`.

## Main results

* `exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation`: [Stacks, Tag 0CQ4],
  deduced from the statement of [Stacks, Tag 087E]; unregistered.
* `isQuasiCompactMorphism_isQuasiSeparated_comp_fst_of_isClosedImmersion`: a closed
  substack of a base change of a quasi-compact quasi-separated 1-morphism is quasi-compact and
  quasi-separated over the new base.
* `AlgebraicGeometry.Space.preimage_le_openComplement_preimage_of_disjoint`: the inverse image
  of an open subspace disjoint from a closed subspace lies in the complement of the inverse image
  of the closed subspace.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open subspace disjoint from a closed subspace pulls back into the complement.** For
`b : A' ⟶ A`, an open subspace `V ⊆ A` and a closed subspace `Z ⊆ A` with disjoint point sets,
the inverse image `b⁻¹V` lies in the open complement of `b⁻¹Z` in `A'`. -/
theorem preimage_le_openComplement_preimage_of_disjoint {A A' : AlgebraicSpaces B S hS}
    (b : A' ⟶ A) (V : OpenSubspaces B S hS A.1) (Z : ClosedSubspaces B S hS A.1)
    (h : Disjoint (subspacePointSet B S hS A.1 V.1) (subspacePointSet B S hS A.1 Z.1)) :
    V.1.preimage b.hom ≤
      (openComplementOfClosedSubspace B S hS A' (preimageClosedSubspace b Z)).1 := by
  refine le_of_range_pointsMap_ι_subset B S hS
    (openComplementOfClosedSubspace B S hS A' (preimageClosedSubspace b Z)).2 ?_
  change _ ⊆ subspacePointSet B S hS A'.1
    (openComplementOfClosedSubspace B S hS A' (preimageClosedSubspace b Z)).1
  rw [subspacePointSet_openComplement, range_pointsMap_preimage_ι]
  intro x hx hxZ
  change x ∈ Set.range (pointsMap B S hS (Z.1.preimage b.hom).toFunctor
    (Z.1.preimage b.hom).ι) at hxZ
  rw [range_pointsMap_preimage_ι] at hxZ
  exact Set.disjoint_left.mp h hx hxZ

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_StackFlatteningByBlowup :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_StackFlatteningByBlowup
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A closed substack of a base change of a quasi-compact quasi-separated 1-morphism is
quasi-compact and quasi-separated over the new base.** For `f : 𝒳 ⟶ 𝒴` quasi-compact and
quasi-separated, `g : 𝒴' ⟶ 𝒴` and a closed immersion `i : 𝒵 ⟶ 𝒴' ×_𝒴 𝒳`, the composite of `i`
with the projection to `𝒴'` is quasi-compact (Stacks 050V, 0CL1, 050W) and quasi-separated
(Stacks 050F, 050E, 050K). -/
theorem isQuasiCompactMorphism_isQuasiSeparated_comp_fst_of_isClosedImmersion
    {𝒳 𝒴 𝒴' 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (hf : Stack.IsQuasiCompactMorphism B S hS f) (hfs : IsQuasiSeparated B S hS f)
    (i : 𝒵 ⟶ (twoFibreProductSquare B S hS g f).pt) (hi : IsClosedImmersion B S hS i) :
    Stack.IsQuasiCompactMorphism B S hS (i ≫ (twoFibreProductSquare B S hS g f).fst) ∧
      IsQuasiSeparated B S hS (i ≫ (twoFibreProductSquare B S hS g f).fst) := by
  have hQ := isTwoFibreProduct_twoFibreProductSquare B S hS g f
  refine ⟨Stack.isQuasiCompactMorphism_comp B S hS _ _
    (isQuasiCompactMorphism_of_isClosedImmersion B S hS i hi)
    (Stack.isQuasiCompactMorphism_baseChange B S hS f g _ hQ hf), ?_⟩
  exact isQuasiSeparated_comp B S hS _ _
    (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isClosedImmersion B S hS i hi))
    (isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f g _
      (Bicategory.isTwoFibreProduct_swap hQ) hfs)

/-- **[Stacks, Tag 0CQ4], from the statement of [Stacks, Tag 087E].** Let `f : 𝒳 ⟶ Y` be a
1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an open subspace, with `Y`
quasi-compact and quasi-separated, `f` of finite type and quasi-separated, `V` quasi-compact and
`𝒳_V ⟶ V` flat and locally of finite presentation. Then there are a `V`-admissible blowup
`b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳_{Y'}` containing every object over `b⁻¹V` (so
`𝒳'_V = 𝒳_V`) such that `𝒳' ⟶ Y'` is flat and of finite presentation.

**Unregistered: it waits on [Stacks, Tag 087E]**; `h087E` is the statement
of 087E at the source's hypotheses. With `h087E` discharged this is
[Stacks, Tag 0CQ4].

The proof is the source's: an affine smooth chart `U ⟶ 𝒳` gives `U ⟶ Y` of finite type, flat
and locally of finite presentation over `V`; 087E gives the blowup with `U'` flat and of finite
presentation over `Y'`. The two inverse images of `U'` along the projections of the
self-intersection of a chart of `𝒳_{Y'}` are flat over `Y'` and contain the complement of the
exceptional divisor, hence agree, so `U'` cuts out a closed substack (Stacks 0507), flat and of
finite presentation over `Y'` because `U'` is. -/
theorem exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation
    (h087E : ∀ {A X : AlgebraicSpaces B S hS} (g : X ⟶ A) (U : Space.OpenSubspaces B S hS A.1),
      Space.IsQuasiCompactSpace B S hS A.1 →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.1 →
      Space.IsQuasiCompactSpace B S hS U.1.toFunctor → Space.IsFiniteType B S hS g.hom →
      Space.IsQuasiSeparated B S hS g.hom → Space.IsFlat B S hS (pullback.snd g.hom U.1.ι) →
      Space.IsLocallyOfFinitePresentation B S hS (pullback.snd g.hom U.1.ι) →
      ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : Space.ClosedSubspaces B S hS A.1),
        Space.IsFinitePresentation B S hS Z.1.ι ∧
          Disjoint (Space.subspacePointSet B S hS A.1 U.1)
            (Space.subspacePointSet B S hS A.1 Z.1) ∧
          Space.IsBlowupAlong B S hS Z b ∧
          Space.IsFlat B S hS
            (Space.strictTransformSpaceToBlowUp B S hS g b (Z.1.preimage b.hom)).hom ∧
          Space.IsFinitePresentation B S hS
            (Space.strictTransformSpaceToBlowUp B S hS g b (Z.1.preimage b.hom)).hom)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hft : IsFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor)
    (hflat : IsFlat B S hS
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (hlfp : IsLocallyOfFinitePresentation B S hS
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ ⟨Y, hY⟩),
      Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ b ∧
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
  obtain ⟨U, -, c, φ, hcsm, hcsu, ⟨ec⟩, hφft, -, hφqs⟩ :=
    Stack.exists_isAffine_smooth_surjective_chart B S hS hY hYqc hYqs f hft
  have hUsp := isAlgebraicSpace_yoneda B S hS U
  -- `U_V ⟶ V` is flat and locally of finite presentation, read on the base-changed chart
  obtain ⟨hφVfl, hφVlfp⟩ := Stack.isFlat_isLocallyOfFinitePresentation_pullback_fst_of_isFlat
    B S hS hY hV.1 hUsp (isAlgebraicSpace_pullback B S hS φ V.ι hUsp hV.1 hY) f V.ι c φ ec hcsm
    (IsPullback.of_hasPullback φ V.ι).flip _
    (isTwoFibreProduct_twoFibreProductSquare B S hS _ f) hflat hlfp
  -- Stacks 087E for `U ⟶ Y`
  let A : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hUsp⟩
  let g : X ⟶ A := ObjectProperty.homMk φ
  obtain ⟨Y', b, Z, hZfp, hdisj, hb, hU'fl, hU'fp⟩ :=
    h087E g ⟨V, hV⟩ hYqc hYqs hVqc hφft hφqs hφVfl hφVlfp
  refine ⟨Y', b, ⟨Z, hZfp, hdisj, hb⟩, ?_⟩
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
    B S hS f _ hft.2 hqs _ hci
  exact ⟨(hQfl hP).1, (hQfl hP).2, hqc, hqs'⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
