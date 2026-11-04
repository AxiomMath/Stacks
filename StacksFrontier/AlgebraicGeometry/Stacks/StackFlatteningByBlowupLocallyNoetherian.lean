module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowupLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.StackFlatteningByBlowup

/-!
# Flattening an algebraic stack by blowing up a locally Noetherian base (Stacks 0CQ4)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an
open subspace, with `Y` quasi-compact, quasi-separated and locally Noetherian, `f` of finite type
and quasi-separated, `V` quasi-compact and `𝒳_V ⟶ V` flat and locally of finite presentation.
There are a `V`-admissible blowup `Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳_{Y'}` with
`𝒳'_V = 𝒳_V` which is flat and of finite presentation over `Y'`: this is [Stacks, Tag 0CQ4] over
a locally Noetherian base.

## Main results

* `AlgebraicStacks.exists_isAdmissibleBlowup_isClosedSubstack_isFlat_of_noetherian`:
  Stacks 0CQ4 over a quasi-compact, quasi-separated, locally Noetherian base.

## Implementation notes

The proof is that of
`AlgebraicStacks.exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation`,
with the flattening of an affine smooth chart `U ⟶ Y` (Stacks 087E) taken over the locally
Noetherian base, where it is
`Space.exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_noetherian`.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CQ4 over a locally Noetherian base.** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an
algebraic stack to an algebraic space and `V ⊆ Y` an open subspace, with `Y` quasi-compact,
quasi-separated and locally Noetherian, `f` of finite type and quasi-separated, `V`
quasi-compact and `𝒳_V ⟶ V` flat and locally of finite presentation. Then there are a
`V`-admissible blowup `b : Y' ⟶ Y` and a closed substack `𝒳' ⊆ 𝒳_{Y'}` containing every object
over `b⁻¹V` (so `𝒳'_V = 𝒳_V`) such that `𝒳' ⟶ Y'` is flat and of finite presentation.

The proof is the source's: an affine smooth chart `U ⟶ 𝒳` gives `U ⟶ Y` of finite type, flat
and locally of finite presentation over `V`; Stacks 087E over the locally Noetherian `Y` gives
the blowup with the strict transform `U'` flat and of finite presentation over `Y'`, and `U'`
cuts out the closed substack (Stacks 0507). -/
theorem exists_isAdmissibleBlowup_isClosedSubstack_isFlat_of_noetherian
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hYN : Space.HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
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
    Space.exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_noetherian
      B.contains_terminal (hN := hYN) g ⟨V, hV⟩ hYqc hYqs hVqc hφft hφqs hφVfl hφVlfp
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
