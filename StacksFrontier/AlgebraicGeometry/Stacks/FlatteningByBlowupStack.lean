module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.Main
public import StacksFrontier.AlgebraicGeometry.Stacks.StackFlatteningByBlowup

/-!
# Flattening an algebraic stack over an algebraic space by blowing up

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an
open subspace. Assume that `Y` is quasi-compact and quasi-separated, that `f` is of finite type
and quasi-separated, that `V` is quasi-compact and that `𝒳_V ⟶ V` is flat and locally of finite
presentation. Then there are a `V`-admissible blowup `Y' ⟶ Y` and a closed substack
`𝒳' ⊆ 𝒳_{Y'}` with `𝒳'_V = 𝒳_V` such that `𝒳' ⟶ Y'` is flat and of finite presentation.
This is [Stacks, Tag 0CQ4].

## Main results

* `exists_admissibleBlowup_flat_finitePresentation_closedSubstack`: [Stacks, Tag 0CQ4].

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flattening by blowing up.** Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an
algebraic space and `V ⊆ Y` an open subspace, with (1) `Y` quasi-compact and quasi-separated, (2)
`f` of finite type and quasi-separated, (3) `V` quasi-compact and (4) `𝒳_V ⟶ V` flat and locally
of finite presentation. Then there are a `V`-admissible blowup `b : Y' ⟶ Y` and a closed substack
`𝒳' ⊆ 𝒳_{Y'}` containing every object of `𝒳_{Y'}` over `b⁻¹V` (so `𝒳'_V = 𝒳_V`, `b` being an
isomorphism over `V`) such that `𝒳' ⟶ Y'` is flat and of finite presentation. -/
@[stacks 0CQ4]
theorem exists_admissibleBlowup_flat_finitePresentation_closedSubstack
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
                (algebraicSpaceStackMap.{u, w} B S hS Y'.2 hY b.hom) f).fst) :=
  exists_isAdmissibleBlowup_isClosedSubstack_isFlat_isFinitePresentation B S hS
    (fun g U h1 h2 h3 h4 h5 h6 h7 =>
      Space.exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransform_of_isFiniteType
        g U h1 h2 h3 h4 h5 h6 h7)
    hY hYqc hYqs f hft hqs V hV hVqc hflat hlfp

end AlgebraicGeometry.Stack.AlgebraicStacks

end
