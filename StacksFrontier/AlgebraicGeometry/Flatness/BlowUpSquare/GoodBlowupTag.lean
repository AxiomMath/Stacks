module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupIsGood
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupUniversal

/-!
# Stacks tag 0GTY: the universal good-triple modification exists and is unique

Let `(X, D, M)` be a triple as in Situation 0F8S.  Stacks tag 0GTY asserts that there is a unique
morphism `b : X' ⟶ X` such that

1. the pullback `D' = b⁻¹D` is defined and `(X', D', M')` is a good triple, where `M' = Lb^*M`,
   and
2. every morphism of schemes `h : Y ⟶ X` for which the pullback `E = h⁻¹D` is defined and
   `(Y, E, Lh^*M)` is a good triple factors uniquely through `b`,

and moreover that over an affine chart `(U, A, f, M^•)` the restriction `b⁻¹(U) ⟶ U` is the
blowing up of `U` in the product of the ideals `I_i(M^•, f)`.

This file assembles the existence and uniqueness assertion from the two conditions proved for the
glued morphism in `GoodBlowupIsGood.lean` and `GoodBlowupUniversal.lean`, and reads off the
affine-chart description.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowup_goodBlowupToBase`: the glued
  morphism has conditions (1) and (2).
* `AlgebraicGeometry.ComplexAndDivisorSituation.existsUnique_isGoodBlowup`: **Stacks tag 0GTY,
  the existence and uniqueness assertion.**
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.existsUnique_iso_preimage_blowUp`:
  **Stacks tag 0GTY, the affine-chart description of `b`.**

## Implementation notes

The affine-chart description is read off
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.restrict` and
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.existsUnique_iso`: the restriction
of `b` over `U` and the blowing up of `U` in `∏ᵢ I_i(M^•, f)` both have the two conditions of the
tag over `U`, hence are identified by a unique isomorphism over `X`, which for morphisms with
image in `U` is the same as an isomorphism over `U` because the inclusion of `U` is a
monomorphism.

The chart used to build the piece of the gluing over a given member of the basis is a chosen one,
so the description is stated for an arbitrary chart; it holds for all of them at once because any
two charts with the same domain give blowups with the same two conditions over that domain.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-- **The glued morphism has conditions (1) and (2) of Stacks tag 0GTY.** -/
theorem isGoodBlowup_goodBlowupToBase : S.IsGoodBlowup S.goodBlowupToBase :=
  ⟨S.isGoodOver_goodBlowupToBase, fun h hh => S.existsUnique_lift_goodBlowupToBase h hh⟩

/-- **Stacks tag 0GTY: the existence and uniqueness assertion.**  In Situation 0F8S there is a
morphism `b : X' ⟶ X` such that

1. the pullback `D' = b⁻¹D` is defined and `(X', D', Lb^*M)` is a good triple, and
2. every morphism `h : Y ⟶ X` for which `h⁻¹D` is defined and `(Y, h⁻¹D, Lh^*M)` is a good triple
   factors uniquely through `b`,

and any morphism with those two properties is identified with it by a unique isomorphism over
`X`.

The morphism is `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`, obtained by
blowing up each affine chart in the product of its determinantal ideals and gluing over the basis
of chart domains; the uniqueness is
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.existsUnique_iso`. -/
@[stacks 0GTY "the existence and uniqueness assertion: there is a morphism `b : X' ⟶ X` whose \
pullback of `D` is defined and makes the pulled-back triple good, through which every morphism \
to `X` with defined pullback of `D` and good pulled-back triple factors uniquely, and any two \
such morphisms are identified by a unique isomorphism over `X`"]
theorem existsUnique_isGoodBlowup :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ S.X), S.IsGoodBlowup b ∧
      ∀ (X'' : Scheme.{u}) (b' : X'' ⟶ S.X), S.IsGoodBlowup b' →
        ∃! e : X'' ≅ X', e.hom ≫ b = b' :=
  ⟨S.goodBlowup, S.goodBlowupToBase, S.isGoodBlowup_goodBlowupToBase,
    fun _ _ hb' => hb'.existsUnique_iso S.isGoodBlowup_goodBlowupToBase⟩

namespace AffineChart

/-- **Stacks tag 0GTY: the affine-chart description of `b`.**  Over an affine chart
`(U, A, f, M^•)` for the triple, the restriction `b⁻¹(U) ⟶ U` of the morphism of the tag is the
blowing up of `U` in the product `∏ᵢ I_i(M^•, f)` of the determinantal ideals of the chart: there
is exactly one isomorphism `b⁻¹(U) ≅ U'` over `U` between the two.

Both morphisms have the two conditions of the tag over `U` — the restriction of `b` by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.restrict`, the blowing up of the
chart by `AffineChart.isGoodBlowupOver_chartBlowupToBase` — so they are identified by a unique
isomorphism over `X`, and over `U` that is the same thing. -/
@[stacks 0GTY "the affine-chart description: over an affine chart `(U, A, f, M^•)` the \
restriction `b⁻¹(U) ⟶ U` of the morphism of the tag is the blowing up of `U` in the product of \
the determinantal ideals `I_i(M^•, f)` of the chart, by a unique isomorphism over `U`"]
theorem existsUnique_iso_preimage_blowUp (C : AffineChart S) :
    ∃! e : (S.goodBlowupToBase ⁻¹ᵁ (C.U : S.X.Opens)).toScheme ≅
        AlgebraicGeometry.blowUp C.blowupCentreIdealSheaf,
      e.hom ≫ AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf =
        S.goodBlowupToBase ∣_ (C.U : S.X.Opens) := by
  have hiff : ∀ e : (S.goodBlowupToBase ⁻¹ᵁ (C.U : S.X.Opens)).toScheme ≅
      AlgebraicGeometry.blowUp C.blowupCentreIdealSheaf,
      (e.hom ≫ AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf =
          S.goodBlowupToBase ∣_ (C.U : S.X.Opens)) ↔
        (e.hom ≫ C.chartBlowupToBase =
          (S.goodBlowupToBase ⁻¹ᵁ (C.U : S.X.Opens)).ι ≫ S.goodBlowupToBase) := by
    refine fun e => ⟨fun h => ?_, fun h => (cancel_mono (C.U : S.X.Opens).ι).mp ?_⟩
    · rw [show C.chartBlowupToBase =
          AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf ≫
            (C.U : S.X.Opens).ι from rfl,
        ← Category.assoc, h, morphismRestrict_ι]
    · rwa [morphismRestrict_ι, Category.assoc]
  obtain ⟨e, he, huniq⟩ := (((S.isGoodBlowupOver_top_iff S.goodBlowupToBase).mpr
    S.isGoodBlowup_goodBlowupToBase).restrict
      (le_top : (C.U : S.X.Opens) ≤ ⊤)).existsUnique_iso
    C.isGoodBlowupOver_chartBlowupToBase
  exact ⟨e, (hiff e).mpr he, fun e' h => huniq e' ((hiff e').mp h)⟩

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation

end
