module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupUniversal
import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChangeGeneral

/-!
# The two conditions of Stacks tag 0GTY over an open subset

Let `(X, D, M)` be a triple as in Situation 0F8S.  Stacks tag 0GTY produces a morphism
`b : X' ⟶ X` by blowing up each affine chart in the product of its determinantal ideals and
gluing; the gluing needs the two conditions of the tag *relativised to an open* `W ⊆ X`, so that
the blowup of a chart can be compared with the restriction of the blowup of a larger chart.

This file introduces that relativisation and proves everything about it that does not mention
the glued morphism: the blowup of a chart has the two conditions over the chart's domain, they
descend to a smaller open, and a morphism having them over `W` is unique up to a unique
isomorphism over `X`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver`: a morphism `p : P ⟶ X` whose
  image lies in `W`, which is good for the triple, and through which every morphism to `X` with
  image in `W` that is good for the triple factors uniquely.  For `W = X` this is exactly
  `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup`, by
  `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowupOver_top_iff`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodOver.comp_of_flat`: goodness of a morphism
  is inherited by its composite with a flat morphism, in particular with the inclusion of an open
  subscheme.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.isGoodBlowupOver_chartBlowupToBase`:
  **the two conditions of Stacks tag 0GTY over an affine chart.**  The blowing up of a chart in
  the product of its determinantal ideals has them over the chart's domain.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.restrict`: the two conditions
  over `W` descend to an open `V ≤ W`, for the restriction of `p` to `p⁻¹V`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.existsUnique_iso`: two morphisms
  with the two conditions over the same open are identified by a unique isomorphism over `X`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowupOver_top_iff`: over `W = X` the
  relativisation is the absolute notion.

## Implementation notes

The relativisation is phrased with the structure morphism going to `X`, not to the open
subscheme `W`: a morphism `p : P ⟶ X` together with the condition `p.opensRange ≤ W`.  This
keeps every morphism in sight in the slice over `X`, so that composing and comparing them needs
no transport along `V.toScheme ≅ W.ι ⁻¹ᵁ V`; the factorisation `P ⟶ W.toScheme`, which the
gluing datum of Stacks 01LH does ask for, is recovered where it is needed by
`AlgebraicGeometry.IsOpenImmersion.lift`.

`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodOver.comp_of_flat` is the localisation step:
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp` equates goodness of the composite
with goodness of the triple pulled back twice, which for a flat second factor is
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_flat` applied to the
once-pulled-back triple.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}}

/-! ### Goodness along a flat morphism -/

/-- **Goodness of a morphism is inherited by its composite with a flat morphism.**  If
`h : Y ⟶ X` is good for the triple `(X, D, M)` and `c : Z ⟶ Y` is flat, then `h ∘ c` is good for
the triple.

The pulled-back triple `(Y, h⁻¹D, Lh^*M)` is good because `h` is, so it is good over the flat
`c` by `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_of_flat`, and
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp` turns that into goodness of
`h ∘ c`.  In particular this applies to the inclusion of an open subscheme and to an
isomorphism. -/
theorem IsGoodOver.comp_of_flat {Y Z : Scheme.{u}} {h : Y ⟶ S.X} (hh : S.IsGoodOver h)
    (c : Z ⟶ Y) [AlgebraicGeometry.Flat c] : S.IsGoodOver (c ≫ h) :=
  have hc : Stacks.Divisors.IsPullbackDefined c (S.D.comap h) :=
    Stacks.Divisors.isPullbackDefined_of_flat c (S.D.comap h) hh.pullbackDefined
  (S.isGoodOver_comp h hh.pullbackDefined c hc).mpr
    ((S.pullback h hh.pullbackDefined).isGoodTriple_pullback c hc hh.isGoodTriple)

/-! ### The relativised conditions -/

/-- **The two conditions of Stacks tag 0GTY, relativised to an open `W ⊆ X`.**  A morphism
`p : P ⟶ X` has them if its image lies in `W`, the triple pulled back along it is good, and
every morphism `t : T ⟶ X` whose image lies in `W` and along which the pulled-back triple is good
factors uniquely through `p`.

For `W = X` this is `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup`, by
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowupOver_top_iff`; the point of carrying
the open is that the blowup of an affine chart has the conditions over that chart's domain, and
that they descend to smaller opens, which is what lets the per-chart blowups be glued. -/
structure IsGoodBlowupOver (S : ComplexAndDivisorSituation.{u, d}) (W : S.X.Opens)
    {P : Scheme.{u}} (p : P ⟶ S.X) : Prop where
  /-- The image of `p` lies in `W`. -/
  range_subset : Set.range p.base ⊆ (W : Set S.X)
  /-- Condition (1) of the tag: the triple pulled back along `p` is good. -/
  isGoodOver : S.IsGoodOver p
  /-- Condition (2) of the tag, for test morphisms with image in `W`. -/
  existsUnique_lift : ∀ {T : Scheme.{u}} (t : T ⟶ S.X),
    Set.range t.base ⊆ (W : Set S.X) → S.IsGoodOver t → ∃! k : T ⟶ P, k ≫ p = t

/-- A morphism whose image lies in an open `W` has image inside the image of the inclusion of
the open subscheme `W`, hence factors through it. -/
theorem range_subset_range_ι {P Y : Scheme.{u}} {p : P ⟶ Y} {W : Y.Opens}
    (h : Set.range p.base ⊆ (W : Set Y)) : Set.range p.base ⊆ Set.range (W.ι).base := by
  rwa [show Set.range (W.ι).base = ((W.ι).opensRange : Set Y) from rfl,
    Scheme.Opens.opensRange_ι]

/-! ### The blowup of a chart -/

namespace AffineChart

variable {C : AffineChart S}

/-- **Stacks tag 0GTY over an affine chart, in the relativised form.**  The blowing up of an
affine chart `(U, A, f, M^•)` in the product `∏ᵢ I_i(M^•, f)` of its determinantal ideals,
followed by the inclusion of `U`, has the two conditions of the tag over `U`.

Condition (1) is `AffineChart.isGoodOver_chartBlowupToBase` and condition (2) is
`AffineChart.existsUnique_lift_chartBlowup`, the latter read for a test morphism `t : T ⟶ X` with
image in `U` by factoring `t` through the open subscheme `U`. -/
theorem isGoodBlowupOver_chartBlowupToBase (C : AffineChart S) :
    S.IsGoodBlowupOver (C.U : S.X.Opens) C.chartBlowupToBase where
  range_subset := Set.range_subset_iff.2 fun z =>
    (AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf z).2
  isGoodOver := C.isGoodOver_chartBlowupToBase
  existsUnique_lift {T} t ht hgood := by
    have hfac : IsOpenImmersion.lift (C.U : S.X.Opens).ι t (range_subset_range_ι ht) ≫
        (C.U : S.X.Opens).ι = t :=
      IsOpenImmersion.lift_fac _ _ _
    have hgood' : S.IsGoodOver
        (IsOpenImmersion.lift (C.U : S.X.Opens).ι t (range_subset_range_ι ht) ≫
          (C.U : S.X.Opens).ι) := by
      rwa [hfac]
    obtain ⟨k, hk, huniq⟩ := C.existsUnique_lift_chartBlowup
      (IsOpenImmersion.lift (C.U : S.X.Opens).ι t (range_subset_range_ι ht)) hgood'
    refine ⟨k, ?_, fun l hl => huniq l ?_⟩
    · change k ≫ AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf ≫
        (C.U : S.X.Opens).ι = t
      rw [← Category.assoc, hk, hfac]
    · refine (cancel_mono (C.U : S.X.Opens).ι).mp ?_
      rw [Category.assoc, hfac]
      exact hl

end AffineChart

/-! ### Descent to a smaller open -/

namespace IsGoodBlowupOver

variable {W V : S.X.Opens} {P : Scheme.{u}} {p : P ⟶ S.X}

/-- **The two conditions of Stacks tag 0GTY descend to a smaller open.**  If `p : P ⟶ X` has them
over `W` and `V ≤ W`, then the restriction of `p` to the open `p⁻¹V ⊆ P` has them over `V`.

Goodness of the restriction is `IsGoodOver.comp_of_flat` for the inclusion of an open subscheme.
For the universal property, a test morphism with image in `V` has image in `W`, so it factors
uniquely through `p`; the factorisation has image in `p⁻¹V`, hence factors through the open
subscheme, and that factorisation is unique because the inclusion of an open subscheme is a
monomorphism.

This is the sentence of the proof of the tag that `b_{U₁}` is canonically isomorphic to the
restriction of `b_{U₂}` over `U₁`: both have the two conditions over `U₁`, so
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.existsUnique_iso` identifies
them. -/
theorem restrict (hp : S.IsGoodBlowupOver W p) (hVW : V ≤ W) :
    S.IsGoodBlowupOver V ((p ⁻¹ᵁ V).ι ≫ p) where
  range_subset := Set.range_subset_iff.2 fun z => z.2
  isGoodOver := hp.isGoodOver.comp_of_flat (p ⁻¹ᵁ V).ι
  existsUnique_lift {T} t ht hgood := by
    obtain ⟨k, hk, huniq⟩ := hp.existsUnique_lift t (ht.trans hVW) hgood
    have hkr : Set.range k.base ⊆ Set.range ((p ⁻¹ᵁ V).ι).base :=
      range_subset_range_ι (by
        rintro y ⟨z, rfl⟩
        change p.base (k.base z) ∈ V
        rw [← Scheme.Hom.comp_apply, hk]
        exact Set.range_subset_iff.mp ht z)
    have hfac : IsOpenImmersion.lift ((p ⁻¹ᵁ V).ι) k hkr ≫ (p ⁻¹ᵁ V).ι = k :=
      IsOpenImmersion.lift_fac _ _ _
    refine ⟨IsOpenImmersion.lift ((p ⁻¹ᵁ V).ι) k hkr, ?_, fun l hl => ?_⟩
    · change IsOpenImmersion.lift ((p ⁻¹ᵁ V).ι) k hkr ≫ (p ⁻¹ᵁ V).ι ≫ p = t
      rw [← Category.assoc, hfac, hk]
    · refine (cancel_mono ((p ⁻¹ᵁ V).ι)).mp ?_
      rw [hfac]
      exact huniq _ ((Category.assoc _ _ _).trans hl)

/-! ### Uniqueness -/

/-- A self-map of `P` over `X` is the identity: both it and the identity are factorisations of
`p` through `p`, which are unique. -/
theorem eq_id_of_comp_eq (hp : S.IsGoodBlowupOver W p) {k : P ⟶ P} (hk : k ≫ p = p) :
    k = 𝟙 P := by
  obtain ⟨_, _, huniq⟩ := hp.existsUnique_lift p hp.range_subset hp.isGoodOver
  rw [huniq k hk, ← huniq (𝟙 P) (Category.id_comp p)]

/-- **Two morphisms with the two conditions of Stacks tag 0GTY over the same open are identified
by a unique isomorphism over `X`.**  Each factors through the other, and both composites are
identities by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.eq_id_of_comp_eq`. -/
theorem existsUnique_iso {P₁ P₂ : Scheme.{u}} {p₁ : P₁ ⟶ S.X} {p₂ : P₂ ⟶ S.X}
    (h₁ : S.IsGoodBlowupOver W p₁) (h₂ : S.IsGoodBlowupOver W p₂) :
    ∃! e : P₁ ≅ P₂, e.hom ≫ p₂ = p₁ := by
  obtain ⟨k, hk, hkuniq⟩ := h₂.existsUnique_lift p₁ h₁.range_subset h₁.isGoodOver
  obtain ⟨l, hl, -⟩ := h₁.existsUnique_lift p₂ h₂.range_subset h₂.isGoodOver
  refine ⟨⟨k, l, h₁.eq_id_of_comp_eq ?_, h₂.eq_id_of_comp_eq ?_⟩, hk, ?_⟩
  · rw [Category.assoc, hl, hk]
  · rw [Category.assoc, hk, hl]
  · exact fun e he => Iso.ext (hkuniq e.hom he)

end IsGoodBlowupOver

/-! ### The absolute notion -/

/-- **Over the whole of `X` the relativised conditions are the conditions of Stacks tag 0GTY.**
The condition on the image is vacuous and every morphism to `X` has image in `X`. -/
theorem isGoodBlowupOver_top_iff {X' : Scheme.{u}} (b : X' ⟶ S.X) :
    S.IsGoodBlowupOver ⊤ b ↔ S.IsGoodBlowup b :=
  ⟨fun h => ⟨h.isGoodOver, fun t hgood => h.existsUnique_lift t (fun _ _ => trivial) hgood⟩,
    fun h => ⟨fun _ _ => trivial, h.isGoodOver, fun t _ hgood => h.existsUnique_lift t hgood⟩⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
