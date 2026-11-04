module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupGluing
import StacksFrontier.AlgebraicGeometry.OpensCoverHom

/-!
# The universal property of the glued blowup

Let `(X, D, M)` be a triple as in Situation 0F8S and let `b : X' ⟶ X` be the morphism glued from
the per-chart blowups in `GoodBlowupGluing.lean`.  This file proves condition (2) of Stacks tag
0GTY for it: a morphism `h : Y ⟶ X` for which `h⁻¹D` is defined and `(Y, h⁻¹D, Lh^*M)` is a good
triple factors uniquely through `b`.

Both halves are local on `Y`.  Over the part of `Y` lying above a member `V` of the basis of
chart domains the factorisation is the one condition (2) supplies for the `V`-piece, followed by
the chart of `X'` over `V`; over an arbitrary open the factorisation is unique because, after
restricting further to the part above a member of the basis, it is a factorisation through the
`V`-piece.  The pieces then glue by
`AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.eq_of_comp_goodBlowupToBase_eq`: a morphism to
  `X` that is good for the triple has at most one factorisation through `b`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.existsUnique_lift_goodBlowupToBase`: **condition
  (2) of Stacks tag 0GTY for the glued morphism.**

## Implementation notes

Uniqueness is proved before existence and is used in its proof, as the compatibility of the local
factorisations on the overlaps.  It is stated for an arbitrary source so that it applies to the
intersection of two members of the covering, which is not of the form `h⁻¹(V)` for `V` in the
basis.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-- The part of `T` above a member of the basis of chart domains maps into that member. -/
private theorem range_preimage_ι_comp_subset {T : Scheme.{u}} (t : T ⟶ S.X) (V : S.chartOpens) :
    Set.range ((t ⁻¹ᵁ V.1).ι ≫ t).base ⊆ (V.1 : Set S.X) := by
  rintro y ⟨z, rfl⟩
  exact z.2

/-- Two morphisms out of `T` agreeing over the part of `T` above each member of the basis of chart
domains are equal. -/
private theorem hom_ext_of_preimage_chartOpens {T Z : Scheme.{u}} (t : T ⟶ S.X) {f g : T ⟶ Z}
    (h : ∀ V : S.chartOpens, (t ⁻¹ᵁ V.1).ι ≫ f = (t ⁻¹ᵁ V.1).ι ≫ g) : f = g :=
  (Scheme.existsUnique_hom_of_opens_cover (fun V : S.chartOpens => t ⁻¹ᵁ V.1)
    (S.exists_mem_preimage_chartOpens t) (fun V => (t ⁻¹ᵁ V.1).ι ≫ f) (fun a b => by
      rw [← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])).unique
    (fun V => rfl) (fun V => (h V).symm)

/-- **A morphism with image in a member of the basis has at most one factorisation through the
glued morphism.**  Such a factorisation is, through the chart of `X'` over that member, a
factorisation through the piece, and those are unique by condition (2) of Stacks tag 0GTY for the
piece. -/
theorem eq_of_comp_goodBlowupToBase_eq_of_range_subset {T : Scheme.{u}} (V : S.chartOpens)
    {t : T ⟶ S.X} (ht : S.IsGoodOver t) (htV : Set.range t.base ⊆ (V.1 : Set S.X))
    {k l : T ⟶ S.goodBlowup} (hk : k ≫ S.goodBlowupToBase = t)
    (hl : l ≫ S.goodBlowupToBase = t) : k = l := by
  have hc : IsOpenImmersion.lift V.1.ι t (range_subset_range_ι htV) ≫ V.1.ι = t :=
    IsOpenImmersion.lift_fac _ _ _
  have hlift : ∀ m : T ⟶ S.goodBlowup, m ≫ S.goodBlowupToBase = t →
      ∃ m' : T ⟶ AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf,
        m' ≫ S.goodBlowupChart V = m ∧ m' ≫ S.chartPieceToBase V = t := by
    intro m hm
    refine ⟨(S.isPullback_goodBlowupChart V).lift
      (IsOpenImmersion.lift V.1.ι t (range_subset_range_ι htV)) m (by rw [hc, hm]), ?_, ?_⟩
    · exact (S.isPullback_goodBlowupChart V).lift_snd _ _ _
    · rw [← S.goodBlowupChart_comp_goodBlowupToBase V, ← Category.assoc,
        (S.isPullback_goodBlowupChart V).lift_snd _ _ _, hm]
  obtain ⟨k', hk'c, hk'b⟩ := hlift k hk
  obtain ⟨l', hl'c, hl'b⟩ := hlift l hl
  obtain ⟨_, _, huniq⟩ := (S.isGoodBlowupOver_chartPieceToBase V).existsUnique_lift t htV ht
  rw [← hk'c, ← hl'c, huniq k' hk'b, huniq l' hl'b]

/-- **A morphism to `X` that is good for the triple has at most one factorisation through the
glued morphism.**  Two factorisations agree over the part of the source above each member of the
basis of chart domains, by
`AlgebraicGeometry.ComplexAndDivisorSituation.eq_of_comp_goodBlowupToBase_eq_of_range_subset`, and
those parts cover the source. -/
theorem eq_of_comp_goodBlowupToBase_eq {T : Scheme.{u}} {t : T ⟶ S.X} (ht : S.IsGoodOver t)
    {k l : T ⟶ S.goodBlowup} (hk : k ≫ S.goodBlowupToBase = t)
    (hl : l ≫ S.goodBlowupToBase = t) : k = l := by
  refine S.hom_ext_of_preimage_chartOpens t fun V => ?_
  exact S.eq_of_comp_goodBlowupToBase_eq_of_range_subset V (ht.comp_of_flat (t ⁻¹ᵁ V.1).ι)
    (S.range_preimage_ι_comp_subset t V) (by rw [Category.assoc, hk])
    (by rw [Category.assoc, hl])

/-- **Condition (2) of Stacks tag 0GTY for the glued morphism.**  A morphism `h : Y ⟶ X` for
which `h⁻¹D` is defined and `(Y, h⁻¹D, Lh^*M)` is a good triple factors through `b : X' ⟶ X` in
exactly one way.

Over the part `h⁻¹(V)` of `Y` above a member `V` of the basis of chart domains, condition (2) for
the `V`-piece supplies a factorisation of `h` through `b_V`; composing it with the chart of `X'`
over `V` gives a factorisation through `b`.  Two of these agree on an overlap by
`AlgebraicGeometry.ComplexAndDivisorSituation.eq_of_comp_goodBlowupToBase_eq`, so they glue, and
the glued morphism factors `h` because it does so on a covering. -/
theorem existsUnique_lift_goodBlowupToBase {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hh : S.IsGoodOver h) : ∃! k : Y ⟶ S.goodBlowup, k ≫ S.goodBlowupToBase = h := by
  choose m hm using fun V : S.chartOpens =>
    ((S.isGoodBlowupOver_chartPieceToBase V).existsUnique_lift
      ((h ⁻¹ᵁ V.1).ι ≫ h) (S.range_preimage_ι_comp_subset h V)
      (hh.comp_of_flat (h ⁻¹ᵁ V.1).ι)).exists
  have hmb : ∀ V : S.chartOpens,
      (m V ≫ S.goodBlowupChart V) ≫ S.goodBlowupToBase = (h ⁻¹ᵁ V.1).ι ≫ h := by
    intro V
    rw [Category.assoc, S.goodBlowupChart_comp_goodBlowupToBase V, hm V]
  obtain ⟨k, hk, -⟩ := Scheme.existsUnique_hom_of_opens_cover
    (fun V : S.chartOpens => h ⁻¹ᵁ V.1) (S.exists_mem_preimage_chartOpens h)
    (fun V => m V ≫ S.goodBlowupChart V) (fun a b => by
      refine S.eq_of_comp_goodBlowupToBase_eq
        (hh.comp_of_flat ((h ⁻¹ᵁ a.1) ⊓ (h ⁻¹ᵁ b.1)).ι) ?_ ?_
      · rw [Category.assoc, hmb a, ← Category.assoc, Scheme.homOfLE_ι]
      · rw [Category.assoc, hmb b, ← Category.assoc, Scheme.homOfLE_ι])
  have hkb : k ≫ S.goodBlowupToBase = h := by
    refine S.hom_ext_of_preimage_chartOpens h fun V => ?_
    rw [← Category.assoc, hk V, hmb V]
  exact ⟨k, hkb, fun k' hk' => S.eq_of_comp_goodBlowupToBase_eq hh hk' hkb⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
