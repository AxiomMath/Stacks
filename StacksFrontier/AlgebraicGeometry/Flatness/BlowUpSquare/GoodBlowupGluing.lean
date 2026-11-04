module

public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBasis
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupOverOpen

/-!
# Gluing the per-chart blowups of Stacks tag 0GTY

Let `(X, D, M)` be a triple as in Situation 0F8S.  The proof of Stacks tag 0GTY blows up each
affine chart `(U, A, f, M^•)` in the product `∏ᵢ I_i(M^•, f)` of its determinantal ideals and
glues the results over the basis of chart domains; here that gluing is carried out.

The gluing datum of Stacks 01LH asks, for each member `V` of the basis, for a scheme over `V`,
and for each inclusion `V ⊆ U` of members for a morphism identifying the piece over `V` with the
part of the piece over `U` lying above `V`.  The pieces are the blowups of the chosen charts; the
restriction morphisms and the cocycle condition come from the universal property, condition (2)
of the tag; and the Cartesian squares come from the universal property as well, the restriction
of the `U`-piece over `V` having the two conditions over `V` by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.restrict` and a morphism with
those conditions being unique up to a unique isomorphism over `X`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.chartOpens`: the basis `ℬ` of the gluing
  paragraph of the tag, the opens that are domains of affine charts.
* `AlgebraicGeometry.ComplexAndDivisorSituation.chartPieceToBase`: the morphism `b_V : V' ⟶ X`
  attached to a member of the basis.
* `AlgebraicGeometry.ComplexAndDivisorSituation.chartGluingData`: the gluing datum.
* `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowup` and
  `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`: the scheme `X'` and the
  morphism `b : X' ⟶ X` of the tag.
* `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupChart`: the chart of `X'` attached to a
  member of the basis.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.opensIsBasis_chartOpens`: the chart domains form
  a basis of the topology of `X`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPullback_chartRes`: the restriction morphisms
  of the datum are Cartesian, which is what makes it a gluing datum.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPullback_goodBlowupChart`: the chart of `X'`
  over `V` identifies the `V`-piece with `b⁻¹(V)`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupChart_comp_goodBlowupToBase`: that
  chart composed with `b` is `b_V`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_ι_comp_goodBlowupToBase`: the
  restriction of `b` to `b⁻¹(V)` is good for the triple, for every member `V` of the basis.

## Implementation notes

A member of the basis is an open, not a chart, so a chart with that domain has to be chosen;
`AlgebraicGeometry.ComplexAndDivisorSituation.chartOf` does so, and
`AlgebraicGeometry.ComplexAndDivisorSituation.chartOf_U` says its domain is the given open.  Two
charts with the same domain give blowups that are uniquely isomorphic over `X`, by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowupOver.existsUnique_iso`, so nothing
depends on the choice.

The Cartesian square over the open `U` is obtained from the Cartesian square over `X` by
`CategoryTheory.IsPullback.of_right`, the right-hand square being the statement that a morphism
with image in `U` is its own base change along `U ⟶ X`
(`AlgebraicGeometry.IsOpenImmersion.isPullback_lift_id`).

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-! ### The basis of chart domains -/

/-- **The basis `ℬ` of the gluing paragraph of Stacks tag 0GTY**: the set of opens of `X` that
are domains of affine charts for the triple. -/
def chartOpens : Set S.X.Opens := Set.range fun C : AffineChart S => (C.U : S.X.Opens)

/-- The chart domains form a basis of the topology of `X`. -/
theorem opensIsBasis_chartOpens : Opens.IsBasis S.chartOpens := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨C, hxC, hCU⟩ := S.exists_chart_mem_le x U hx
  exact ⟨(C.U : S.X.Opens), ⟨C, rfl⟩, hxC, hCU⟩

/-- The opens `t⁻¹(V)`, for `V` a member of the basis of chart domains, cover the source of any
morphism `t` to `X`. -/
theorem exists_mem_preimage_chartOpens {T : Scheme.{u}} (t : T ⟶ S.X) (x : T) :
    ∃ V : S.chartOpens, x ∈ t ⁻¹ᵁ V.1 := by
  obtain ⟨C, hxC⟩ := S.exists_chart_mem (t.base x)
  exact ⟨⟨(C.U : S.X.Opens), ⟨C, rfl⟩⟩, hxC⟩

/-- A chosen affine chart whose domain is a given member of the basis of chart domains. -/
def chartOf (V : S.chartOpens) : AffineChart S := (Set.mem_range.mp V.2).choose

/-- The domain of the chosen chart `chartOf V` is `V`. -/
@[simp]
theorem chartOf_U (V : S.chartOpens) : ((S.chartOf V).U : S.X.Opens) = V.1 :=
  (Set.mem_range.mp V.2).choose_spec

/-! ### The pieces -/

/-- **The morphism `b_V : V' ⟶ X` of Stacks tag 0GTY attached to a member of the basis**: the
blowing up of the chosen chart with domain `V` in the product of its determinantal ideals,
followed by the inclusion of `V` into `X`. -/
def chartPieceToBase (V : S.chartOpens) :
    AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ⟶ S.X :=
  (S.chartOf V).chartBlowupToBase

/-- The piece over `V` has the two conditions of Stacks tag 0GTY over `V`. -/
theorem isGoodBlowupOver_chartPieceToBase (V : S.chartOpens) :
    S.IsGoodBlowupOver V.1 (S.chartPieceToBase V) :=
  S.chartOf_U V ▸ (S.chartOf V).isGoodBlowupOver_chartBlowupToBase

/-- The structure morphism of the piece over `V`, as a morphism to the open subscheme `V`. -/
def chartPieceProj (V : S.chartOpens) :
    AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ⟶ (V.1 : Scheme.{u}) :=
  IsOpenImmersion.lift V.1.ι (S.chartPieceToBase V)
    (range_subset_range_ι (S.isGoodBlowupOver_chartPieceToBase V).range_subset)

/-- The structure morphism of the piece over `V`, followed by the inclusion of `V` into `X`, is
`b_V`. -/
@[simp]
theorem chartPieceProj_comp_ι (V : S.chartOpens) :
    S.chartPieceProj V ≫ V.1.ι = S.chartPieceToBase V :=
  IsOpenImmersion.lift_fac _ _ _

/-! ### The restriction morphisms -/

/-- The factorisation of `b_V` through `b_U` exists and is unique. -/
private theorem existsUnique_chartRes {V U : S.chartOpens} (h : V.1 ≤ U.1) :
    ∃! k : AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ⟶
      AlgebraicGeometry.blowUp (S.chartOf U).blowupCentreIdealSheaf,
      k ≫ S.chartPieceToBase U = S.chartPieceToBase V :=
  ((S.isGoodBlowupOver_chartPieceToBase U).existsUnique_lift (S.chartPieceToBase V)
    ((S.isGoodBlowupOver_chartPieceToBase V).range_subset.trans h)
    (S.isGoodBlowupOver_chartPieceToBase V).isGoodOver)

/-- **The restriction morphism of the gluing datum.**  For an inclusion `V ⊆ U` of members of the
basis, the unique factorisation of `b_V` through `b_U`. -/
def chartRes {V U : S.chartOpens} (h : V.1 ≤ U.1) :
    AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ⟶
      AlgebraicGeometry.blowUp (S.chartOf U).blowupCentreIdealSheaf :=
  ((S.isGoodBlowupOver_chartPieceToBase U).existsUnique_lift (S.chartPieceToBase V)
    ((S.isGoodBlowupOver_chartPieceToBase V).range_subset.trans h)
    (S.isGoodBlowupOver_chartPieceToBase V).isGoodOver).choose

/-- The restriction morphism for `V ⊆ U`, followed by `b_U`, is `b_V`. -/
@[simp]
theorem chartRes_comp {V U : S.chartOpens} (h : V.1 ≤ U.1) :
    S.chartRes h ≫ S.chartPieceToBase U = S.chartPieceToBase V :=
  (S.existsUnique_chartRes h).choose_spec.1

/-- Any factorisation of `b_V` through `b_U` is the restriction morphism. -/
theorem chartRes_eq {V U : S.chartOpens} (h : V.1 ≤ U.1)
    (k : AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ⟶
      AlgebraicGeometry.blowUp (S.chartOf U).blowupCentreIdealSheaf)
    (hk : k ≫ S.chartPieceToBase U = S.chartPieceToBase V) : k = S.chartRes h :=
  (S.existsUnique_chartRes h).choose_spec.2 k hk

/-- The cocycle condition: restricting from `U` to `V` and then to `W` is restricting from `U` to
`W`. -/
theorem chartRes_trans {W V U : S.chartOpens} (hWV : W.1 ≤ V.1) (hVU : V.1 ≤ U.1) :
    S.chartRes (hWV.trans hVU) = S.chartRes hWV ≫ S.chartRes hVU :=
  (S.chartRes_eq (hWV.trans hVU) (S.chartRes hWV ≫ S.chartRes hVU)
    (by rw [Category.assoc, S.chartRes_comp hVU, S.chartRes_comp hWV])).symm

/-! ### The Cartesian squares -/

/-- A Cartesian square stays Cartesian after precomposing the two morphisms out of its corner
with an isomorphism. -/
private theorem isPullback_comp_iso {C : Type*} [Category C] {P Q A B Z : C}
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z} (h : IsPullback fst snd f g)
    (e : Q ≅ P) [HasPullback f g] :
    IsPullback (e.hom ≫ fst) (e.hom ≫ snd) f g :=
  IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, h.w]⟩ (e ≪≫ h.isoPullback)
    (by rw [Iso.trans_hom, Category.assoc, h.isoPullback_hom_fst])
    (by rw [Iso.trans_hom, Category.assoc, h.isoPullback_hom_snd])

/-- **The restriction morphism identifies the `V`-piece with the part of the `U`-piece over `V`,
as a morphism over `X`.** -/
theorem isPullback_chartRes_toBase {V U : S.chartOpens} (h : V.1 ≤ U.1) :
    IsPullback (S.chartRes h) (S.chartPieceProj V) (S.chartPieceToBase U) V.1.ι := by
  obtain ⟨e, he, -⟩ := (S.isGoodBlowupOver_chartPieceToBase V).existsUnique_iso
    ((S.isGoodBlowupOver_chartPieceToBase U).restrict h)
  have hres : e.hom ≫ (S.chartPieceToBase U ⁻¹ᵁ V.1).ι = S.chartRes h :=
    S.chartRes_eq h _ (by rw [Category.assoc]; exact he)
  have hproj : e.hom ≫ (S.chartPieceToBase U ∣_ V.1) = S.chartPieceProj V := by
    refine (cancel_mono V.1.ι).mp ?_
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hres, S.chartRes_comp h,
      S.chartPieceProj_comp_ι]
  rw [← hres, ← hproj]
  exact isPullback_comp_iso (isPullback_morphismRestrict (S.chartPieceToBase U) V.1).flip e

/-- **The restriction morphisms of the gluing datum are Cartesian**, as squares over the open
`U`. -/
theorem isPullback_chartRes {V U : S.chartOpens} (h : V.1 ≤ U.1) :
    IsPullback (S.chartRes h) (S.chartPieceProj V) (S.chartPieceProj U) (S.X.homOfLE h) := by
  refine IsPullback.of_right ?_ ?_
    (IsOpenImmersion.isPullback_lift_id (S.chartPieceToBase U) U.1.ι
      (range_subset_range_ι (S.isGoodBlowupOver_chartPieceToBase U).range_subset)).flip
  · rw [Category.comp_id, Scheme.homOfLE_ι]
    exact S.isPullback_chartRes_toBase h
  · refine (cancel_mono U.1.ι).mp ?_
    rw [Category.assoc, Category.assoc, S.chartPieceProj_comp_ι, Scheme.homOfLE_ι,
      S.chartPieceProj_comp_ι, S.chartRes_comp h]

/-! ### The glued morphism -/

/-- **The gluing datum of Stacks 01LH that the proof of Stacks tag 0GTY glues**: over each member
`V` of the basis of chart domains, the blowing up of the chosen chart with domain `V` in the
product of its determinantal ideals. -/
def chartGluingData : Scheme.BasisGluingData S.X S.chartOpens where
  obj V := AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf
  proj V := S.chartPieceProj V
  res h := S.chartRes h
  isPullback_res h := S.isPullback_chartRes h
  res_trans hWV hVU := S.chartRes_trans hWV hVU

/-- **The scheme `X'` of Stacks tag 0GTY.** -/
def goodBlowup : Scheme.{u} := S.chartGluingData.glued S.opensIsBasis_chartOpens

/-- **The morphism `b : X' ⟶ X` of Stacks tag 0GTY.** -/
def goodBlowupToBase : S.goodBlowup ⟶ S.X :=
  S.chartGluingData.toBase S.opensIsBasis_chartOpens

/-- The chart of `X'` attached to a member of the basis of chart domains: the open immersion of
the blowup of the chosen chart into `X'`. -/
def goodBlowupChart (V : S.chartOpens) :
    AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ⟶ S.goodBlowup :=
  S.chartGluingData.chart S.opensIsBasis_chartOpens V

/-- **The chart of `X'` over `V` identifies the `V`-piece with `b⁻¹(V)`.** -/
theorem isPullback_goodBlowupChart (V : S.chartOpens) :
    IsPullback (S.chartPieceProj V) (S.goodBlowupChart V) V.1.ι S.goodBlowupToBase :=
  S.chartGluingData.isPullback_proj_chart S.opensIsBasis_chartOpens V

/-- The chart of `X'` over a member of the basis is an open immersion. -/
instance isOpenImmersion_goodBlowupChart (V : S.chartOpens) :
    IsOpenImmersion (S.goodBlowupChart V) :=
  MorphismProperty.of_isPullback (S.isPullback_goodBlowupChart V) inferInstance

/-- **The chart of `X'` over `V`, composed with `b`, is `b_V`.** -/
@[simp]
theorem goodBlowupChart_comp_goodBlowupToBase (V : S.chartOpens) :
    S.goodBlowupChart V ≫ S.goodBlowupToBase = S.chartPieceToBase V := by
  rw [← (S.isPullback_goodBlowupChart V).w, S.chartPieceProj_comp_ι]

/-- Every point of `X'` lies in the image of the chart over some member of the basis. -/
theorem exists_mem_range_goodBlowupChart (y : S.goodBlowup) :
    ∃ (V : S.chartOpens) (z : AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf),
      (S.goodBlowupChart V).base z = y := by
  obtain ⟨C, hxC⟩ := S.exists_chart_mem (S.goodBlowupToBase.base y)
  refine ⟨⟨(C.U : S.X.Opens), ⟨C, rfl⟩⟩, ?_⟩
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
    (S.isPullback_goodBlowupChart ⟨(C.U : S.X.Opens), ⟨C, rfl⟩⟩)
    ⟨S.goodBlowupToBase.base y, hxC⟩ y rfl
  exact ⟨z, hz⟩

/-- **The restriction of `b` to `b⁻¹(V)` is good for the triple**, for every member `V` of the
basis. -/
theorem isGoodOver_ι_comp_goodBlowupToBase (V : S.chartOpens) :
    S.IsGoodOver ((S.goodBlowupToBase ⁻¹ᵁ V.1).ι ≫ S.goodBlowupToBase) := by
  obtain ⟨e, he⟩ : ∃ e : AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf ≅
      (S.goodBlowupToBase ⁻¹ᵁ V.1).toScheme,
      e.hom ≫ (S.goodBlowupToBase ⁻¹ᵁ V.1).ι = S.goodBlowupChart V :=
    ⟨_, (S.isPullback_goodBlowupChart V).isoIsPullback_hom_snd _ _
      (isPullback_morphismRestrict S.goodBlowupToBase V.1)⟩
  have hfac : e.inv ≫ S.chartPieceToBase V =
      (S.goodBlowupToBase ⁻¹ᵁ V.1).ι ≫ S.goodBlowupToBase := by
    rw [← S.goodBlowupChart_comp_goodBlowupToBase V, ← he, Category.assoc,
      Iso.inv_hom_id_assoc]
  rw [← hfac]
  exact (S.isGoodBlowupOver_chartPieceToBase V).isGoodOver.comp_of_flat e.inv

end AlgebraicGeometry.ComplexAndDivisorSituation

end
