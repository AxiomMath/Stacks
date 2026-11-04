module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupTag
import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChangeGeneral

/-!
# Stacks tag 0F8V: the modification of the pulled-back triple is a strict transform

Let `(X, D, M)` be a triple as in Situation 0F8S, let `h : Y ⟶ X` be a morphism along which the
pullback `E = h⁻¹D` is defined, and let `b : X' ⟶ X` and `c : Y' ⟶ Y` be the morphisms of Stacks
tag 0GTY for `(X, D, M)` and `(Y, E, Lh^*M)`.  Alongside its displayed identification of derived
décalages, Stacks tag 0F8V asserts that `Y'` is the strict transform of `Y` with respect to `b`.

The precise formulation in the proof of the tag is that over a quasi-compact open `W ⊂ X` for
which `b⁻¹(W) ⟶ W` is a blowing up, the morphism `(h', c)` identifies `Y'|_W` with the strict
transform of `Y_W`; and the proof observes that this is a local question on `W` and proves it
over an affine chart.  That is what this file does: over an affine chart `(U, A, f, M^•)` the
restriction `b⁻¹(U) ⟶ U` is the blowing up of `U` in `I = ∏ᵢ I_i(M^•, f)`
(`AffineChart.existsUnique_iso_preimage_blowUp`), and the restriction `c⁻¹(h⁻¹U) ⟶ h⁻¹(U)` is the
blowing up of `h⁻¹(U)` in `I𝒪_{h⁻¹(U)}`, which by Stacks tag 080E is exactly the strict transform
of `h⁻¹(U)`.

## Main results

* `AffineChart.isGoodBlowupOver_pullbackChartBlowupToBase`: the blowing up of `h⁻¹(U)` in
  `I𝒪_{h⁻¹(U)}` has the two conditions of Stacks tag 0GTY for `(Y, E, Lh^*M)` over `h⁻¹(U)`.
* `AffineChart.existsUnique_iso_strictTransform`: **Stacks tag 0F8V, the strict-transform
  assertion.**

## Implementation notes

Condition (2) for the blowing up of the inverse-image centre is the universal property of blowing
up (Stacks tag 0806) together with
`AffineChart.isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf`: a morphism to `h⁻¹(U)` that
is good for the pulled-back triple is, composed with `h`, good for `(X, D, M)`
(`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp`), and along such a morphism the
inverse image of `I` is an effective Cartier divisor.

Condition (1) is `AffineChart.isGoodOver_comp_ι` applied to the composite
`blowUp (I𝒪_{h⁻¹U}) ⟶ h⁻¹(U) ⟶ U`: the inverse image of each factor `I_i(M^•, f)` along it is a
factor of the exceptional divisor of that blowing up, hence an effective Cartier divisor by
Stacks tag 07ZV, which is the same mechanism as over the chart itself.  The passage from goodness
over `X` to goodness over `Y` is the equivalence
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp`.

## References

* [Stacks Project, Tag 0F8V](https://stacks.math.columbia.edu/tag/0F8V)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **The inverse image of the centre of the blowup of a chart is the product of the inverse
images of the determinantal ideals.**  Taking inverse images of ideal sheaves is multiplicative,
by `Stacks.IdealSheaf.comap_finset_prod`. -/
theorem comap_blowupCentreIdealSheaf_eq_prod (C : AffineChart S) {Z : Scheme.{u}}
    (g : Z ⟶ (C.U : S.X.Opens).toScheme) :
    C.blowupCentreIdealSheaf.comap g
      = ∏ i ∈ C.complex.bounded.toFinset, (C.determinantalIdealSheaf i).comap g := by
  rw [C.blowupCentreIdealSheaf_eq_prod, Stacks.IdealSheaf.comap_finset_prod]

/-- **Each inverse image of a determinantal ideal of a chart becomes an effective Cartier divisor
on the blowup of the inverse image of the centre.**  The inverse image of the whole centre is the
exceptional divisor of that blowup, hence an effective Cartier divisor by Stacks tag 02OS, and a
factor of an effective Cartier divisor is one by Stacks tag 07ZV. -/
theorem isEffectiveCartierDivisor_comap_comap_determinantalIdealSheaf (C : AffineChart S)
    {Z : Scheme.{u}} (g : Z ⟶ (C.U : S.X.Opens).toScheme) {i : ℤ}
    (hi : i ∈ C.complex.bounded.toFinset) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (((C.determinantalIdealSheaf i).comap g).comap
        (AlgebraicGeometry.blowUpToBase (C.blowupCentreIdealSheaf.comap g))) := by
  refine isEffectiveCartierDivisor_comap_of_mem_prod _ C.complex.bounded.toFinset
    (fun j => (C.determinantalIdealSheaf j).comap g) ?_ hi
  rw [← C.comap_blowupCentreIdealSheaf_eq_prod g]
  exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal
    (C.blowupCentreIdealSheaf.comap g)

/-- **The blowing up of `h⁻¹(U)` in the inverse image of the centre of the chart**, read as a
morphism to `Y`.  This is what the morphism `c` of Stacks tag 0GTY for the pulled-back triple
restricts to over `h⁻¹(U)`. -/
def pullbackChartBlowupToBase (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X) :
    AlgebraicGeometry.blowUp
        (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens))) ⟶ Y :=
  AlgebraicGeometry.blowUpToBase
      (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens))) ≫
    (h ⁻¹ᵁ (C.U : S.X.Opens)).ι

/-- **The blowing up of `h⁻¹(U)` in the inverse image of the centre has the two conditions of
Stacks tag 0GTY for the pulled-back triple over `h⁻¹(U)`.**

Condition (1) is `AffineChart.isGoodOver_comp_ι` for the composite to `U`, whose inverse images
of the determinantal ideals are factors of the exceptional divisor; the passage between goodness
over `X` and goodness over `Y` is
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp`.  Condition (2) is the universal
property of blowing up: a morphism to `h⁻¹(U)` that is good for the pulled-back triple is, after
composing with `h`, good for `(X, D, M)`, and along such a morphism the inverse image of the
centre is an effective Cartier divisor by
`AffineChart.isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf`. -/
theorem isGoodBlowupOver_pullbackChartBlowupToBase (C : AffineChart S) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    (S.pullback h hD).IsGoodBlowupOver (h ⁻¹ᵁ (C.U : S.X.Opens))
      (C.pullbackChartBlowupToBase h) := by
  have hιD : Stacks.Divisors.IsEffectiveCartierDivisor
      ((S.D.comap h).comap (h ⁻¹ᵁ (C.U : S.X.Opens)).ι) :=
    Stacks.Divisors.isPullbackDefined_of_flat (h ⁻¹ᵁ (C.U : S.X.Opens)).ι (S.D.comap h) hD
  -- composing with the restriction of `h` and the inclusion of the chart
  have hq : ∀ {T : Scheme.{u}} (x : T ⟶ (h ⁻¹ᵁ (C.U : S.X.Opens)).toScheme),
      (x ≫ (h ∣_ (C.U : S.X.Opens))) ≫ (C.U : S.X.Opens).ι =
        (x ≫ (h ⁻¹ᵁ (C.U : S.X.Opens)).ι) ≫ h :=
    fun x => by rw [Category.assoc, Category.assoc, morphismRestrict_ι]
  have hp : Stacks.Divisors.IsPullbackDefined (C.pullbackChartBlowupToBase h) (S.D.comap h) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      ((S.D.comap h).comap (C.pullbackChartBlowupToBase h))
    rw [pullbackChartBlowupToBase, Scheme.IdealSheafData.comap_comp]
    exact isPullbackDefined_blowUpToBase _ _ hιD
  have hgoodX : S.IsGoodOver (C.pullbackChartBlowupToBase h ≫ h) := by
    rw [pullbackChartBlowupToBase, ← hq]
    refine C.isGoodOver_comp_ι _ (by
      change Stacks.Divisors.IsEffectiveCartierDivisor (S.D.comap _)
      rw [hq, Scheme.IdealSheafData.comap_comp]
      exact hp) fun i hi => ?_
    rw [Scheme.IdealSheafData.comap_comp]
    exact C.isEffectiveCartierDivisor_comap_comap_determinantalIdealSheaf
      (h ∣_ (C.U : S.X.Opens)) hi
  refine ⟨?_, ⟨hp, (S.isGoodOver_comp h hD (C.pullbackChartBlowupToBase h) hp).mp hgoodX⟩,
    fun {T} t ht hgood => ?_⟩
  · rintro y ⟨z, rfl⟩
    exact ((AlgebraicGeometry.blowUpToBase
      (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens)))).base z).2
  · -- the universal property
    have hfac : IsOpenImmersion.lift (h ⁻¹ᵁ (C.U : S.X.Opens)).ι t
        (range_subset_range_ι ht) ≫ (h ⁻¹ᵁ (C.U : S.X.Opens)).ι = t :=
      IsOpenImmersion.lift_fac _ _ _
    have hgoodt : S.IsGoodOver ((IsOpenImmersion.lift (h ⁻¹ᵁ (C.U : S.X.Opens)).ι t
        (range_subset_range_ι ht) ≫ (h ∣_ (C.U : S.X.Opens))) ≫ (C.U : S.X.Opens).ι) := by
      rw [hq, hfac]
      exact (S.isGoodOver_comp h hD t hgood.pullbackDefined).mpr hgood.isGoodTriple
    obtain ⟨k, hk, huniq⟩ := existsUnique_lift_blowUpToBase
      (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens)))
      (IsOpenImmersion.lift (h ⁻¹ᵁ (C.U : S.X.Opens)).ι t (range_subset_range_ι ht))
      (by
        rw [← Scheme.IdealSheafData.comap_comp]
        exact C.isEffectiveCartierDivisor_comap_blowupCentreIdealSheaf _ hgoodt)
    refine ⟨k, ?_, fun l hl => huniq l ((cancel_mono (h ⁻¹ᵁ (C.U : S.X.Opens)).ι).mp
      (by rw [Category.assoc, hfac]; exact hl))⟩
    change k ≫ AlgebraicGeometry.blowUpToBase _ ≫ (h ⁻¹ᵁ (C.U : S.X.Opens)).ι = t
    rw [← Category.assoc, hk, hfac]

/-- **Stacks tag 0F8V: the modification of the pulled-back triple is the strict transform.**  Let
`h : Y ⟶ X` be a morphism along which `E = h⁻¹D` is defined, let `b : X' ⟶ X` and `c : Y' ⟶ Y` be
the morphisms of Stacks tag 0GTY for `(X, D, M)` and `(Y, E, Lh^*M)`, and let `(U, A, f, M^•)` be
an affine chart for `(X, D, M)`.  Over `U` the morphism `b` is the blowing up of `U` in
`I = ∏ᵢ I_i(M^•, f)`, and `c⁻¹(h⁻¹U) ⟶ h⁻¹(U)` is identified, by exactly one isomorphism over
`h⁻¹(U)`, with the strict transform of `h⁻¹(U)` with respect to that blowing up.

Both are the blowing up of `h⁻¹(U)` in `I𝒪_{h⁻¹(U)}`: the first by
`AffineChart.isGoodBlowupOver_pullbackChartBlowupToBase` and the uniqueness of a morphism with
the two conditions of Stacks tag 0GTY over `h⁻¹(U)`, the second by Stacks tag 080E. -/
@[stacks 0F8V "the strict-transform assertion: over an affine chart `(U, A, f, M^•)`, the \
restriction of the morphism `c` of tag 0GTY for the pulled-back triple is identified, by exactly \
one isomorphism over `h⁻¹(U)`, with the strict transform of `h⁻¹(U)` with respect to the \
restriction of `b` over `U`, which is the blowing up of `U` in the product of the determinantal \
ideals of the chart"]
theorem existsUnique_iso_strictTransform (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    ∃! e : ((S.pullback h hD).goodBlowupToBase ⁻¹ᵁ
        (h ⁻¹ᵁ (C.U : S.X.Opens))).toScheme ≅
      Stacks.StrictTransform.scheme (h ∣_ (C.U : S.X.Opens))
        (AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf)
        (AlgebraicGeometry.exceptionalIdeal C.blowupCentreIdealSheaf),
      e.hom ≫ (Stacks.StrictTransform.ideal (h ∣_ (C.U : S.X.Opens))
            (AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf)
            (AlgebraicGeometry.exceptionalIdeal C.blowupCentreIdealSheaf)).subschemeι ≫
          pullback.fst (h ∣_ (C.U : S.X.Opens))
            (AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf) =
        (S.pullback h hD).goodBlowupToBase ∣_ (h ⁻¹ᵁ (C.U : S.X.Opens)) := by
  set α := AlgebraicGeometry.strictTransformBlowUpIso (h ∣_ (C.U : S.X.Opens))
    C.blowupCentreIdealSheaf
  obtain ⟨β, hβ, hβuniq⟩ := ((((S.pullback h hD).isGoodBlowupOver_top_iff
    (S.pullback h hD).goodBlowupToBase).mpr
      (S.pullback h hD).isGoodBlowup_goodBlowupToBase).restrict
        (le_top : (h ⁻¹ᵁ (C.U : S.X.Opens)) ≤ ⊤)).existsUnique_iso
    (C.isGoodBlowupOver_pullbackChartBlowupToBase h hD)
  have hiff : ∀ e : ((S.pullback h hD).goodBlowupToBase ⁻¹ᵁ
      (h ⁻¹ᵁ (C.U : S.X.Opens))).toScheme ≅
      AlgebraicGeometry.blowUp (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens))),
      (e.hom ≫ AlgebraicGeometry.blowUpToBase
          (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens))) =
        (S.pullback h hD).goodBlowupToBase ∣_ (h ⁻¹ᵁ (C.U : S.X.Opens))) ↔
      (e.hom ≫ C.pullbackChartBlowupToBase h =
        ((S.pullback h hD).goodBlowupToBase ⁻¹ᵁ (h ⁻¹ᵁ (C.U : S.X.Opens))).ι ≫
          (S.pullback h hD).goodBlowupToBase) := by
    intro e
    rw [pullbackChartBlowupToBase]
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rw [← Category.assoc, he]
      exact morphismRestrict_ι _ _
    · refine (cancel_mono (h ⁻¹ᵁ (C.U : S.X.Opens)).ι).mp ?_
      rw [Category.assoc, he]
      exact (morphismRestrict_ι _ _).symm
  refine ⟨β ≪≫ ((Over.forget _).mapIso α).symm, ?_, fun e he => ?_⟩
  · change (β.hom ≫ α.inv.left) ≫ _ = _
    rw [Category.assoc]
    exact (congrArg (β.hom ≫ ·) (Over.w α.inv)).trans ((hiff β).mpr hβ)
  · have h1 : (e ≪≫ (Over.forget _).mapIso α).hom ≫ AlgebraicGeometry.blowUpToBase
        (C.blowupCentreIdealSheaf.comap (h ∣_ (C.U : S.X.Opens))) =
        (S.pullback h hD).goodBlowupToBase ∣_ (h ⁻¹ᵁ (C.U : S.X.Opens)) := by
      change (e.hom ≫ α.hom.left) ≫ _ = _
      rw [Category.assoc]
      exact (congrArg (e.hom ≫ ·) (Over.w α.hom)).trans he
    have h2 : e ≪≫ (Over.forget _).mapIso α = β := hβuniq _ ((hiff _).mp h1)
    rw [← h2, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation

end
