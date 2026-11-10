module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupGluing
import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ContainingDivisorFibre

/-!
# The glued blowup is good for the triple

Let `(X, D, M)` be a triple as in Situation 0F8S and let `b : X' ⟶ X` be the morphism glued from
the per-chart blowups in `GoodBlowupGluing.lean`.  This file proves condition (1) of Stacks tag
0GTY for it: the pullback `D' = b⁻¹D` is defined and `(X', D', Lb^*M)` is a good triple.

Both halves are local on `X'`, which is covered by the charts of the gluing.  That the pullback
of the divisor is defined is read off the corresponding statement for the piece over a member of
the basis of chart domains, by the affine-local criterion for an effective Cartier divisor.  For
goodness, the chart of `(X', D', Lb^*M)` at a point is the pullback along `b` of the chart `C` of
`(X, D, M)` used to build the piece containing that point, by part (1) of Stacks tag 0F8T; its
determinantal ideals are the extensions of those of `C`, and those become principal because on
the piece the inverse image of each `I_i(M^•, f)` is an effective Cartier divisor.

## Main results

* `ComplexAndDivisorSituation.isPullbackDefined_goodBlowupToBase`: the pullback of `D` along the
  glued morphism is defined.
* `ComplexAndDivisorSituation.exists_affineOpen_isPrincipal_map_determinantalIdeal`: the
  determinantal ideals of a chart become principal on a small affine open of `X'` above its domain.
* `ComplexAndDivisorSituation.isGoodOver_goodBlowupToBase`: **condition (1) of Stacks tag 0GTY for
  the glued morphism.**

## Implementation notes

The determinantal ideals of the pulled-back chart are the ideals `I_i(M^•, f)·Γ(X', A)` for an
affine open `A ⊆ b⁻¹(U)` of `X'`, which is a statement about the ring map `Γ(X, U) ⟶ Γ(X', A)`
induced by `b`.  It is compared with the corresponding statement on the piece by factoring
`A ⟶ X'` through the chart of the gluing — possible because `A` is chosen inside the image of an
affine open of the piece on which all the finitely many inverse images `I_i(M^•, f)𝒪_{U'}` are
simultaneously principal — and then reading both sides on the affine open `⊤` of `A`.
`AlgebraicGeometry.Scheme.Opens.ι_appLE_top` is what identifies the two, up to the isomorphism
`Γ(X', A) ≅ Γ(A, ⊤)`, along which principality transports.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-- Equal morphisms induce the same map on sections over a pair of opens; the two proofs that the
smaller open lies over the larger need no reconciliation, being proofs of a `Prop`. -/
private theorem appLE_eq_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (W : Y.Opens) (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) :
    f.appLE U W hf = g.appLE U W hg := by
  subst hfg
  rfl

/-- Principality of an ideal is reflected by extension along a ring map with a left inverse: the
extension of the extension along the left inverse is the ideal itself. -/
private theorem isPrincipal_of_isPrincipal_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (ψ : B →+* A) (hψφ : ∀ a : A, ψ (φ a) = a)
    {J : Ideal A} (h : (Ideal.map φ J).IsPrincipal) : J.IsPrincipal := by
  obtain ⟨t, ht⟩ := h
  have hid : Ideal.map ψ (Ideal.map φ J) = J := by
    rw [Ideal.map_map, show ψ.comp φ = RingHom.id A from RingHom.ext hψφ, Ideal.map_id]
  refine ⟨ψ t, ?_⟩
  rw [← hid, ht, Ideal.map_span, Set.image_singleton]

/-! ### The pullback of the divisor -/

/-- **The pullback of `D` along the glued morphism is defined.**  Every point of `X'` lies over a
member `V` of the basis of chart domains, and the pullback of `D` along the restriction of `b` to
`b⁻¹(V)` is defined because that restriction is good for the triple
(`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_ι_comp_goodBlowupToBase`); so the ideal
of `b⁻¹D` is cut out by a nonzerodivisor on an affine open around the point, which is the
affine-local criterion of Stacks tag 01WS. -/
theorem isPullbackDefined_goodBlowupToBase :
    Stacks.Divisors.IsPullbackDefined S.goodBlowupToBase S.D := by
  refine Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_of_affineLocal _
    fun y hy => ?_
  obtain ⟨V, hyV⟩ := S.exists_mem_preimage_chartOpens S.goodBlowupToBase y
  have hN : Stacks.Divisors.IsEffectiveCartierDivisor
      ((S.D.comap S.goodBlowupToBase).comap (S.goodBlowupToBase ⁻¹ᵁ V.1).ι) := by
    rw [← Scheme.IdealSheafData.comap_comp]
    exact (S.isGoodOver_ι_comp_goodBlowupToBase V).pullbackDefined
  obtain ⟨A, hA, hyA, -, t, htreg, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor_comap
      (S.D.comap S.goodBlowupToBase) hN y hyV
  exact ⟨⟨A, hA⟩, hyA, t, htreg.mem_nonZeroDivisors, hspan⟩

/-! ### Goodness of the pulled-back triple -/

/-- The piece over a member of the basis maps into the domain of the chosen chart with that
domain. -/
theorem chartPieceToBase_apply_mem (V : S.chartOpens)
    (z : AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf) :
    (S.chartPieceToBase V).base z ∈ ((S.chartOf V).U : S.X.Opens) :=
  ((AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf).base z).2

/-- **The determinantal ideals of a chart become principal on a small affine open of `X'` above
its domain.**  Let `V` be a member of the basis of chart domains, `C` the chosen chart with that
domain, and `z` a point of the piece over `V`.  Then the image of `z` in `X'` has an affine open
neighbourhood `A` inside `b⁻¹(U)` on which the extension of every determinantal ideal of `C`
along the map on sections induced by `b` is principal.

On the piece the inverse image of each `I_i(M^•, f)` is an effective Cartier divisor, hence the
finitely many of them that are not the unit ideal are simultaneously principal on one affine open
`A'` around `z`; the neighbourhood `A` is chosen inside the image of `A'`, so that the inclusion
of `A` into `X'` factors through the piece and lands in `A'`. -/
theorem exists_affineOpen_isPrincipal_map_determinantalIdeal (V : S.chartOpens)
    (z : AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf) :
    ∃ (A : S.goodBlowup.affineOpens)
      (hA : (A : S.goodBlowup.Opens) ≤
        S.goodBlowupToBase ⁻¹ᵁ ((S.chartOf V).U : S.X.Opens)),
      (S.goodBlowupChart V).base z ∈ (A : S.goodBlowup.Opens) ∧
        ∀ i : ℤ, (Ideal.map (S.goodBlowupToBase.appLE ((S.chartOf V).U : S.X.Opens)
            (A : S.goodBlowup.Opens) hA).hom
              ((S.chartOf V).determinantalIdeal i)).IsPrincipal := by
  classical
  -- simultaneous principality of the inverse images of the determinantal ideals on the piece
  obtain ⟨A', hzA', hprin⟩ := AffineChart.exists_affineOpen_forall_isPrincipal
    (S.chartOf V).complex.bounded.toFinset
    (fun i => ((S.chartOf V).determinantalIdealSheaf i).comap
      (AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf))
    (fun i hi => Stacks.CartierAffineLocal.isLocallyPrincipal _
      ((S.chartOf V).isEffectiveCartierDivisor_comap_determinantalIdealSheaf hi)) z
  -- an affine open of `X'` around the image of `z`, inside the image of `A'`
  obtain ⟨A, hyA, hAle⟩ : ∃ A : S.goodBlowup.affineOpens,
      (S.goodBlowupChart V).base z ∈ (A : Set S.goodBlowup) ∧
        (A : Set S.goodBlowup) ⊆
          ((S.goodBlowupChart V ''ᵁ (A' : (AlgebraicGeometry.blowUp
            (S.chartOf V).blowupCentreIdealSheaf).Opens)) : Set S.goodBlowup) := by
    obtain ⟨-, ⟨A, hAaff, rfl⟩, hyA, hAle⟩ :=
      S.goodBlowup.isBasis_affineOpens.exists_subset_of_mem_open
        ((Scheme.Hom.apply_mem_image_iff (S.goodBlowupChart V)).mpr hzA')
        (S.goodBlowupChart V ''ᵁ (A' : (AlgebraicGeometry.blowUp
          (S.chartOf V).blowupCentreIdealSheaf).Opens)).isOpen
    exact ⟨⟨A, hAaff⟩, hyA, hAle⟩
  -- `A` lies over the domain of the chart
  have hAb : (A : S.goodBlowup.Opens) ≤
      S.goodBlowupToBase ⁻¹ᵁ ((S.chartOf V).U : S.X.Opens) := by
    intro x hx
    obtain ⟨z', -, rfl⟩ := hAle hx
    change S.goodBlowupToBase.base ((S.goodBlowupChart V).base z') ∈
      ((S.chartOf V).U : S.X.Opens)
    rw [← Scheme.Hom.comp_apply, S.goodBlowupChart_comp_goodBlowupToBase V]
    exact S.chartPieceToBase_apply_mem V z'
  -- the inclusion of `A` factors through the chart of the gluing
  have hrange : Set.range ((A : S.goodBlowup.Opens).ι).base ⊆
      Set.range (S.goodBlowupChart V).base := by
    rw [show Set.range ((A : S.goodBlowup.Opens).ι).base = (A : Set S.goodBlowup) from
      congrArg (fun W : S.goodBlowup.Opens => (W : Set S.goodBlowup))
        (Scheme.Opens.opensRange_ι (A : S.goodBlowup.Opens))]
    intro x hx
    obtain ⟨z', -, hz'⟩ := hAle hx
    exact ⟨z', hz'⟩
  have hafac : IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange ≫
      S.goodBlowupChart V = (A : S.goodBlowup.Opens).ι :=
    IsOpenImmersion.lift_fac _ _ _
  -- and lands in `A'`
  have haA' : (⊤ : (A : S.goodBlowup.Opens).toScheme.Opens) ≤
      IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange ⁻¹ᵁ
        (A' : (AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf).Opens) := by
    intro w _
    obtain ⟨z', hz'A', hz'⟩ := hAle w.2
    have hj : (S.goodBlowupChart V).base
        ((IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange).base w)
        = (S.goodBlowupChart V).base z' := by
      rw [← Scheme.Hom.comp_apply, hafac]
      exact hz'.symm
    change (IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange).base w ∈
      (A' : (AlgebraicGeometry.blowUp (S.chartOf V).blowupCentreIdealSheaf).Opens)
    rw [(S.goodBlowupChart V).isOpenEmbedding.injective hj]
    exact hz'A'
  -- the factorisation of `A ⟶ X` through the blowup of the chart
  have hmor : (IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange ≫
        AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf) ≫
      ((S.chartOf V).U : S.X.Opens).ι =
      (A : S.goodBlowup.Opens).ι ≫ S.goodBlowupToBase := by
    rw [Category.assoc,
      show AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf ≫
        ((S.chartOf V).U : S.X.Opens).ι = S.chartPieceToBase V from rfl,
      ← S.goodBlowupChart_comp_goodBlowupToBase V, ← Category.assoc, hafac]
  have hle1 : (⊤ : (A : S.goodBlowup.Opens).toScheme.Opens) ≤
      ((IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange ≫
        AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf) ≫
          ((S.chartOf V).U : S.X.Opens).ι) ⁻¹ᵁ ((S.chartOf V).U : S.X.Opens) :=
    fun x _ => ((IsOpenImmersion.lift (S.goodBlowupChart V) (A : S.goodBlowup.Opens).ι hrange ≫
      AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf).base x).2
  have hle2 : (⊤ : (A : S.goodBlowup.Opens).toScheme.Opens) ≤
      ((A : S.goodBlowup.Opens).ι ≫ S.goodBlowupToBase) ⁻¹ᵁ
        ((S.chartOf V).U : S.X.Opens) :=
    fun x _ => hAb x.2
  have hle3 : (⊤ : (A : S.goodBlowup.Opens).toScheme.Opens) ≤
      (A : S.goodBlowup.Opens).ι ⁻¹ᵁ (A : S.goodBlowup.Opens) :=
    fun x _ => x.2
  refine ⟨A, hAb, hyA, fun i => ?_⟩
  by_cases hi : i ∈ (S.chartOf V).complex.bounded.toFinset
  · refine isPrincipal_of_isPrincipal_map (A : S.goodBlowup.Opens).topIso.inv.hom
      (A : S.goodBlowup.Opens).topIso.hom.hom (fun s => ?_) ?_
    · rw [← CommRingCat.comp_apply, (A : S.goodBlowup.Opens).topIso.inv_hom_id]
      rfl
    · have hval : Ideal.map (A : S.goodBlowup.Opens).topIso.inv.hom
          (Ideal.map (S.goodBlowupToBase.appLE ((S.chartOf V).U : S.X.Opens)
            (A : S.goodBlowup.Opens) hAb).hom ((S.chartOf V).determinantalIdeal i))
          = ((((S.chartOf V).determinantalIdealSheaf i).comap
              (AlgebraicGeometry.blowUpToBase (S.chartOf V).blowupCentreIdealSheaf)).comap
            (IsOpenImmersion.lift (S.goodBlowupChart V)
              (A : S.goodBlowup.Opens).ι hrange)).ideal ⟨⊤, isAffineOpen_top _⟩ := by
        rw [← Scheme.IdealSheafData.comap_comp,
          (S.chartOf V).ideal_comap_determinantalIdealSheaf _ ⟨⊤, isAffineOpen_top _⟩ i hle1,
          appLE_eq_of_eq hmor ((S.chartOf V).U : S.X.Opens)
            (⊤ : (A : S.goodBlowup.Opens).toScheme.Opens) hle1 hle2,
          ← Scheme.Opens.ι_appLE_top (A : S.goodBlowup.Opens) hle3, Ideal.map_map,
          ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      rw [hval, Stacks.IdealSheaf.ideal_comap_appLE _ _ A' ⟨⊤, isAffineOpen_top _⟩ haA']
      obtain ⟨t, ht⟩ := hprin i hi
      exact ⟨_, by rw [ht, Ideal.map_span, Set.image_singleton]⟩
  · have hr : (S.chartOf V).complex.rank i = 0 := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
    rw [(S.chartOf V).determinantalIdeal_eq_top hr, Ideal.map_top]
    exact ⟨1, Ideal.span_singleton_one.symm⟩

/-- **Condition (1) of Stacks tag 0GTY for the glued morphism.**  The pullback `D' = b⁻¹D` is
defined and `(X', D', Lb^*M)` is a good triple.

A point of `D'` lies in the image of the chart of `X'` over some member `V` of the basis of chart
domains; the chart of the pulled-back triple at it is the pullback along `b`, in the sense of part
(1) of Stacks tag 0F8T, of the chosen chart `C` with domain `V`, taken over the affine open of
`X'` supplied by `exists_affineOpen_isPrincipal_map_determinantalIdeal`; its determinantal ideals
are the extensions of those of `C`, which are principal there. -/
theorem isGoodOver_goodBlowupToBase : S.IsGoodOver S.goodBlowupToBase where
  pullbackDefined := S.isPullbackDefined_goodBlowupToBase
  isGoodTriple := by
    rintro y -
    obtain ⟨V, z, hz⟩ := S.exists_mem_range_goodBlowupChart y
    obtain ⟨A, hAb, hyA, hprin⟩ :=
      S.exists_affineOpen_isPrincipal_map_determinantalIdeal V z
    refine ⟨(S.chartOf V).pullback S.goodBlowupToBase S.isPullbackDefined_goodBlowupToBase
      A hAb, hz ▸ hyA, fun i => ?_⟩
    rw [(S.chartOf V).pullback_determinantalIdeal]
    exact hprin i

end AlgebraicGeometry.ComplexAndDivisorSituation

end
