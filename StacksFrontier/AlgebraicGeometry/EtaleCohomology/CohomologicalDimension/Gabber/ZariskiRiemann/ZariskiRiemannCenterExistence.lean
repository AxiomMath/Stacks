module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannFibreCompact
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Every point of a model in the closure of `j(η)` is a center

Let `B` be a local domain with fraction field `K` and `M` a proper model `f : Y ⟶ Spec B` with
point `j : Spec K ⟶ Y`. A point `y ∈ Y` in the closure of the image of `j` and over the closed
point of `Spec B` is the center of a valuation ring of `K` dominating `B`: the point `j(η)`
specializes to `y`, the image `A` of `σ : 𝒪_{Y,y} ⟶ 𝒪_{Y,j(η)} ⟶ K` is a local subring of `K`
containing `B` (`σ` is a map over `B`), and a valuation ring `V` dominating `A` (Stacks 00IA) has
center `y` by `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.centerPoint_eq_of_stalk_mem`;
it dominates `B` because its center lies over the closed point of `Spec B`.

This proves the input `AlgebraicGeometry.Scheme.ZariskiRiemann.ExistsValuationCenter` of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkSpecializes_comp_stalkBaseMap` —
  `B ⟶ 𝒪_{Y,y} ⟶ K` is the inclusion `B ⊆ K`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.existsValuationCenter`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath_of_etaleInputs`
  — the implication with the two Zariski–Riemann inputs discharged.

## References

* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)

/-- **The specialization map to `K` is a map over `B`**: for `j(η) ⤳ y`, the composite
`B ⟶ 𝒪_{Y,y} ⟶ 𝒪_{Y,j(η)} ⟶ K` is the inclusion `B ⊆ K`. -/
theorem stalkSpecializes_comp_stalkBaseMap {y : ↥M.Y}
    (hsp : M.j (closedPoint (FractionRing B)) ⤳ y) :
    (M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j).hom.comp
        (M.stalkBaseMap y) = algebraMap B (FractionRing B) := by
  have h2 : ∀ h : Spec (CommRingCat.of (FractionRing B)) ⟶ Spec (CommRingCat.of B),
      h = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) →
      (Spec (CommRingCat.of B)).presheaf.germ ⊤ (h (closedPoint (FractionRing B))) trivial ≫
        stalkClosedPointTo h =
        (ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rintro h rfl
    exact germ_stalkClosedPointTo_Spec _
  have h3 := h2 _ M.fac
  rw [stalkClosedPointTo_comp] at h3
  have h4 := Hom.germ_stalkMap M.f ⊤ (M.j (closedPoint (FractionRing B))) trivial
  have h5 : M.Y.presheaf.Γgerm y ≫ M.Y.presheaf.stalkSpecializes hsp =
      M.Y.presheaf.Γgerm (M.j (closedPoint (FractionRing B))) :=
    M.Y.presheaf.germ_stalkSpecializes (U := ⊤) (y := y) trivial hsp
  have key : (ΓSpecIso (CommRingCat.of B)).inv ≫ M.f.appTop ≫ M.Y.presheaf.Γgerm y ≫
      M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j =
      CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    calc (ΓSpecIso (CommRingCat.of B)).inv ≫ M.f.appTop ≫ M.Y.presheaf.Γgerm y ≫
          M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j
        = (ΓSpecIso (CommRingCat.of B)).inv ≫ M.f.appTop ≫
          M.Y.presheaf.Γgerm (M.j (closedPoint (FractionRing B))) ≫
            Scheme.stalkClosedPointTo M.j := by
          rw [reassoc_of% h5]
      _ = (ΓSpecIso (CommRingCat.of B)).inv ≫
          ((Spec (CommRingCat.of B)).presheaf.germ ⊤ (M.f (M.j (closedPoint (FractionRing B))))
            trivial ≫ M.f.stalkMap (M.j (closedPoint (FractionRing B)))) ≫
            Scheme.stalkClosedPointTo M.j := by
          rw [h4]
          rfl
      _ = (ΓSpecIso (CommRingCat.of B)).inv ≫ (ΓSpecIso (CommRingCat.of B)).hom ≫
          CommRingCat.ofHom (algebraMap B (FractionRing B)) :=
          congrArg ((ΓSpecIso (CommRingCat.of B)).inv ≫ ·) ((Category.assoc _ _ _).trans h3)
      _ = _ := Iso.inv_hom_id_assoc _ _
  exact congrArg CommRingCat.Hom.hom key

end ProperModel

/-- **Points in the closure of `j(η)` over the closed point are centers** (the input
`AlgebraicGeometry.Scheme.ZariskiRiemann.ExistsValuationCenter`): a valuation ring dominating the
image of `𝒪_{Y,y}` in `Frac B` (Stacks 00IA) is centered at `y` and dominates `B`. -/
theorem existsValuationCenter : ExistsValuationCenter.{u} := by
  intro B _ _ _ M y hy hf
  have : Subsingleton ↥(Spec (CommRingCat.of (FractionRing B))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing B)))
  have hsp : M.j (closedPoint (FractionRing B)) ⤳ y := by
    have hr : Set.range M.j = {M.j (closedPoint (FractionRing B))} := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        rw [Subsingleton.elim p (closedPoint (FractionRing B))]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    rw [hr] at hy
    exact specializes_iff_mem_closure.2 hy
  set σ := M.Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo M.j
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.range σ.hom).exists_le_valuationSubring
  have hR : ∀ a, σ.hom a ∈ V := fun a ↦ hle (show σ.hom a ∈ σ.hom.range from ⟨a, rfl⟩)
  have hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V := fun b ↦ by
    rw [← M.stalkSpecializes_comp_stalkBaseMap hsp]
    exact hR _
  have hP : ∀ a ∈ maximalIdeal (M.Y.presheaf.stalk y), σ.hom a ≠ 0 → (σ.hom a)⁻¹ ∉ V := by
    intro a ha h0 hinv
    let x : (LocalSubring.range σ.hom).toSubring := ⟨σ.hom a, ⟨a, rfl⟩⟩
    have hx : ¬ IsUnit x := by
      rintro ⟨w, hw⟩
      obtain ⟨b, hb⟩ : ((↑w⁻¹ : (LocalSubring.range σ.hom).toSubring) : FractionRing B) ∈
          σ.hom.range := (↑w⁻¹ : (LocalSubring.range σ.hom).toSubring).2
      have hmul : σ.hom a * σ.hom b = 1 := by
        have hw' : ((w : (LocalSubring.range σ.hom).toSubring) : FractionRing B) = σ.hom a :=
          congrArg Subtype.val hw
        rw [hb, ← hw']
        exact congrArg Subtype.val w.mul_inv
      have hab1 : a * b - 1 ∉ maximalIdeal (M.Y.presheaf.stalk y) := fun h ↦
        (maximalIdeal.isMaximal (M.Y.presheaf.stalk y)).ne_top ((Ideal.eq_top_iff_one _).2
          (by simpa using Ideal.sub_mem _ (Ideal.mul_mem_right b _ ha) h))
      have hu : IsUnit (σ.hom (a * b - 1)) :=
        ((mem_maximalIdeal _).not.1 hab1 |> not_not.1).map σ.hom
      rw [map_sub, map_mul, hmul, map_one, sub_self] at hu
      exact not_isUnit_zero hu
    exact hx (hloc.map_nonunit x (isUnit_of_coe_inv_mem (V := V) (Subring.inclusion hle x) h0 hinv))
  have hc : M.centerPoint V hV = y := M.centerPoint_eq_of_stalk_mem V hV hsp hR hP
  have hl : IsLocalHom (valuationSubringBaseMap V hV) := by
    rw [isLocalHom_iff_comap_closedPoint]
    have h := congrArg (fun g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of B) ↦
      g (closedPoint V)) (M.center_comp_f V hV)
    dsimp only at h
    change Spec.map (CommRingCat.ofHom (valuationSubringBaseMap V hV)) (closedPoint V) = _
    rw [← h]
    change M.f (M.centerPoint V hV) = _
    rw [hc, hf]
  exact ⟨V, hV, hl, hc⟩

/-- **`ValuationGermDeath n` implies `CenteredGermDeath n`**, given the cofilteredness of the
proper models and the étale-sheaf and scheme inputs `GermDeathSpreads`, `StalkZeroOffClosure`,
`DeadAtStableUnderRefinement`, `KillsOfForallDeadAt`, `FibreOpenOverEtale`, `CenterOpenBasic` and
`FiniteLiftsAtPoint`: the Zariski–Riemann inputs `ExistsValuationCenter` and
`ZariskiRiemannFibreQuasiCompact` are proved (`existsValuationCenter`,
`zariskiRiemannFibreQuasiCompact`). -/
theorem centeredGermDeath_of_valuationGermDeath_of_etaleInputs {n : ℕ}
    (hVGD : ValuationGermDeath.{u} n)
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hspread : GermDeathSpreads.{u}) (hzero : StalkZeroOffClosure.{u})
    (hstab : DeadAtStableUnderRefinement.{u}) (hkills : KillsOfForallDeadAt.{u})
    (hfibre : FibreOpenOverEtale.{u}) (hbasic : CenterOpenBasic.{u})
    (hfin : FiniteLiftsAtPoint.{u}) : CenteredGermDeath.{u} n :=
  centeredGermDeath_of_valuationGermDeath hVGD hcof hspread hzero hstab hkills hfibre
    existsValuationCenter hbasic hfin zariskiRiemannFibreQuasiCompact

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
