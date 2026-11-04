module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.SecondBlowupCharts

/-!
# The second blow-up of Hironaka's local model over the line `V(x, y)`

Hironaka's example (the source of [Stacks, Tag 08J1]) is, near its special point, the two-step
blow-up of `Spec A`, `A = k[x, y, z]`: first in `(x, y)`, then in the strict transform of
`(x - y², z)`. On the chart `U₂ = Spec k[v, y, z]` of the first blow-up (`x = (v + y)·y`) the
second blow-up is `Bl_{(v,z)} Spec k[v, y, z]`, with the two charts
`secondChartOne : Spec k[v, y, z₂] ⟶ Bl` (`z = v·z₂`) and `secondChartTwo : Spec k[v₂, y, z] ⟶ Bl`
(`v = z·v₂`).

This file proves the part of the flatness statement (M1) of the local model that lives over `U₂`:
the base change of `Bl_{(v,z)} Spec k[v, y, z] ⟶ Spec A` to the line `V(x, y) = Spec k[z]` is flat
over `k[z]`. On the two charts the base change is `Spec k[v, z₂]` with `z ↦ v·z₂` and
`Spec k[v₂, z]` with `z ↦ z`.

## Main results

* `Stacks.Examples.HironakaLocalModel.flat_of_two_opens`: a morphism is flat as soon as it is flat
  on two open immersions covering its source.
* `Stacks.Examples.HironakaLocalModel.isPullback_secondChartOne_line`,
  `Stacks.Examples.HironakaLocalModel.isPullback_secondChartTwo_line`: the base change of the two
  charts to `V(x, y)`.
* `Stacks.Examples.HironakaLocalModel.flat_secondBlowup_line`: **(M1 over `U₂`)** the base change
  of `Bl_{(v,z)} Spec k[v, y, z] ⟶ Spec k[x, y, z]` to `V(x, y)` is flat over `V(x, y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Examples.HironakaLocalModel

/-- **A morphism that is flat on two open immersions covering its source is flat.** -/
theorem flat_of_two_opens {X Y₁ Y₂ Z : Scheme.{u}} (f : X ⟶ Z) (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X)
    [IsOpenImmersion g₁] [IsOpenImmersion g₂]
    (hcov : ∀ x, x ∈ Set.range g₁ ∨ x ∈ Set.range g₂) (h₁ : Flat (g₁ ≫ f))
    (h₂ : Flat (g₂ ≫ f)) : Flat f := by
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun b : Bool => bif b then g₂.opensRange else g₁.opensRange) ?_ ?_
  · refine eq_top_iff.mpr fun x _ => ?_
    simpa [Bool.exists_bool, or_comm] using hcov x
  · have key {Y} (g : Y ⟶ X) [IsOpenImmersion g] (h : Flat (g ≫ f)) :
        Flat (g.opensRange.ι ≫ f) := by
      rw [← g.isoOpensRange_inv_comp, Category.assoc]
      infer_instance
    exact Bool.rec (key g₁ h₁) (key g₂ h₂)

variable (k : Type u) [Field k]

/-- The second blow-up of the local model on `U₂`, as a scheme over `Spec k[x, y, z]`:
`Bl_{(v,z)} Spec k[v, y, z] ⟶ Spec k[v, y, z] ⟶ Spec k[x, y, z]`, the second map being `Spec` of
`x ↦ (v + y)·y`. -/
abbrev secondBlowupToBase :
    blowUp (idealSheafSpec (secondCentre k)) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) :=
  blowUpToBase (idealSheafSpec (secondCentre k)) ≫
    Spec.map (CommRingCat.ofHom (towerMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k))

/-- The line `V(x, y) = Spec k[z]` in `Spec k[x, y, z]`. -/
abbrev lineι :
    Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 3) k)) :=
  Spec.map (CommRingCat.ofHom (lineMap k : MvPolynomial (Fin 3) k →+* Polynomial k))

/-- The line `V(x, y)` is a closed subscheme of `Spec k[x, y, z]`. -/
instance : IsClosedImmersion (lineι k) :=
  IsClosedImmersion.spec_of_surjective _ (lineMap_surjective k)

/-- On the first chart `Spec k[v, y, z₂]`, the second blow-up maps to `Spec k[x, y, z]` by `Spec`
of the composite of `towerMap` with `chartOneMap`. -/
theorem secondChartOne_secondBlowupToBase :
    secondChartOne k ≫ secondBlowupToBase k =
      Spec.map (CommRingCat.ofHom (((chartOneMap k).comp (towerMap k) : _ →ₐ[k] _) :
        MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)) := by
  rw [secondBlowupToBase, ← Category.assoc, secondChartOne_blowUpToBase, ← Spec.map_comp]
  rfl

/-- On the second chart `Spec k[v₂, y, z]`, the second blow-up maps to `Spec k[x, y, z]` by `Spec`
of the composite of `towerMap` with `chartTwoMap`. -/
theorem secondChartTwo_secondBlowupToBase :
    secondChartTwo k ≫ secondBlowupToBase k =
      Spec.map (CommRingCat.ofHom (((chartTwoMap k).comp (towerMap k) : _ →ₐ[k] _) :
        MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)) := by
  rw [secondBlowupToBase, ← Category.assoc, secondChartTwo_blowUpToBase, ← Spec.map_comp]
  rfl

/-- **The base change of the first chart to `V(x, y)`** is `Spec k[v, z₂]`, over `Spec k[z]` by
`z ↦ v·z₂`, and into the chart `Spec k[v, y, z₂]` by `y = 0`. -/
theorem isPullback_secondChartOne_line :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (surfaceMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 2) k)))
      (Spec.map (CommRingCat.ofHom
        (lineToChartOne k : Polynomial k →+* MvPolynomial (Fin 2) k)))
      (secondChartOne k ≫ secondBlowupToBase k) (lineι k) := by
  rw [secondChartOne_secondBlowupToBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chartOne k)

/-- **The base change of the second chart to `V(x, y)`** is `Spec k[v₂, z]`, over `Spec k[z]` by
`z ↦ z`, and into the chart `Spec k[v₂, y, z]` by `y = 0`. -/
theorem isPullback_secondChartTwo_line :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (surfaceMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 2) k)))
      (Spec.map (CommRingCat.ofHom
        (lineToChartTwo k : Polynomial k →+* MvPolynomial (Fin 2) k)))
      (secondChartTwo k ≫ secondBlowupToBase k) (lineι k) := by
  rw [secondChartTwo_secondBlowupToBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chartTwo k)

/-- From the base change of a chart `c` to `V(x, y)`, the open immersion of that base change into
the base change of the blow-up, its image (the inverse image of the chart), and its structure map
over `V(x, y)`. -/
private theorem exists_chart_of_isPullback {Y W : Scheme.{u}} (c : Y ⟶ blowUp (idealSheafSpec
      (secondCentre k))) [IsOpenImmersion c] (p : W ⟶ Y) (q : W ⟶ Spec (CommRingCat.of
      (Polynomial k))) (h : IsPullback p q (c ≫ secondBlowupToBase k) (lineι k)) :
    ∃ j : W ⟶ pullback (secondBlowupToBase k) (lineι k), IsOpenImmersion j ∧
      j ≫ pullback.snd _ _ = q ∧
      ∀ x, pullback.fst (secondBlowupToBase k) (lineι k) x ∈ Set.range c → x ∈ Set.range j := by
  set F := secondBlowupToBase k
  set G := lineι k
  let j : W ⟶ pullback F G := pullback.lift (p ≫ c) q (by rw [Category.assoc, h.w])
  have hj₂ : j ≫ pullback.snd F G = q := pullback.lift_snd _ _ _
  have hleft : IsPullback j p (pullback.fst F G) c := by
    refine IsPullback.of_right (h₁₂ := pullback.snd F G) (v₁₃ := G) (h₂₂ := F) ?_
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback F G).flip
    rw [hj₂]
    exact h.flip
  refine ⟨j, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hleft.flip inferInstance,
    hj₂, fun x hx => ?_⟩
  obtain ⟨w, rfl⟩ : x ∈ Set.range (pullback.fst (pullback.fst F G) c) := by
    rwa [IsOpenImmersion.range_pullbackFst]
  refine ⟨hleft.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hleft.isoPullback_inv_fst]

/-- **(M1 over `U₂`.)** The base change of the second blow-up
`Bl_{(v,z)} Spec k[v, y, z] ⟶ Spec k[x, y, z]` to the line `V(x, y) = Spec k[z]` is flat over
`k[z]`. On the two charts it is `Spec k[v, z₂] ⟶ Spec k[z]`, `z ↦ v·z₂`, and
`Spec k[v₂, z] ⟶ Spec k[z]`, `z ↦ z`, both flat (`k[z]` is a principal ideal domain and the two
rings are torsion-free over it). -/
theorem flat_secondBlowup_line :
    Flat (pullback.snd (secondBlowupToBase k) (lineι k)) := by
  obtain ⟨j₁, h₁, hs₁, hr₁⟩ :=
    exists_chart_of_isPullback k _ _ _ (isPullback_secondChartOne_line k)
  obtain ⟨j₂, h₂, hs₂, hr₂⟩ :=
    exists_chart_of_isPullback k _ _ _ (isPullback_secondChartTwo_line k)
  refine flat_of_two_opens _ j₁ j₂ (fun x => ?_) ?_ ?_
  · exact (secondChart_cover (pullback.fst (secondBlowupToBase k) (lineι k) x)).imp (hr₁ x) (hr₂ x)
  · rw [hs₁, Flat.SpecMap_iff]
    exact flat_lineToChartOne k
  · rw [hs₂, Flat.SpecMap_iff]
    exact flat_lineToChartTwo k

/-- The base change of the second blow-up to the line `V(x, y)` is flat over `V(x, y)`. -/
instance : Flat (pullback.snd (secondBlowupToBase k) (lineι k)) :=
  flat_secondBlowup_line k

end Stacks.Examples.HironakaLocalModel

end
