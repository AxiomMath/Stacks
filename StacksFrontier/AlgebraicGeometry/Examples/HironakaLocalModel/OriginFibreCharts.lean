module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.CentreFamily
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.SecondBlowupFibre
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.FirstBlowupStrictCentreLine
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# Hironaka's local model: four affine charts of the source of the tower

Let `k` be a field, `A = k[x, y, z]`, `I = (x, y)`, `J = (x - y², z)`, `B₁ = Bl_I Spec A` with its
charts `U₁ = Spec k[x, y₁, z]` and `U₂ = Spec k[x₁, y, z]`, `J'` the strict transform of `V(J)`
on `B₁`, and `T = Bl_{J'} B₁ ⟶ Spec A` the tower of Hironaka's example (the source of
[Stacks, Tag 08J1]). This file covers `T` by four affine open subschemes and computes on each of
them the ideal of the fibre of `T` over the origin.

* Over `U₂`, after `v = x₁ - y`, the second blow-up is `Bl_{(v,z)} Spec k[v, y, z]`
  ([Stacks, Tag 0805]); its two charts give `U₂₁ = Spec k[v, y, z₂]` (`z = v·z₂`,
  `Stacks.Examples.HironakaLocalModel.towerChartOne`) and `U₂₂ = Spec k[v₂, y, z]` (`v = z·v₂`,
  `Stacks.Examples.HironakaLocalModel.towerChartTwo`). There the fibre over the origin is cut out
  by `(y, v·z₂)` and by `(y, z)`.
* Over the basic opens `D(1 - x·y₁²)` and `D(z)` of `U₁`, which miss `V(J') = V(1 - x·y₁², z)`,
  the second blow-up is an isomorphism ([Stacks, Tag 02OS])
  (`Stacks.Examples.HironakaLocalModel.towerBasicChart`).

A point of `U₁` on `V(J')` lies in `U₂`, so the four charts cover `T`
(`Stacks.Examples.HironakaLocalModel.towerChart_cover`). Inequalities of ideal sheaves on `T` can
then be checked on the four charts (`Stacks.Examples.HironakaLocalModel.le_of_comap_le_four`).

## Main results

* `Stacks.Examples.HironakaLocalModel.towerChart_cover`: the four charts cover `T`.
* `Stacks.Examples.HironakaLocalModel.comap_towerChartOne_towerFibreIdeal`,
  `...comap_towerChartTwo_towerFibreIdeal`, `...comap_towerBasicChart_towerFibreIdeal`: the fibre
  over the origin on the charts.
* `Stacks.Examples.HironakaLocalModel.le_of_comap_le_four`,
  `Stacks.Examples.HironakaLocalModel.comap_ker_le_ker_of_comp_eq`: the tools for comparing ideal
  sheaves on the charts.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.TwoStepTower

universe u

namespace Stacks.Examples.HironakaLocalModel

/-! ### Generalities on ideal sheaves -/

/-- **An upper bound for the inverse image of a kernel.** If `ψ ≫ f = h ≫ g`, then the inverse
image along `g` of the kernel of `f` is contained in the kernel of `h`. -/
theorem comap_ker_le_ker_of_comp_eq {V W Y T : Scheme.{u}} (f : Y ⟶ T) (g : W ⟶ T)
    (ψ : V ⟶ Y) (h : V ⟶ W) (hc : ψ ≫ f = h ≫ g) : f.ker.comap g ≤ h.ker := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.Hom.ker_comp, ← hc]
  exact Scheme.Hom.le_ker_comp ψ f

/-- An inequality of inverse images along an open immersion from an affine scheme is an
inequality of the ideals on its image. -/
theorem ideal_image_top_le_of_comap_le {X Z : Scheme.{u}} [IsAffine Z] (g : Z ⟶ X)
    [IsOpenImmersion g] {I J : X.IdealSheafData} (h : I.comap g ≤ J.comap g) :
    I.ideal ⟨g ''ᵁ ⊤, (isAffineOpen_top Z).image_of_isOpenImmersion g⟩ ≤
      J.ideal ⟨g ''ᵁ ⊤, (isAffineOpen_top Z).image_of_isOpenImmersion g⟩ := by
  have hi : (I.comap g).ideal ⟨⊤, isAffineOpen_top Z⟩ ≤ (J.comap g).ideal ⟨⊤, isAffineOpen_top Z⟩ :=
    h _
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
  exact (Ideal.comap_le_comap_iff_of_surjective _
    (ConcreteCategory.bijective_of_isIso ((g.appIso ⊤).inv)).2 _ _).mp hi

/-- A point in the range of an open immersion lies in the image of the top open. -/
theorem mem_image_top_of_mem_range {X Z : Scheme.{u}} (g : Z ⟶ X) [IsOpenImmersion g] {x : X}
    (hx : x ∈ Set.range g) : x ∈ g ''ᵁ ⊤ := by
  change x ∈ ((g ''ᵁ ⊤ : X.Opens) : Set X)
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
  exact hx

/-- **Inequalities of ideal sheaves are checked on a cover by four affine open subschemes.** -/
theorem le_of_comap_le_four {X Z₁ Z₂ Z₃ Z₄ : Scheme.{u}} [IsAffine Z₁] [IsAffine Z₂]
    [IsAffine Z₃] [IsAffine Z₄] (g₁ : Z₁ ⟶ X) (g₂ : Z₂ ⟶ X) (g₃ : Z₃ ⟶ X) (g₄ : Z₄ ⟶ X)
    [IsOpenImmersion g₁] [IsOpenImmersion g₂] [IsOpenImmersion g₃] [IsOpenImmersion g₄]
    (hcov : ∀ x, x ∈ Set.range g₁ ∨ x ∈ Set.range g₂ ∨ x ∈ Set.range g₃ ∨ x ∈ Set.range g₄)
    {I J : X.IdealSheafData} (h₁ : I.comap g₁ ≤ J.comap g₁) (h₂ : I.comap g₂ ≤ J.comap g₂)
    (h₃ : I.comap g₃ ≤ J.comap g₃) (h₄ : I.comap g₄ ≤ J.comap g₄) : I ≤ J := by
  let U : Fin 4 → X.affineOpens :=
    ![⟨g₁ ''ᵁ ⊤, (isAffineOpen_top Z₁).image_of_isOpenImmersion g₁⟩,
      ⟨g₂ ''ᵁ ⊤, (isAffineOpen_top Z₂).image_of_isOpenImmersion g₂⟩,
      ⟨g₃ ''ᵁ ⊤, (isAffineOpen_top Z₃).image_of_isOpenImmersion g₃⟩,
      ⟨g₄ ''ᵁ ⊤, (isAffineOpen_top Z₄).image_of_isOpenImmersion g₄⟩]
  refine Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun i => ?_
  · refine eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
    rcases hcov x with h | h | h | h
    · exact ⟨0, mem_image_top_of_mem_range g₁ h⟩
    · exact ⟨1, mem_image_top_of_mem_range g₂ h⟩
    · exact ⟨2, mem_image_top_of_mem_range g₃ h⟩
    · exact ⟨3, mem_image_top_of_mem_range g₄ h⟩
  · fin_cases i
    · exact ideal_image_top_le_of_comap_le g₁ h₁
    · exact ideal_image_top_le_of_comap_le g₂ h₂
    · exact ideal_image_top_le_of_comap_le g₃ h₃
    · exact ideal_image_top_le_of_comap_le g₄ h₄

/-- The inverse image of the ideal sheaf of an ideal along `Spec φ` is the ideal sheaf of its
extension. -/
theorem comap_specMap_idealSheafSpec {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (K : Ideal R) :
    (idealSheafSpec K).comap (Spec.map (CommRingCat.ofHom φ)) = idealSheafSpec (K.map φ) := by
  rw [idealSheafSpec, Stacks.AlgebraicGeometry.comap_ofIdealTop, Ideal.map_map, idealSheafSpec,
    Ideal.map_map, ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The kernel of `Spec φ` is the ideal sheaf of the kernel of `φ`. -/
theorem ker_specMap_ofHom {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (Spec.map (CommRingCat.ofHom φ)).ker = idealSheafSpec (RingHom.ker φ) :=
  Scheme.ker_SpecMap _

variable (k : Type u) [Field k]

/-- An inequality of ideals of `k[x, y, z]` gives one of their ideal sheaves. -/
theorem idealSheafOf_inf_le {a b c : Ideal (Ring3 k)} (h : a ⊓ b ≤ c) :
    idealSheafOf k a ⊓ idealSheafOf k b ≤ idealSheafOf k c := by
  refine Scheme.IdealSheafData.le_of_isAffine fun g hg => ?_
  have h1 : g ∈ (idealSheafOf k a).ideal ⟨⊤, isAffineOpen_top _⟩ := hg.1
  have h2 : g ∈ (idealSheafOf k b).ideal ⟨⊤, isAffineOpen_top _⟩ := hg.2
  rw [idealSheafOf_ideal_top] at h1 h2 ⊢
  obtain ⟨f, rfl⟩ := (gammaEquiv k).surjective g
  rw [gammaEquiv_mem_map_iff] at h1 h2 ⊢
  exact h ⟨h1, h2⟩

/-! ### The second blow-up over the chart `U₂` -/

/-- The strict transform `J'` of `V(J)` on the first blow-up. -/
abbrev strictCurve : (blowUp (centreIdeal k)).IdealSheafData :=
  strictCentre (centreIdeal k) (curveIdeal k)

/-- **The second blow-up over `U₂`**, with its composite to the first blow-up: the open
immersion of `Bl_{(v,z)} Spec k[v, y, z]` into the source of the tower given by
[Stacks, Tag 0805] and the change of coordinates `x₁ = v + y`. -/
theorem exists_chartTwoBlowupι :
    ∃ e : blowUp (idealSheafSpec (secondCentre k)) ⟶ blowUp (strictCurve k),
      IsOpenImmersion e ∧
      e ≫ blowUpToBase (strictCurve k) = blowUpToBase (idealSheafSpec (secondCentre k)) ≫
        Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k)) ≫ chartι k 1 ∧
      ∀ w, blowUpToBase (strictCurve k) w ∈ Set.range (chartι k 1) → w ∈ Set.range e := by
  obtain ⟨h₂, sq₂⟩ := exists_isPullback_blowUp_of_comap_eq
    (strictCentre (centreIdeal k) (curveIdeal k)) (chartι k 1) _ (comap_chartι_one_strictCentre k)
  obtain ⟨h₁, sq₁⟩ := exists_isPullback_blowUp_of_comap_eq
    (idealSheafOf k (Ideal.span {X 0 - X 1, X 2}))
    (Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k))) _ (comap_shift_idealSheafOf k)
  have sq := sq₁.flip.paste_horiz sq₂.flip
  refine ⟨h₁ ≫ h₂, MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance,
    ?_, fun w hw => mem_range_of_isPullback sq w ?_⟩
  · rw [Category.assoc, ← sq₂.w, ← Category.assoc, ← sq₁.w, Category.assoc]
  · obtain ⟨u, hu⟩ := hw
    obtain ⟨u', rfl⟩ :=
      (Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k))).surjective u
    exact ⟨u', by rw [Scheme.Hom.comp_apply, hu]⟩

/-- The second blow-up over the chart `U₂`, as an open of the source of the tower. -/
def chartTwoBlowupι : blowUp (idealSheafSpec (secondCentre k)) ⟶ blowUp (strictCurve k) :=
  (exists_chartTwoBlowupι k).choose

/-- The second blow-up over `U₂` is an open immersion into the source of the tower. -/
instance : IsOpenImmersion (chartTwoBlowupι k) := (exists_chartTwoBlowupι k).choose_spec.1

/-- The second blow-up over `U₂` lies over `U₂`. -/
theorem chartTwoBlowupι_comp :
    chartTwoBlowupι k ≫ blowUpToBase (strictCurve k) =
      blowUpToBase (idealSheafSpec (secondCentre k)) ≫
        Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k)) ≫ chartι k 1 :=
  (exists_chartTwoBlowupι k).choose_spec.2.1

/-- Every point of the source of the tower over `U₂` lies in the second blow-up over `U₂`. -/
theorem mem_range_chartTwoBlowupι (w : blowUp (strictCurve k))
    (hw : blowUpToBase (strictCurve k) w ∈ Set.range (chartι k 1)) :
    w ∈ Set.range (chartTwoBlowupι k) :=
  (exists_chartTwoBlowupι k).choose_spec.2.2 w hw

/-- The chart `U₂₁ = Spec k[v, y, z₂]` (`z = v·z₂`) of the source of the tower. -/
def towerChartOne : Spec (.of (Ring3 k)) ⟶ blowUp (strictCurve k) :=
  secondChartOne k ≫ chartTwoBlowupι k

/-- The chart `U₂₂ = Spec k[v₂, y, z]` (`v = z·v₂`) of the source of the tower. -/
def towerChartTwo : Spec (.of (Ring3 k)) ⟶ blowUp (strictCurve k) :=
  secondChartTwo k ≫ chartTwoBlowupι k

/-- The chart `U₂₁` is an open immersion into the source of the tower. -/
instance : IsOpenImmersion (towerChartOne k) := by
  dsimp only [towerChartOne]; infer_instance

/-- The chart `U₂₂` is an open immersion into the source of the tower. -/
instance : IsOpenImmersion (towerChartTwo k) := by
  dsimp only [towerChartTwo]; infer_instance

/-- A chart of the second blow-up over `Spec ψ`, composed with `chartTwoBlowupι`, lies over
`Spec (ψ ∘ shiftHom)`. -/
private theorem comp_chartTwoBlowupι_blowUpToBase
    (c : Spec (.of (Ring3 k)) ⟶ blowUp (idealSheafSpec (secondCentre k)))
    (ψ : Ring3 k →ₐ[k] Ring3 k)
    (hc : c ≫ blowUpToBase (idealSheafSpec (secondCentre k)) =
      Spec.map (CommRingCat.ofHom (ψ : Ring3 k →+* Ring3 k))) :
    (c ≫ chartTwoBlowupι k) ≫ blowUpToBase (strictCurve k) =
      Spec.map (CommRingCat.ofHom ((ψ.comp (shiftHom k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) ≫ chartι k 1 := by
  rw [Category.assoc, chartTwoBlowupι_comp, ← Category.assoc, hc, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A chart of the tower over `Spec (ψ ∘ shiftHom)` lies over `Spec (ψ ∘ towerMap)`. -/
private theorem comp_strictTower_of_comp_blowUpToBase
    (c : Spec (.of (Ring3 k)) ⟶ blowUp (strictCurve k)) (ψ : Ring3 k →ₐ[k] Ring3 k)
    (hc : c ≫ blowUpToBase (strictCurve k) =
      Spec.map (CommRingCat.ofHom ((ψ.comp (shiftHom k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) ≫ chartι k 1) :
    c ≫ strictTower (centreIdeal k) (curveIdeal k) =
      Spec.map (CommRingCat.ofHom ((ψ.comp (towerMap k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) := by
  rw [strictTower, ← Category.assoc, hc, Category.assoc, chartι_comp_blowUpToBase,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← shiftHom_comp_chartHom_one]
  rfl

/-- The chart `U₂₁` over the first blow-up: `x₁ ↦ v + y`, `y ↦ y`, `z ↦ v·z₂`. -/
theorem towerChartOne_comp_blowUpToBase :
    towerChartOne k ≫ blowUpToBase (strictCurve k) =
      Spec.map (CommRingCat.ofHom (((chartOneMap k).comp (shiftHom k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) ≫ chartι k 1 :=
  comp_chartTwoBlowupι_blowUpToBase k _ _ secondChartOne_blowUpToBase

/-- The chart `U₂₂` over the first blow-up: `x₁ ↦ z·v₂ + y`, `y ↦ y`, `z ↦ z`. -/
theorem towerChartTwo_comp_blowUpToBase :
    towerChartTwo k ≫ blowUpToBase (strictCurve k) =
      Spec.map (CommRingCat.ofHom (((chartTwoMap k).comp (shiftHom k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) ≫ chartι k 1 :=
  comp_chartTwoBlowupι_blowUpToBase k _ _ secondChartTwo_blowUpToBase

/-- The chart `U₂₁` over `Spec A`. -/
theorem towerChartOne_comp_strictTower :
    towerChartOne k ≫ strictTower (centreIdeal k) (curveIdeal k) =
      Spec.map (CommRingCat.ofHom (((chartOneMap k).comp (towerMap k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) :=
  comp_strictTower_of_comp_blowUpToBase k _ _ (towerChartOne_comp_blowUpToBase k)

/-- The chart `U₂₂` over `Spec A`. -/
theorem towerChartTwo_comp_strictTower :
    towerChartTwo k ≫ strictTower (centreIdeal k) (curveIdeal k) =
      Spec.map (CommRingCat.ofHom (((chartTwoMap k).comp (towerMap k) : Ring3 k →ₐ[k] Ring3 k) :
        Ring3 k →+* Ring3 k)) :=
  comp_strictTower_of_comp_blowUpToBase k _ _ (towerChartTwo_comp_blowUpToBase k)

/-! ### The second blow-up over basic opens of `U₁` -/

/-- The equations `(1 - x·y₁², z)` of `V(J')` on `U₁`. -/
abbrev strictSpan : Ideal (Ring3 k) := Ideal.span {1 - X 0 * X 1 ^ 2, (X 2 : Ring3 k)}

/-- The equation `1 - x·y₁²` lies in the ideal `strictSpan`. -/
theorem unitEq_mem_strictSpan : unitEq k ∈ strictSpan k :=
  Ideal.subset_span (Set.mem_insert _ _)

/-- The equation `z` lies in the ideal `strictSpan`. -/
theorem X_two_mem_strictSpan : (X 2 : Ring3 k) ∈ strictSpan k :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- The basic open `D(f)` of `U₁`, as an open of the first blow-up. -/
abbrev firstBasicι (f : Ring3 k) :
    Spec (.of (Localization.Away f)) ⟶ blowUp (centreIdeal k) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ring3 k) (Localization.Away f))) ≫ chartι k 0

/-- A basic open `D(f)` of `U₁` with `f` an equation of `V(J')` misses `V(J')`. -/
theorem range_firstBasicι_subset (f : Ring3 k) (hf : f ∈ strictSpan k) :
    ((firstBasicι k f).opensRange : Set (blowUp (centreIdeal k))) ⊆
      ((strictCurve k).support : Set (blowUp (centreIdeal k)))ᶜ := by
  rintro _ ⟨d, rfl⟩ hd
  rw [Scheme.Hom.comp_apply] at hd
  have hd' : Spec.map (CommRingCat.ofHom (algebraMap (Ring3 k) (Localization.Away f))) d ∈
      ((strictCentre (centreIdeal k) (curveIdeal k)).comap (chartι k 0)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hd
  rw [comap_chartι_zero_strictCentre] at hd'
  have hmem := le_asIdeal_of_mem_support k _ _ hd' hf
  rw [specMap_asIdeal, Ideal.mem_comap] at hmem
  exact d.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
    (IsLocalization.Away.algebraMap_isUnit f))

/-- A point of `U₁` off `V(f)` lies in `D(f)`. -/
theorem chartι_zero_mem_range_firstBasicι (f : Ring3 k) (q : ambient k)
    (hq : f ∉ (primeOf k q).asIdeal) : chartι k 0 q ∈ Set.range (firstBasicι k f) := by
  have hr : q ∈ Set.range (PrimeSpectrum.comap (algebraMap (Ring3 k) (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hq
  obtain ⟨d, hd⟩ := hr
  let d' : Spec (CommRingCat.of (Localization.Away f)) := d
  have hd' : Spec.map (CommRingCat.ofHom (algebraMap (Ring3 k) (Localization.Away f))) d' = q :=
    hd
  exact ⟨d', by rw [firstBasicι, Scheme.Hom.comp_apply, hd']⟩

/-- **The second blow-up over a basic open of `U₁` missing `V(J')` is an isomorphism**
([Stacks, Tag 02OS]): an open immersion of `D(f) ⊆ U₁` into the source of the tower, lifting
`D(f) ⟶ B₁`, whose range contains every point lying over `D(f)`. -/
theorem exists_towerBasicChart (f : Ring3 k) (hf : f ∈ strictSpan k) :
    ∃ e : Spec (.of (Localization.Away f)) ⟶ blowUp (strictCurve k), IsOpenImmersion e ∧
      e ≫ blowUpToBase (strictCurve k) = firstBasicι k f ∧
      ∀ w, blowUpToBase (strictCurve k) w ∈ Set.range (firstBasicι k f) → w ∈ Set.range e := by
  set J' := strictCurve k
  set W := (firstBasicι k f).opensRange
  have := isIso_blowUpToBase_restrict_of_subset_compl_support J' W
    (range_firstBasicι_subset k f hf)
  let e : Spec (CommRingCat.of (Localization.Away f)) ⟶ blowUp J' :=
    (firstBasicι k f).isoOpensRange.hom ≫ inv (blowUpToBase J' ∣_ W) ≫ (blowUpToBase J' ⁻¹ᵁ W).ι
  have he : e ≫ blowUpToBase J' = firstBasicι k f := by
    simp only [e, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨e, inferInstance, he, fun w hw => ?_⟩
  obtain ⟨d, hd⟩ := hw
  have h1 : blowUpToBase J' (e d) = firstBasicι k f d := by rw [← Scheme.Hom.comp_apply, he]
  refine ⟨d, blowUpToBase_injective_of_notMem_support J' ?_ (h1.trans hd)⟩
  rw [h1]
  exact range_firstBasicι_subset k f hf ⟨d, rfl⟩

/-- The open `D(f)` of `U₁` (for `f` an equation of `V(J')`), as an open of the source of the
tower. -/
def towerBasicChart (f : Ring3 k) (hf : f ∈ strictSpan k) :
    Spec (.of (Localization.Away f)) ⟶ blowUp (strictCurve k) :=
  (exists_towerBasicChart k f hf).choose

/-- The chart `D(f)` is an open immersion into the source of the tower. -/
instance (f : Ring3 k) (hf : f ∈ strictSpan k) : IsOpenImmersion (towerBasicChart k f hf) :=
  (exists_towerBasicChart k f hf).choose_spec.1

/-- The chart `D(f)` lies over `D(f) ⊆ U₁`. -/
theorem towerBasicChart_comp (f : Ring3 k) (hf : f ∈ strictSpan k) :
    towerBasicChart k f hf ≫ blowUpToBase (strictCurve k) = firstBasicι k f :=
  (exists_towerBasicChart k f hf).choose_spec.2.1

/-- Every point of the source of the tower lying over `D(f) ⊆ U₁` lies in the chart `D(f)`. -/
theorem mem_range_towerBasicChart (f : Ring3 k) (hf : f ∈ strictSpan k)
    (w : blowUp (strictCurve k))
    (hw : blowUpToBase (strictCurve k) w ∈ Set.range (firstBasicι k f)) :
    w ∈ Set.range (towerBasicChart k f hf) :=
  (exists_towerBasicChart k f hf).choose_spec.2.2 w hw

/-- The chart `D(f)` over `Spec A`. -/
theorem towerBasicChart_comp_strictTower (f : Ring3 k) (hf : f ∈ strictSpan k) :
    towerBasicChart k f hf ≫ strictTower (centreIdeal k) (curveIdeal k) =
      Spec.map (CommRingCat.ofHom ((algebraMap (Ring3 k) (Localization.Away f)).comp
        (chartHom k 0 : Ring3 k →+* Ring3 k))) := by
  rw [strictTower, ← Category.assoc, towerBasicChart_comp, firstBasicι, Category.assoc,
    chartι_comp_blowUpToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **The four charts cover the source of the tower**: `U₂₁`, `U₂₂`, and the parts of the source
over `D(1 - x·y₁²)` and `D(z)` in `U₁`. -/
theorem towerChart_cover (w : blowUp (strictCurve k)) :
    w ∈ Set.range (towerChartOne k) ∨ w ∈ Set.range (towerChartTwo k) ∨
      w ∈ Set.range (towerBasicChart k (unitEq k) (unitEq_mem_strictSpan k)) ∨
      w ∈ Set.range (towerBasicChart k (X 2) (X_two_mem_strictSpan k)) := by
  have hU₂ : blowUpToBase (strictCurve k) w ∈ Set.range (chartι k 1) →
      w ∈ Set.range (towerChartOne k) ∨ w ∈ Set.range (towerChartTwo k) := by
    intro h
    obtain ⟨u, rfl⟩ := mem_range_chartTwoBlowupι k w h
    rcases secondChart_cover u with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨a, rfl⟩
  obtain ⟨i, q, hq⟩ := exists_chartι_eq k (blowUpToBase (strictCurve k) w)
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · by_cases hJ : strictSpan k ≤ (primeOf k q).asIdeal
    · obtain ⟨q', hq'⟩ := exists_chartι_one_eq_chartι_zero k q hJ
      exact (hU₂ ⟨q', hq'.trans hq⟩).imp_right Or.inl
    · have hgen : unitEq k ∉ (primeOf k q).asIdeal ∨ (X 2 : Ring3 k) ∉ (primeOf k q).asIdeal := by
        by_contra! hc
        apply hJ
        rw [Ideal.span_le]
        rintro _ (rfl | rfl)
        exacts [hc.1, hc.2]
      rcases hgen with h | h
      · exact Or.inr (Or.inr (Or.inl (mem_range_towerBasicChart k _ _ w
          (hq ▸ chartι_zero_mem_range_firstBasicι k _ q h))))
      · exact Or.inr (Or.inr (Or.inr (mem_range_towerBasicChart k _ _ w
          (hq ▸ chartι_zero_mem_range_firstBasicι k _ q h))))
  · exact (hU₂ ⟨q, hq⟩).imp_right Or.inl

/-! ### The fibre over the origin on the charts -/

/-- The ideal sheaf of the fibre of the tower over the origin. -/
abbrev towerFibreIdeal : (blowUp (strictCurve k)).IdealSheafData :=
  (originIdealSheaf k).comap (strictTower (centreIdeal k) (curveIdeal k))

/-- On `U₂₁` the fibre over the origin is `(y, v·z₂)`. -/
theorem comap_towerChartOne_towerFibreIdeal :
    (towerFibreIdeal k).comap (towerChartOne k) =
      idealSheafOf k (Ideal.span {X 1, X 0 * X 2}) := by
  rw [towerFibreIdeal, ← Scheme.IdealSheafData.comap_comp, towerChartOne_comp_strictTower,
    comap_specMap_idealSheafOf, ← fibreIdeal_chartOne]

/-- On `U₂₂` the fibre over the origin is `(y, z)`. -/
theorem comap_towerChartTwo_towerFibreIdeal :
    (towerFibreIdeal k).comap (towerChartTwo k) = idealSheafOf k (Ideal.span {X 1, X 2}) := by
  rw [towerFibreIdeal, ← Scheme.IdealSheafData.comap_comp, towerChartTwo_comp_strictTower,
    comap_specMap_idealSheafOf, ← fibreIdeal_chartTwo]

/-- On `D(f) ⊆ U₁` the fibre over the origin is the extension of `(x, y, z)`. -/
theorem comap_towerBasicChart_towerFibreIdeal (f : Ring3 k) (hf : f ∈ strictSpan k) :
    (towerFibreIdeal k).comap (towerBasicChart k f hf) =
      idealSheafSpec ((originIdeal k).map ((algebraMap (Ring3 k) (Localization.Away f)).comp
        (chartHom k 0 : Ring3 k →+* Ring3 k))) := by
  rw [towerFibreIdeal, ← Scheme.IdealSheafData.comap_comp, towerBasicChart_comp_strictTower]
  exact comap_specMap_idealSheafSpec _ _

end Stacks.Examples.HironakaLocalModel

end
