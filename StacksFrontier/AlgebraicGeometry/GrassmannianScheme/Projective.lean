module

public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Plucker
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# The Grassmannian is projective

The Plücker morphism `G(k, n) ⟶ ℙᴺ_ℤ` is a closed immersion. The preimage of the standard open
`D₊(T_ι)` is the chart of `G(k, n)` attached to `ι`: a point of the chart attached to `κ` with
nonvanishing minor on the columns `ι` lies in the chart attached to `ι`
(`AlgebraicGeometry.Grassmannian.exists_comp_chart_eq_of_isUnit_det`). On that chart the
Plücker morphism is given on rings by `T_λ/T_ι ↦` the minor of the chart matrix on `λ`, and every
chart coordinate `x_{j,i}` is such a minor, namely the one on `ι` with `ι i` replaced by `j`
(`AlgebraicGeometry.Grassmannian.plucker_chartMatrix_setValue`); so the ring map is surjective and
the chart maps to `D₊(T_ι)` by a closed immersion. Base change gives a closed immersion
`G(k, n)_S ⟶ ℙᴺ_S` over `S`, so `G(k, n)_S` is projective over `S`.

## Main results

* `AlgebraicGeometry.Grassmannian.preimage_pluckerMap_basicOpen`: the preimage of `D₊(T_ι)` is
  the chart attached to `ι`.
* `AlgebraicGeometry.Grassmannian.isClosedImmersion_pluckerMap`: **the Plücker morphism is a
  closed immersion.**
* `AlgebraicGeometry.Grassmannian.isProjectiveMorphism_schemeOver`: `G(k, n)_S` is H-projective
  over `S`.
* `AlgebraicGeometry.Grassmannian.isProjective_schemeOver`: **`G(k, n)_S` is projective over
  `S`.**

## References

* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SectionsToProjectiveSpace

universe u

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Grassmannian

/-! ### Two general facts -/

/-- A global function whose nonvanishing locus is everything is a unit. -/
theorem isUnit_of_basicOpen_eq_top {T : Scheme.{u}} (r : Γ(T, ⊤)) (h : T.basicOpen r = ⊤) :
    IsUnit r :=
  T.toRingedSpace.isUnit_of_isUnit_germ ⊤ r fun x hx =>
    (T.mem_basicOpen r x hx).mp (by rwa [h])

/-- **A morphism restricted over an open `U` is a closed immersion** as soon as the preimage of
`U` is the image of an open immersion `j` whose composite with the morphism corestricts to a
closed immersion into `U`. -/
theorem isClosedImmersion_morphismRestrict_of_comp_eq {X Y A : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (j : A ⟶ X) [IsOpenImmersion j] (hj : j.opensRange = f ⁻¹ᵁ U)
    (c : A ⟶ U.toScheme) [IsClosedImmersion c] (hc : c ≫ U.ι = j ≫ f) :
    IsClosedImmersion (f ∣_ U) := by
  have e : Set.range j = Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι, ← hj]
    rfl
  have heq : f ∣_ U = (IsOpenImmersion.isoOfRangeEq j (f ⁻¹ᵁ U).ι e).inv ≫ c := by
    rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc, hc,
      IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]
  rw [heq]
  infer_instance

variable {k n : ℕ}

/-! ### The preimage of a standard open -/

/-- The standard open of `ℙᴺ` attached to an embedding. -/
abbrev pluckerOpen (ι : Fin (n - k) ↪ Fin n) :
    (projectiveSpaceAtUniverse.{u} (pluckerDim k n)).Opens :=
  Proj.basicOpen (coordGrading.{u} (pluckerDim k n)) (MvPolynomial.X (pluckerIndexEquiv k n ι))

/-- The chart's Plücker morphism maps the whole chart into the standard open of its index. -/
theorem preimage_chartPluckerMap_self (ι : Fin (n - k) ↪ Fin n) :
    chartPluckerMap.{u} ι ⁻¹ᵁ pluckerOpen.{u} ι = ⊤ := by
  rw [pluckerOpen, chartPluckerMap, preimage_basicOpen, pluckerSections_self, Scheme.basicOpen_one]

/-- A point of the chart attached to `κ` whose Plücker image lies in `D₊(T_ι)` lies in the chart
attached to `ι`. -/
theorem chart_apply_mem_opensRange_of_mem_preimage {κ ι : Fin (n - k) ↪ Fin n}
    {y : Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ)))}
    (hy : y ∈ chartPluckerMap κ ⁻¹ᵁ pluckerOpen ι) :
    chart.{u} k n κ y ∈ (chart.{u} k n ι).opensRange := by
  rw [pluckerOpen, chartPluckerMap, preimage_basicOpen] at hy
  let W := (Spec (.of (MvPolynomial (ChartIndex.{u} κ) (ULift.{u} ℤ)))).basicOpen
    (pluckerSections κ (𝟙 _) (pluckerIndexEquiv k n ι))
  have hdet : IsUnit ((chartMatrix κ (AffineSpace.toSpecMvPolyIntEquiv _ W.ι)).submatrix
      id ι).det := by
    have h₁ : ((chartMatrix κ (AffineSpace.toSpecMvPolyIntEquiv _ W.ι)).submatrix id ι).det =
        W.ι.appTop (pluckerSections κ (𝟙 _) (pluckerIndexEquiv k n ι)) := by
      rw [appTop_pluckerSections, Category.comp_id, pluckerSections, Equiv.symm_apply_apply]
      rfl
    rw [h₁]
    exact isUnit_of_basicOpen_eq_top _ <| by
      rw [← Scheme.preimage_basicOpen_top, Scheme.Opens.ι_preimage_self]
  obtain ⟨g, hg⟩ := exists_comp_chart_eq_of_isUnit_det W.ι hdet
  obtain ⟨z, hz⟩ : y ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  refine ⟨g z, ?_⟩
  simpa only [Scheme.Hom.comp_apply, hz] using congrArg (fun f => f z) hg

/-- **The preimage of the standard open `D₊(T_ι)` under the Plücker morphism is the chart attached
to `ι`.** -/
theorem preimage_pluckerMap_basicOpen (ι : Fin (n - k) ↪ Fin n) :
    pluckerMap.{u} k n ⁻¹ᵁ pluckerOpen.{u} ι = (chart.{u} k n ι).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨κ, y, rfl⟩ := exists_mem_range_chart k n x
    exact chart_apply_mem_opensRange_of_mem_preimage
      (by rwa [← chart_comp_pluckerMap k n κ, Scheme.Hom.comp_preimage])
  · rintro ⟨y, rfl⟩
    change (chart k n ι ≫ pluckerMap k n) y ∈ pluckerOpen ι
    rw [chart_comp_pluckerMap]
    exact (preimage_chartPluckerMap_self ι).ge trivial

/-! ### The chart morphisms into the standard opens -/

/-- The chart coordinates generate the ring of the chart. -/
theorem mem_range_of_chartCoords_mem {ι : Fin (n - k) ↪ Fin n}
    {B : Type*} [CommRing B]
    (φ : B →+* Γ(Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))), ⊤))
    (h : ∀ a, chartCoords ι a ∈ φ.range) : Function.Surjective φ := by
  intro y
  obtain ⟨p, rfl⟩ : ∃ p, (Scheme.ΓSpecIso (.of (MvPolynomial (ChartIndex.{u} ι)
      (ULift.{u} ℤ)))).inv p = y :=
    ⟨(Scheme.ΓSpecIso _).hom y, by
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩
  change (Scheme.ΓSpecIso _).inv.hom p ∈ φ.range
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : (MvPolynomial.C a : MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)) =
        ((a.down : ℤ) : MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ)) := by
      rw [← map_intCast (MvPolynomial.C (σ := ChartIndex.{u} ι) (R := ULift.{u} ℤ))]
      exact congrArg MvPolynomial.C (ULift.ext _ _ (by simp))
    refine ⟨((a.down : ℤ) : B), ?_⟩
    rw [map_intCast, hC, map_intCast]
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p a hp =>
    rw [map_mul]
    exact mul_mem hp (h a)

/-- The restriction of a chart's Plücker morphism over the standard open of its index is a
closed immersion. -/
theorem isClosedImmersion_resLE_chartPluckerMap (ι : Fin (n - k) ↪ Fin n) :
    IsClosedImmersion ((chartPluckerMap.{u} ι).resLE (pluckerOpen.{u} ι) ⊤
      (preimage_chartPluckerMap_self ι).ge) := by
  have : IsAffine (⊤ : (Spec (.of (MvPolynomial (ChartIndex.{u} ι)
      (ULift.{u} ℤ)))).Opens).toScheme := isAffineOpen_top _
  have : IsAffine (pluckerOpen ι).toScheme :=
    Proj.isAffineOpen_basicOpen (coordGrading.{u} (pluckerDim k n)) _
      (X_mem_coordGrading_one (pluckerIndexEquiv k n ι)) Nat.one_pos
  refine IsClosedImmersion.of_surjective_of_isAffine _
    (Stacks.ChartDictionary.surjective_appTop_resLE_of_surjective _ _ ?_)
  apply mem_range_of_chartCoords_mem
  rintro ⟨⟨⟨j, hj⟩, i⟩⟩
  refine ⟨Stacks.ChartDictionary.chartCoord.{u} (pluckerDim k n) (pluckerIndexEquiv k n ι)
    (pluckerIndexEquiv k n (ι.setValue i j)), ?_⟩
  refine (Stacks.ChartDictionary.appLE_chartCoord_top (pluckerSections ι (𝟙 _))
    (span_pluckerSections ι (𝟙 _)) (pluckerSections_self ι (𝟙 _)) _ _).trans ?_
  rw [pluckerSections, Equiv.symm_apply_apply, plucker_chartMatrix_setValue]
  rfl

/-- The corestriction of a chart's Plücker morphism to the standard open of its index. -/
def chartPluckerCorestrict (ι : Fin (n - k) ↪ Fin n) :
    Spec (.of (MvPolynomial (ChartIndex.{u} ι) (ULift.{u} ℤ))) ⟶ (pluckerOpen.{u} ι).toScheme :=
  (Scheme.topIso _).inv ≫ (chartPluckerMap.{u} ι).resLE (pluckerOpen.{u} ι) ⊤
    (preimage_chartPluckerMap_self ι).ge

/-- The corestriction of a chart's Plücker morphism to the standard open of its index is a closed
immersion. -/
instance (ι : Fin (n - k) ↪ Fin n) : IsClosedImmersion (chartPluckerCorestrict.{u} ι) := by
  have := isClosedImmersion_resLE_chartPluckerMap ι
  unfold chartPluckerCorestrict
  infer_instance

/-- Composing the corestriction with the inclusion of the standard open recovers the chart's
Plücker morphism. -/
theorem chartPluckerCorestrict_ι (ι : Fin (n - k) ↪ Fin n) :
    chartPluckerCorestrict.{u} ι ≫ (pluckerOpen.{u} ι).ι = chartPluckerMap.{u} ι := by
  rw [chartPluckerCorestrict, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.toIso_inv_ι_assoc]

/-! ### The Plücker morphism is a closed immersion -/

variable (k n)

/-- **The Plücker morphism `G(k, n) ⟶ ℙᴺ_ℤ` is a closed immersion.** -/
instance isClosedImmersion_pluckerMap : IsClosedImmersion (pluckerMap.{u} k n) := by
  have hcover : ⨆ t : Fin (pluckerDim k n + 1),
      Proj.basicOpen (coordGrading.{u} (pluckerDim k n)) (MvPolynomial.X t) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _
      (projectiveSpaceOver.irrelevant_coordGrading_le_span_X (pluckerDim k n))
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ hcover fun t => ?_
  obtain ⟨ι, rfl⟩ := (pluckerIndexEquiv k n).surjective t
  exact isClosedImmersion_morphismRestrict_of_comp_eq (pluckerMap k n) (pluckerOpen ι)
    (chart k n ι) (preimage_pluckerMap_basicOpen ι).symm (chartPluckerCorestrict ι)
    ((chartPluckerCorestrict_ι ι).trans (chart_comp_pluckerMap k n ι).symm)

/-! ### Projectivity -/

/-- **`G(k, n)_S` is H-projective over `S`**: the base change of the Plücker morphism is a closed
immersion `G(k, n)_S ⟶ ℙᴺ_S` over `S`. -/
theorem isProjectiveMorphism_schemeOver (S : Scheme.{u}) :
    IsProjectiveMorphism (schemeOver.over k n S).hom := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun a c ha hc => @IsClosedImmersion.comp _ _ _ a c ha hc⟩
  refine ⟨pluckerDim k n, pullback.map (terminal.from S) (terminal.from (scheme.{u} k n))
    (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} (pluckerDim k n))) (𝟙 S)
    (pluckerMap k n) (𝟙 _) (by simp) (by simp), ?_,
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)⟩
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance
    (isClosedImmersion_pluckerMap k n) (Category.id_comp _).symm (by simp)

/-- **`G(k, n)_S` is projective over `S`.** -/
theorem isProjective_schemeOver (S : Scheme.{u}) : IsProjective (schemeOver.over k n S).hom :=
  (isProjectiveMorphism_schemeOver k n S).isProjective

end AlgebraicGeometry.Grassmannian

end
