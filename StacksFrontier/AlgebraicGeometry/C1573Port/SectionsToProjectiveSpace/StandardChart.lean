module

public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away

namespace Stacks.SectionsToProjectiveSpace.C1573
end Stacks.SectionsToProjectiveSpace.C1573

/-!
# Morphisms into a standard chart of projective space

Let `D₊(Tⱼ) ⊆ ℙⁿ_ℤ` be the `j`-th standard chart, with its ratio coordinates `Tₗ / Tⱼ`. A morphism
`f : Y ⟶ ℙⁿ_ℤ` landing in `D₊(Tⱼ)` is the morphism attached by
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` to the pulled back ratios, a
family of global sections of `𝒪_Y` whose `j`-th member is `1`.

## Main definitions

* `Stacks.SectionsToProjectiveSpace.C1573.chartOpen`: the standard chart `D₊(Tⱼ)`.
* `Stacks.SectionsToProjectiveSpace.C1573.chartRatio`: the ratio `Tₗ / Tⱼ` as a global section of
  the chart.

## Main results

* `Stacks.SectionsToProjectiveSpace.C1573.chartOpen_ι_eq`: the inclusion of the chart is the
  morphism attached to its ratio coordinates.
* `Stacks.SectionsToProjectiveSpace.C1573.exists_eq_toProjectiveSpaceAtUniverse`: a morphism
  landing in `D₊(Tⱼ)` is the morphism attached to the pulled back ratios.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Opposite

universe u

namespace Stacks.SectionsToProjectiveSpace

open _root_.Stacks.SectionsToProjectiveSpace.C1573
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

/-- The `j`-th standard chart `D₊(Tⱼ)` of the integral model of projective space. -/
abbrev C1573.chartOpen (j : Fin (n + 1)) : (projectiveSpaceAtUniverse.{u} n).Opens :=
  Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X j)

/-- The variable `Tₗ` is homogeneous of degree `1 • 1`. -/
theorem C1573.X_mem_coordGrading_smul (l : Fin (n + 1)) :
    (MvPolynomial.X l : coordRing.{u} n) ∈ coordGrading.{u} n (1 • 1) := by
  simpa using X_mem_coordGrading_one l

/-- The ring map from the degree-zero localization at `Tⱼ` to the global sections of the chart
`D₊(Tⱼ)`. -/
abbrev C1573.chartRingHom (j : Fin (n + 1)) :
    Away (coordGrading.{u} n) (MvPolynomial.X j) →+* Γ((chartOpen.{u} j).toScheme, ⊤) :=
  ((Proj.basicOpenIsoAway (coordGrading.{u} n) (MvPolynomial.X j)
    (X_mem_coordGrading_one j) Nat.one_pos).hom ≫ (chartOpen.{u} j).topIso.inv).hom

/-- The ratio `Tₗ / Tⱼ`, as a global section of the chart `D₊(Tⱼ)`. -/
def C1573.chartRatio (j l : Fin (n + 1)) : Γ((chartOpen.{u} j).toScheme, ⊤) :=
  chartRingHom j (Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one j) 1 (MvPolynomial.X l)
    (X_mem_coordGrading_smul l))

/-- The `j`-th ratio on the `j`-th chart is `1`. -/
theorem C1573.chartRatio_self (j : Fin (n + 1)) : chartRatio.{u} j j = 1 := by
  rw [chartRatio, ← map_one (chartRingHom.{u} j)]
  congr 1
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, HomogeneousLocalization.val_one]
  convert Localization.mk_self (⟨MvPolynomial.X j ^ 1, ⟨1, rfl⟩⟩ :
    Submonoid.powers (MvPolynomial.X j : coordRing.{u} n)) using 2
  exact (pow_one _).symm

/-- The ratio coordinates of a chart span the unit ideal. -/
theorem C1573.span_range_chartRatio (j : Fin (n + 1)) :
    Ideal.span (Set.range (chartRatio.{u} j)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩)
    (by rw [chartRatio_self]; exact isUnit_one)

/-- Two ring homomorphisms out of the degree-zero localization at `Tⱼ` agreeing on the ratios
`Tₗ / Tⱼ` are equal. -/
theorem C1573.away_ringHom_ext_ratio {P : Type*} [CommRing P] (j : Fin (n + 1))
    {φ ψ : Away (coordGrading.{u} n) (MvPolynomial.X j) →+* P}
    (h : ∀ l, φ (Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one j) 1 (MvPolynomial.X l)
      (X_mem_coordGrading_smul l)) =
        ψ (Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one j) 1 (MvPolynomial.X l)
          (X_mem_coordGrading_smul l))) : φ = ψ := by
  suffices hc : φ.comp (Stacks.AlgebraicGeometry.ProjPolyChart.chartHom (ULift.{u} ℤ) n j) =
      ψ.comp (Stacks.AlgebraicGeometry.ProjPolyChart.chartHom (ULift.{u} ℤ) n j) by
    refine RingHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ :=
      Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_surjective (ULift.{u} ℤ) n j z
    exact RingHom.congr_fun hc w
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · obtain ⟨x⟩ := r
    have hx : (ULift.up x : ULift.{u} ℤ) = (x : ULift.{u} ℤ) := by ext; simp
    simp only [hx, map_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_X,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartCoord]
    exact h k.1

/-- **The inclusion of a standard chart is the morphism of its ratio coordinates.** -/
theorem C1573.chartOpen_ι_eq (j : Fin (n + 1)) :
    (chartOpen.{u} j).ι =
      toProjectiveSpaceAtUniverse (chartRatio.{u} j) (span_range_chartRatio j) := by
  set Y := (chartOpen.{u} j).toScheme
  set s := chartRatio.{u} j
  have hs := span_range_chartRatio.{u} j
  have hj : sectionsHom s (MvPolynomial.X j) = 1 := by
    rw [sectionsHom_X]
    exact chartRatio_self j
  have hW : Y.basicOpen ((sectionsHom s) (MvPolynomial.X j)) = ⊤ := by
    rw [hj, Scheme.basicOpen_one]
  have h1 := Stacks.ProjGlobalSectionsAppTop.ι_comp_fromOfGlobalSections (coordGrading.{u} n)
    (sectionsHom s) (map_irrelevant_eq_top s hs) Nat.one_pos (X_mem_coordGrading_one j)
  have h2 := Stacks.ProjGlobalSectionsAppTop.eq_toBasicOpenOfGlobalSections
    (coordGrading.{u} n) (sectionsHom s)
    Nat.one_pos (X_mem_coordGrading_one j) (Y.basicOpen ((sectionsHom s) (MvPolynomial.X j))).ι ?_
  · rw [← h2] at h1
    have : IsIso (Y.basicOpen ((sectionsHom s) (MvPolynomial.X j))).ι := by
      rw [hW, ← Scheme.topIso_hom]
      infer_instance
    exact ((cancel_epi _).mp h1).symm
  · refine CommRingCat.hom_ext (away_ringHom_ext_ratio j fun l => ?_)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one
        (coordGrading.{u} n) (sectionsHom s)
        (X_mem_coordGrading_one j) 1 (MvPolynomial.X l) (X_mem_coordGrading_smul l)
        (v := 1) (by rw [mul_one, hj, map_one]),
      one_pow, mul_one, sectionsHom_X]
    show (Y.basicOpen (s j)).ι.appTop (s l) = _
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, sectionsHom_X]
    show _ = (Y.presheaf.map (homOfLE le_top).op ≫ Y.presheaf.map (eqToHom _).op) (s l)
    rw [← Functor.map_comp]
    rfl

/-- **A morphism landing in a standard chart is the morphism of the pulled back ratios.** If
`f : Y ⟶ ℙⁿ_ℤ` lands in `D₊(Tⱼ)`, then `f` is the morphism attached to a family of global sections
of `𝒪_Y` whose `j`-th member is `1`. -/
theorem C1573.exists_eq_toProjectiveSpaceAtUniverse {Y : Scheme.{u}}
    (f : Y ⟶ projectiveSpaceAtUniverse.{u} n) (j : Fin (n + 1))
    (h : Set.range f.base ⊆ (chartOpen.{u} j : Set (projectiveSpaceAtUniverse.{u} n))) :
    ∃ (s : Fin (n + 1) → Γ(Y, ⊤)) (hs : Ideal.span (Set.range s) = ⊤),
      s j = 1 ∧ f = toProjectiveSpaceAtUniverse s hs := by
  have hr : Set.range f.base ⊆ Set.range (chartOpen.{u} j).ι.base := by
    rwa [Scheme.Opens.range_ι]
  set ψ := IsOpenImmersion.lift (chartOpen.{u} j).ι f hr
  have hψ : ψ ≫ (chartOpen.{u} j).ι = f := IsOpenImmersion.lift_fac _ _ _
  have hs := span_range_comp ψ.appTop.hom _ (span_range_chartRatio.{u} j)
  refine ⟨fun l => ψ.appTop (chartRatio.{u} j l), hs, ?_, ?_⟩
  · simp only [chartRatio_self, map_one]
  · rw [← hψ, chartOpen_ι_eq]
    exact Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality ψ _ _ hs

end Stacks.SectionsToProjectiveSpace

end
