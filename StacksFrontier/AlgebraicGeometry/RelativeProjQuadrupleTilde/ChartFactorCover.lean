module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ClassifyingData
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Fraction
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# The classifying morphism factors locally through a standard open of degree `d` of a chart

Let `(f : T → S, d, L, ψ)` be a quadruple of positive degree in Situation 01NN and
`h : T ⟶ Proj_S(𝒜)` the morphism it classifies. Every point `t` of `T` has an open
neighbourhood `V` lying over an affine open `U` of the base, on which `h` factors as
`g ≫ chart U` with `g` landing in the standard open `D₊(c)` of a section `c` of `𝒜_d` over `U`.

The morphism `h` lands in the relative degree-`d` open `U_d` by construction, whose part inside
the chart over `U` is the union of the `D₊(e)` for `e` homogeneous of degree `d`
(`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_preimage_degreeOpen`); reading `e`
through the identification of the two graded rings of sections over `U` gives `c`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.exists_chart_factor`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation Stacks.RelativeProj.Situation.QuadrupleChart

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

variable (s : Stacks.RelativeProj.Situation.{u})

/-- A point of a chart whose image lies in the relative degree-`d` open lies in the standard open
of a section of `𝒜_d` over the affine open of the chart. -/
theorem exists_mem_basicOpen_of_chart_mem_degreeOpen (U : s.base.affineOpens) (d : ℕ)
    (z : AlgebraicGeometry.Proj (s.sectionRingGrading U.1))
    (hz : relativeProjChart s U z ∈ (relativeProjData s).degreeOpen d) :
    ∃ c : s.sectionPieces U.1 d, z ∈ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) := by
  set e := situationChartIso s ⟨U.1, U.2⟩
  have hez : e.hom (e.inv z) = z := by
    show (e.inv ≫ e.hom) z = z
    rw [e.inv_hom_id]
    rfl
  have key : (relativeProjData s).chart U.1 U.2 (e.inv z) = relativeProjChart s U z := by
    show relativeProjChart s U (e.hom (e.inv z)) = _
    rw [hez]
  have hx : e.inv z ∈ (relativeProjData s).chart U.1 U.2 ⁻¹ᵁ (relativeProjData s).degreeOpen d := by
    show (relativeProjData s).chart U.1 U.2 (e.inv z) ∈ (relativeProjData s).degreeOpen d
    rwa [key]
  rw [RelativeProjData.chart_preimage_degreeOpen (relativeProjData s) U.1 U.2 d] at hx
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  set y := sectionGradedHom s ⟨U.1, U.2⟩ a.1
  have hy : y ∈ s.sectionRingGrading U.1 d := Graded.map_mem _ a.2
  obtain ⟨c, hcy⟩ := hy
  refine ⟨c, ?_⟩
  have hinv : sectionGradedInv s ⟨U.1, U.2⟩ y = a.1 :=
    DFunLike.congr_fun (sectionGradedInv_comp_hom s ⟨U.1, U.2⟩) a.1
  have hb : e.inv z ∈ e.hom ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) y := by
    rwa [← hinv] at ha
  rw [← hez]
  show e.hom (e.inv z) ∈ Proj.basicOpen (s.sectionRingGrading U.1) (DirectSum.of _ d c)
  rwa [hcy]

/-- **The classifying morphism factors locally through a standard open of degree `d` of a
chart.** -/
theorem exists_chart_factor {T : Scheme.{u}} (f : T ⟶ s.base) {d : ℕ} (hd : 0 < d)
    (P : Quadruple f s.algebra (d : ℤ)) (t : T) :
    ∃ (V : T.Opens) (_ : t ∈ V) (U : s.base.affineOpens) (c : s.sectionPieces U.1 d)
      (g : V.toScheme ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1)),
      V ≤ f ⁻¹ᵁ U.1 ∧
      V.ι ≫ classifyingHom s (by exact_mod_cast hd) P = g ≫ relativeProjChart s U ∧
      (⊤ : V.toScheme.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c) := by
  set h := classifyingHom s (by exact_mod_cast hd : (0 : ℤ) < d) P
  have hπ : h ≫ relativeProjToBase s = f := classifyingHom_comp_toBase s _ P
  obtain ⟨U', hU', hft, -⟩ := (Opens.isBasis_iff_nbhd.mp s.base.isBasis_affineOpens)
    (show f t ∈ (⊤ : s.base.Opens) from trivial)
  set U : s.base.affineOpens := ⟨U', hU'⟩
  have hht : h t ∈ (relativeProjChart s U).opensRange := by
    rw [opensRange_relativeProjChart]
    show (h ≫ relativeProjToBase s) t ∈ U.1
    rwa [hπ]
  obtain ⟨z, hz⟩ := hht
  have hdeg : h t ∈ (relativeProjData s).degreeOpen d := by
    have key : ∀ (n : ℕ) (_ : n = d) (x : ((relativeProjData s).degreeOpen n : Scheme.{u})),
        (x.1 : relativeProj s) ∈ (relativeProjData s).degreeOpen d := by
      rintro n rfl x
      exact x.2
    exact key _ (Int.toNat_natCast d) (Fd.degreeOpenEquiv' (sheafGradedAlgebra s)
      (relativeProjData s) (by exact_mod_cast hd : (0 : ℤ) < d) T (Fd.mk f P) t)
  obtain ⟨c, hc⟩ := exists_mem_basicOpen_of_chart_mem_degreeOpen s U d z (hz ▸ hdeg)
  set D := relativeProjChart s U ''ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)
  set V := f ⁻¹ᵁ U.1 ⊓ h ⁻¹ᵁ D
  have hr : Set.range (V.ι ≫ h).base ⊆ Set.range (relativeProjChart s U).base := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, -, hw⟩ := v.2.2
    exact ⟨w, hw⟩
  have hfac := IsOpenImmersion.lift_fac (relativeProjChart s U) (V.ι ≫ h) hr
  refine ⟨V, ⟨hft, z, hc, hz⟩, U, c, IsOpenImmersion.lift (relativeProjChart s U) (V.ι ≫ h) hr,
    inf_le_left, hfac.symm, fun v _ => ?_⟩
  obtain ⟨w, hw, hwv⟩ := v.2.2
  have hinj := (relativeProjChart s U).isOpenEmbedding.injective
  have : IsOpenImmersion.lift (relativeProjChart s U) (V.ι ≫ h) hr v = w := by
    apply hinj
    rw [← Scheme.Hom.comp_apply, hfac]
    exact hwv.symm
  show (IsOpenImmersion.lift (relativeProjChart s U) (V.ι ≫ h) hr).base v ∈
    Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)
  rwa [this]

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
