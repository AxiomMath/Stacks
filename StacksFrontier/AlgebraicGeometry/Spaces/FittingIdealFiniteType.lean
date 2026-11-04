module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealChain
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteFromGeneratingSections

/-!
# The Fitting ideals of a finitely presented module are quasi-coherent of finite type

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be
a quasi-coherent `𝒪_F`-module whose sections over every affine étale chart form a finitely
presented module over the chart ring.  Then the `r`-th Fitting ideal sheaf
`AlgebraicGeometry.Space.fittingIdeal` of `G` is a quasi-coherent sheaf of ideals of finite type.

## Main results

* `AlgebraicGeometry.Space.fittingIdeal_isCartesianOnAffineCharts` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_fittingIdeal`: the Fitting ideal sheaf is
  cartesian on affine charts, hence quasi-coherent.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_fittingIdeal`: the Fitting ideal sheaf is of finite
  type.
* `AlgebraicGeometry.Space.isFiniteTypeQuasicoherentIdeal_fittingIdeal`: the Fitting ideals of a
  quasi-coherent module with finitely presented sections over the affine étale charts are
  quasi-coherent ideals of finite type.
* `isFiniteTypeQuasicoherentIdeal_fittingIdeal_of_isFinitePresentationOnSite`: the Fitting ideals
  of a finitely presented quasi-coherent module are quasi-coherent ideals of finite type.

## References

* [Stacks Project, Tag 0CZ5](https://stacks.math.columbia.edu/tag/0CZ5)
* [Stacks Project, Tag 0CZ3](https://stacks.math.columbia.edu/tag/0CZ3)
* [Stacks Project, Tag 0C3E](https://stacks.math.columbia.edu/tag/0C3E)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Over an affine étale chart `U`, a section lies in the `r`-th Fitting ideal sheaf if and only if
it lies in the chartwise Fitting ideal over `U`. -/
private theorem mem_fittingIdeal_affine_iff (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (a : chartRing B S hS F hF U) :
    a ∈ (fittingIdeal B S hS F hF G r).toSubmodule.obj (op U) ↔
      a ∈ @fittingIdealOnChart B S hS F hF G r U (hfin U hU) := by
  rw [fittingIdeal_obj_eq_fittingIdealOnChart G hG hfin r hU]
  exact Iff.rfl

/-! ### Quasi-coherence of the Fitting ideal sheaf -/

/-- The base change comparison of the `r`-th Fitting ideal sheaf along a morphism `f : V ⟶ U` of
affine étale charts is surjective. -/
theorem surjective_sectionsBaseChange_fittingIdeal (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) :
    Function.Surjective
      (sectionsBaseChange (fittingIdeal B S hS F hF G r).toSheafOfModules f) := by
  have _ := hfin U hU
  have _ := hfin V hV
  let _ := chartAlgebra (hF := hF) f
  let I := fittingIdeal B S hS F hF G r
  let Q : Ideal (chartRing B S hS F hF V) :=
    { carrier := {b | ∃ z, ((sectionsBaseChange I.toSheafOfModules f z).1 :
        chartRing B S hS F hF V) = b}
      zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
      add_mem' := fun ⟨zx, hzx⟩ ⟨zy, hzy⟩ =>
        ⟨zx + zy, by rw [map_add]; exact congrArg₂ (· + ·) hzx hzy⟩
      smul_mem' := fun c _ ⟨z, hz⟩ => ⟨c • z, by rw [map_smul]; exact congrArg (c * ·) hz⟩ }
  have hgen : ∀ b : chartRing B S hS F hF V,
      b ∈ I.toSubmodule.obj (op V) → b ∈ Q := by
    intro b hb
    have h₁ : b ∈ @fittingIdealOnChart B S hS F hF G r V (hfin V hV) :=
      (mem_fittingIdeal_affine_iff G hG hfin r hV b).mp hb
    rw [fittingIdealOnChart_baseChange_of_isCartesianOnAffineCharts G hG r hU hV f] at h₁
    refine Ideal.map_le_iff_le_comap.mpr (fun a ha => ?_) h₁
    exact ⟨TensorProduct.tmul _ (1 : chartRing B S hS F hF V)
      (⟨a, (mem_fittingIdeal_affine_iff G hG hfin r hU a).mpr ha⟩ :
        I.toSheafOfModules.val.obj (op U)),
      congrArg (fun w : I.toSheafOfModules.val.obj (op V) => (w.1 : chartRing B S hS F hF V))
        (chartBaseChange_one_tmul I.toSheafOfModules f _)⟩
  intro y
  obtain ⟨z, hz⟩ := hgen (y.1 : chartRing B S hS F hF V) y.2
  exact ⟨z, Subtype.ext hz⟩

/-- The `r`-th Fitting ideal sheaf of a module cartesian on affine charts, with finite sections
over the affine étale charts, is cartesian on affine charts. -/
theorem fittingIdeal_isCartesianOnAffineCharts (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) :
    IsCartesianOnAffineCharts (fittingIdeal B S hS F hF G r).toSheafOfModules :=
  isCartesianOnAffineCharts_submodule_unit_of_surjective B S hS ⟨F, hF⟩ _
    fun _ _ hU hV f => surjective_sectionsBaseChange_fittingIdeal G hG hfin r hU hV f

/-- The `r`-th Fitting ideal sheaf of a module cartesian on affine charts, with finite sections
over the affine étale charts, is quasi-coherent. -/
theorem isQuasicoherentOnSite_fittingIdeal (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) :
    (fittingIdeal B S hS F hF G r).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (fittingIdeal_isCartesianOnAffineCharts G hG hfin r)

/-! ### Finite type of the Fitting ideal sheaf -/

/-- The chartwise Fitting ideal of a finitely presented module over an affine étale chart is
finitely generated. -/
theorem fg_fittingIdealOnChart (G : Modules.{u, u} B S hS F hF) (r : ℕ)
    {W : SmallEtale B S hS F}
    (hfpW : Module.FinitePresentation (chartRing B S hS F hF W) (G.val.obj (op W))) :
    (@fittingIdealOnChart B S hS F hF G r W (by have := hfpW; infer_instance)).FG := by
  have _ := hfpW
  have _ : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) := inferInstance
  exact (fittingIdeal_basic_properties.{u, u, u, u} (R := chartRing B S hS F hF W)
    (M := G.val.obj (op W))).2.2.2.1 hfpW r

/-- Generators of the chartwise Fitting ideal over an affine étale chart restrict to generators
of the chartwise Fitting ideal over any affine étale chart below it. -/
theorem span_range_chartRestrict_eq_fittingIdealOnChart (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) {b a : SmallEtale B S hS F}
    (hb : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj b))
    (ha : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj a))
    (w : a ⟶ b) {n : ℕ} (g : Fin n → chartRing B S hS F hF b)
    (hg : Ideal.span (Set.range g) = @fittingIdealOnChart B S hS F hF G r b (hfin b hb)) :
    Ideal.span (Set.range fun i => chartRestrict (hF := hF) w (g i)) =
      @fittingIdealOnChart B S hS F hF G r a (hfin a ha) := by
  have _ := hfin b hb
  have _ := hfin a ha
  rw [fittingIdealOnChart_baseChange_of_isCartesianOnAffineCharts G hG r hb ha w, ← hg,
    Ideal.map_span, ← Set.range_comp]
  rfl

/-- The restrictions along `hh : V ⟶ b` of generators `g` of the chartwise Fitting ideal over an
affine étale chart `b` generate the `r`-th Fitting ideal sheaf over `V`: every section of the
Fitting ideal sheaf over a chart above `V` is, on the members of a covering, a combination of their
restrictions. -/
theorem generates_fittingIdeal (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) {b V : SmallEtale B S hS F}
    (hb : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj b))
    (hh : V ⟶ b) {n : ℕ} (g : Fin n → chartRing B S hS F hF b)
    (hg : Ideal.span (Set.range g) = @fittingIdealOnChart B S hS F hF G r b (hfin b hb))
    (hgmem : ∀ i, g i ∈ (fittingIdeal B S hS F hF G r).toSubmodule.obj (op b)) :
    PresheafOfModules.Generates (smallEtaleRingedSite B S hS F hF).J
      (fittingIdeal B S hS F hF G r).toSheafOfModules.val
      (fun i => ((fittingIdeal B S hS F hF G r).toSheafOfModules.val.map hh.op)
        ⟨g i, hgmem i⟩) := by
  intro Z f t
  obtain ⟨Jz, Yf, af, hYaff, hYcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F Z
  refine ⟨Sieve.ofArrows Yf af, hYcov, ?_⟩
  rintro W' gg ⟨Y', hh', u, ⟨j⟩, hggc⟩
  have _ := hfin b hb
  have _ := hfin (Yf j) (hYaff j)
  have hmor : hh' ≫ af j ≫ f ≫ hh = (gg ≫ f) ≫ hh :=
    ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm.trans
      (congrArg (fun w => (w ≫ f) ≫ hh) hggc)
  have hterm : ∀ i, chartRestrict (hF := hF) hh'
        (chartRestrict (hF := hF) (af j ≫ f ≫ hh) (g i)) =
      chartRestrict (hF := hF) (gg ≫ f) (chartRestrict (hF := hF) hh (g i)) := by
    intro i
    refine Eq.trans (DFunLike.congr_fun
      (chartRestrict_comp (hF := hF) (af j ≫ f ≫ hh) hh') (g i)).symm ?_
    exact (congrArg (fun w => chartRestrict (hF := hF) w (g i)) hmor).trans
      (DFunLike.congr_fun (chartRestrict_comp (hF := hF) hh (gg ≫ f)) (g i))
  have hlhs : chartRestrict (hF := hF) hh'
        (chartRestrict (hF := hF) (af j) t.1) =
      chartRestrict (hF := hF) gg t.1 :=
    (DFunLike.congr_fun (chartRestrict_comp (hF := hF) (af j) hh') t.1).symm.trans
      (congrArg (fun w => chartRestrict (hF := hF) w t.1) hggc)
  have hYj : chartRestrict (hF := hF) (af j) t.1 ∈
      Ideal.span (Set.range fun i =>
        chartRestrict (hF := hF) (af j ≫ f ≫ hh) (g i)) := by
    rw [span_range_chartRestrict_eq_fittingIdealOnChart G hG hfin r hb (hYaff j) _ g hg]
    exact (mem_fittingIdeal_affine_iff G hG hfin r (hYaff j) _).mp
      ((fittingIdeal B S hS F hF G r).toSubmodule.map_mem (af j).op t.2)
  obtain ⟨c₀, hc₀⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hYj
  refine ⟨fun i => chartRestrict (hF := hF) hh' (c₀ i), Subtype.ext ?_⟩
  have hfinal : ∑ i, chartRestrict (hF := hF) hh' (c₀ i) *
        chartRestrict (hF := hF) (gg ≫ f) (chartRestrict (hF := hF) hh (g i)) =
      chartRestrict (hF := hF) gg t.1 := by
    calc ∑ i, chartRestrict (hF := hF) hh' (c₀ i) *
          chartRestrict (hF := hF) (gg ≫ f) (chartRestrict (hF := hF) hh (g i))
        = ∑ i, chartRestrict (hF := hF) hh' (c₀ i *
            chartRestrict (hF := hF) (af j ≫ f ≫ hh) (g i)) :=
          Finset.sum_congr rfl fun i _ =>
            (congrArg (fun y => chartRestrict (hF := hF) hh' (c₀ i) * y)
              (hterm i).symm).trans
              (map_mul (chartRestrict (hF := hF) hh') (c₀ i) _).symm
      _ = chartRestrict (hF := hF) hh' (∑ i, c₀ i *
            chartRestrict (hF := hF) (af j ≫ f ≫ hh) (g i)) :=
          (map_sum (chartRestrict (hF := hF) hh') _ Finset.univ).symm
      _ = chartRestrict (hF := hF) hh' (chartRestrict (hF := hF) (af j) t.1) :=
          congrArg _ hc₀
      _ = chartRestrict (hF := hF) gg t.1 := hlhs
  exact Eq.trans (AddSubmonoidClass.coe_finsetSum _ _) hfinal

/-- Finitely presented sections over the affine étale charts are finite sections. -/
private theorem finite_sections_of_finitePresentation_sections (G : Modules.{u, u} B S hS F hF)
    (hfp : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.FinitePresentation (chartRing B S hS F hF W) (G.val.obj (op W))) :
    ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) := fun W hW =>
  have := hfp W hW
  inferInstance

/-- The `r`-th Fitting ideal sheaf of a module cartesian on affine charts, whose sections over the
affine étale charts are finitely presented, is of finite type. -/
theorem isFiniteTypeOnSite_fittingIdeal (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G)
    (hfp : ∀ W : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.FinitePresentation (chartRing B S hS F hF W) (G.val.obj (op W)))
    (r : ℕ) :
    SheafOfModules.IsFiniteTypeOnSite (fittingIdeal B S hS F hF G r).toSheafOfModules := by
  have hfin := finite_sections_of_finitePresentation_sections G hfp
  refine Stacks.SheafOfModules.isFiniteTypeOnSite_of_locally_finite_generators _ fun U => ?_
  obtain ⟨Jw, Wf, φ, hWaff, hWcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F U
  refine ⟨⟨Sieve.ofArrows Wf φ, hWcov⟩, fun V q hq => ?_⟩
  obtain ⟨V', hh, p, ⟨k⟩, -⟩ := hq
  have _ := hfin (Wf k) (hWaff k)
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (fg_fittingIdealOnChart G r (hfp (Wf k) (hWaff k)))
  have hgmem : ∀ i, g i ∈ (fittingIdeal B S hS F hF G r).toSubmodule.obj (op (Wf k)) := fun i =>
    (mem_fittingIdeal_affine_iff G hG hfin r (hWaff k) (g i)).mpr
      (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hgen := generates_fittingIdeal G hG hfin r (hWaff k) hh g hg hgmem
  exact ⟨SheafOfModules.generatingSectionsOfGenerates _ _ hgen,
    ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩⟩

/-! ### The Fitting ideals as quasi-coherent ideals of finite type -/

/-- For a quasi-coherent `𝒪_X`-module on an algebraic space `X` whose sections over every affine
étale chart form a finitely presented module over the chart ring, the `r`-th Fitting ideal `Fit_r`
is a quasi-coherent ideal of finite type. -/
theorem isFiniteTypeQuasicoherentIdeal_fittingIdeal (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    (hfp : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.FinitePresentation (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (r : ℕ) :
    IsFiniteTypeQuasicoherentIdeal B S hS X (fittingIdeal B S hS X.1 X.2 G r) := by
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hG
  have hfin := finite_sections_of_finitePresentation_sections G hfp
  exact ⟨isQuasicoherentOnSite_fittingIdeal G hcart hfin r,
    isFiniteTypeOnSite_fittingIdeal G hcart hfp r⟩

/-- For a finitely presented quasi-coherent `𝒪_X`-module `ℱ` on an algebraic space `X`, the `r`-th
Fitting ideal `Fit_r(ℱ)` is a quasi-coherent ideal of finite type. -/
@[stacks 0CZ5]
theorem isFiniteTypeQuasicoherentIdeal_fittingIdeal_of_isFinitePresentationOnSite
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite G) (r : ℕ) :
    IsFiniteTypeQuasicoherentIdeal B S hS X (fittingIdeal B S hS X.1 X.2 G r) :=
  isFiniteTypeQuasicoherentIdeal_fittingIdeal X G hG
    (module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hfp) r

end AlgebraicGeometry.Space

end
