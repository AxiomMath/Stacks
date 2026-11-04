module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartAgree
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue

/-!
# Glueing the twisted classes of the charts

Let `i : Z ⟶ X` be a closed immersion such that every point of `Z` lies in a chart of `i` by `c`
generators of its ideal.  The twisted classes of the charts agree on overlaps
(`Stacks.Perfect.ConormalClass.chartSec_agree`), and over the complement of `Z` the source
`i_*(ℒ^∨ ⊗ i^*ℱ)` has no nonzero sections, so they glue to a morphism

`i_*(⋀^c(𝒞_{Z/X})^∨ ⊗_{𝒪_Z} i^*ℱ) ⟶ ℋ^c_Z(ℱ)`,

natural in `ℱ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.SupportedFraction (supportCohomologySheaf supportCohomologySheafMap
  supportCohomologySheafFunctor)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] modulesMonoidal

variable {X : Scheme.{u}}

/-- The change of support is natural in the coefficient module. -/
theorem supportChangeH_natural {T T' : Set X} (hT : IsClosed T) (hT' : IsClosed T')
    (hTT' : T ⊆ T') {F G : X.Modules} (φ : F ⟶ G) (p : ℤ) :
    supportChangeH hT hT' hTT' F p ≫ supportCohomologySheafMap hT' φ p =
      supportCohomologySheafMap hT φ p ≫ supportChangeH hT hT' hTT' G p := by
  unfold supportChangeH supportCohomologySheafMap
  exact ((DerivedCategory.homologyFunctor X.Modules p).map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.homologyFunctor X.Modules p).map
      ((supportChange X.toRingedSpace hT hT' hTT').naturality
        ((DerivedCategory.singleFunctor X.Modules 0).map φ)).symm).trans
      ((DerivedCategory.homologyFunctor X.Modules p).map_comp _ _))

/-- A module on a scheme has no nonzero sections over the empty open. -/
theorem subsingleton_sections_bot {Y : Scheme.{u}} (N : Y.Modules) : Subsingleton Γ(N, ⊥) :=
  ⟨fun a b =>
    TopCat.Sheaf.eq_of_locally_eq' (F := (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} Y))
      (fun _ : PEmpty.{u + 1} => (⊥ : Y.Opens)) ⊥ (fun e => e.elim) bot_le a b (fun e => e.elim)⟩

section Natural

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)

/-- **The functor `ℱ ↦ i_*(⋀^c(𝒞_{Z/X})^∨ ⊗_{𝒪_Z} i^*ℱ)`.** -/
def twistFunctor : X.Modules ⥤ X.Modules :=
  Scheme.Modules.pullback i ⋙ tensorLeft (dualModule (line i c)) ⋙ Scheme.Modules.pushforward i

/-- The functor `twistFunctor i c` sends `ℱ` to `twistSource i c ℱ`. -/
theorem twistFunctor_obj (F : X.Modules) : (twistFunctor i c).obj F = twistSource i c F := rfl

variable {i c} {F F' : X.Modules} (φ : F ⟶ F') {W : X.Opens} {f : Fin c → Γ(X, W)}
  (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)

/-- Evaluation at the wedge of the chart generators is natural in the coefficient module. -/
theorem chartEvalSec_natural (U : X.Opens) (hU : U ≤ W) (m : Γ(twistSource i c F, U)) :
    chartEvalSec F' hgen U hU (((twistFunctor i c).map φ).app U m) =
      ((Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ)).app U
        (chartEvalSec F hgen U hU m) := by
  set ψ := (Scheme.Modules.pullback i).map φ
  have e := congrArg (fun χ => χ.app (i ⁻¹ᵁ U) m)
    (evalAt_natural (line i c) ((Scheme.Modules.pullback i).obj F) (i ⁻¹ᵁ W) (chartWedge hgen) ψ)
  show ((Scheme.Modules.pullback i).obj F').presheaf.map
      (homOfLE (le_image_preimage (i.preimage_mono hU))).op
      ((evalAt (line i c) ((Scheme.Modules.pullback i).obj F') (i ⁻¹ᵁ W) (chartWedge hgen)).app
        (i ⁻¹ᵁ U) ((dualModule (line i c) ◁ ψ).app (i ⁻¹ᵁ U) m)) = _
  refine (congrArg _ e).trans ?_
  exact (hom_app_map ψ (le_image_preimage (i.preimage_mono hU)) _).symm

/-- The descent map of a chart is natural in the coefficient module. -/
theorem chartDescent_natural {T : Set X} (hT : IsClosed T)
    (hfT : chartSupport W (chartEq W f) ⊆ T) :
    chartDescent i W f F hgen hT hfT ≫
        (push W).map ((res W).map (supportCohomologySheafMap hT φ (c : ℤ))) =
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) ≫
        chartDescent i W f F' hgen hT hfT := by
  refine hom_ext_unit i F ?_
  rw [← Category.assoc, unit_comp_chartDescent, ← Category.assoc]
  have hη : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) =
      φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F' :=
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality φ).symm
  rw [hη, Category.assoc φ, unit_comp_chartDescent, ← Category.assoc φ, ← topClass_natural,
    Category.assoc]
  exact congrArg (fun χ => topClass W F hT (chartEq W f) hfT ≫ χ)
    ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality _).symm

/-- The descent of sections over a chart is natural in the coefficient module. -/
theorem chartDescSec_natural (U : X.Opens) (hU : U ≤ W) (y : Γ(quotPull i F, U)) :
    chartDescSec F' hgen U hU
        (((Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ)).app U y) =
      (supportCohomologySheafMap (isClosed_chartSupport W (chartEq W f)) φ (c : ℤ)).app U
        (chartDescSec F hgen U hU y) := by
  have e := congrArg (fun χ => χ.app U y)
    (chartDescent_natural φ hgen (isClosed_chartSupport W (chartEq W f)) subset_rfl)
  show (supportCohomologySheaf (isClosed_chartSupport W (chartEq W f)) F' (c : ℤ)).presheaf.map
      (homOfLE (le_image_preimage hU)).op ((chartDescent i W f F' hgen
        (isClosed_chartSupport W (chartEq W f)) subset_rfl).app U
          (((Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ)).app U y)) = _
  refine (congrArg _ e.symm).trans ?_
  exact (hom_app_map _ (le_image_preimage hU) _).symm

/-- The twisted class of a chart is natural in the coefficient module. -/
theorem chartSec_natural (U : X.Opens) (hU : U ≤ W) (m : Γ(twistSource i c F, U)) :
    chartSec F' hgen U hU (((twistFunctor i c).map φ).app U m) =
      (supportCohomologySheafMap (isClosed_zeroLocus i) φ (c : ℤ)).app U
        (chartSec F hgen U hU m) := by
  refine (chartSec_eq_iff F' hgen U hU _ _).2 ?_
  have e := congrArg (fun χ => χ.app U (chartSec F hgen U hU m))
    (supportChangeH_natural (isClosed_zeroLocus i) (isClosed_chartSupport W (chartEq W f))
      (zeroLocus_subset_chartSupport W f hgen) φ (c : ℤ))
  refine e.symm.trans ?_
  show (supportCohomologySheafMap _ φ (c : ℤ)).app U ((chartTheta F hgen).app U
    (chartSec F hgen U hU m)) = _
  rw [chartTheta_chartSec, chartEvalSec_natural, chartDescSec_natural]

end Natural

/-! ### The glueing -/

section Glue

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)

/-- **The charts of `i` by `c` generators of its ideal**: an open `W ⊆ X` with sections
`f₁, …, f_c` generating the ideal sheaf of `Z` over `W`. -/
def ChartIndex : Type u :=
  {p : Σ W : X.Opens, (Fin c → Γ(X, W)) //
    IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) p.1 p.2}

/-- The complement of `Z`. -/
def offZero : X.Opens := ⟨(zeroLocus i)ᶜ, (isClosed_zeroLocus i).isOpen_compl⟩

/-- The covering of `X` by the charts and the complement of `Z`. -/
def coverOpen : Option (ChartIndex i c) → X.Opens
  | none => offZero i
  | some a => a.1.1

variable (F : X.Modules)

/-- Over an open disjoint from `Z`, the module `twistSource i c ℱ` has no nonzero sections. -/
theorem subsingleton_twistSource {U : X.Opens} (hU : U ≤ offZero i) :
    Subsingleton Γ(twistSource i c F, U) := by
  have h : i ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun z hz => hU hz ⟨z, rfl⟩
  show Subsingleton Γ(dualModule (line i c) ⊗ (Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U)
  rw [h]
  exact subsingleton_sections_bot _

/-- The local maps of the glueing. -/
def coverSec : ∀ (a : Option (ChartIndex i c)) (U : X.Opens), U ≤ coverOpen i c a →
    Γ(twistSource i c F, U) → Γ(supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ), U)
  | none, _, _, _ => 0
  | some a, U, h, m => chartSec F a.2 U h m

/-- The twisted class of a chart sends zero to zero. -/
theorem chartSec_zero {W : X.Opens} {f : Fin c → Γ(X, W)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f) (U : X.Opens) (hU : U ≤ W) :
    chartSec F hgen U hU 0 = 0 := by
  have h := chartSec_add F hgen U hU 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-- Over an open disjoint from `Z`, every local map `coverSec` vanishes. -/
theorem coverSec_eq_zero_of_le_offZero (a : Option (ChartIndex i c)) {U : X.Opens}
    (h : U ≤ coverOpen i c a) (hU : U ≤ offZero i) (m : Γ(twistSource i c F, U)) :
    coverSec i c F a U h m = 0 := by
  have := subsingleton_twistSource i c F hU
  rcases a with _ | a
  · rfl
  · rw [Subsingleton.elim m 0]
    exact chartSec_zero i c F a.2 U h

variable (hcharts : ∀ x ∈ zeroLocus i, ∃ a : ChartIndex i c, x ∈ a.1.1)

/-- If every point of `Z` lies in a chart, the opens `coverOpen i c a` cover `X`. -/
private theorem exists_mem_coverOpen
    (hcharts : ∀ x ∈ zeroLocus i, ∃ a : ChartIndex i c, x ∈ a.1.1) (x : X) :
    ∃ a, x ∈ coverOpen i c a := by
  by_cases hx : x ∈ zeroLocus i
  · obtain ⟨a, ha⟩ := hcharts x hx
    exact ⟨some a, ha⟩
  · exact ⟨none, hx⟩

include hcharts in
/-- There is a morphism `twistSource i c ℱ ⟶ ℋ^c_Z(ℱ)` restricting to `coverSec` on each open of
the covering `coverOpen i c`. -/
theorem exists_twistMap :
    ∃ φ : twistSource i c F ⟶ supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ),
      ∀ (a : Option (ChartIndex i c)) (U : X.Opens) (h : U ≤ coverOpen i c a)
        (m : Γ(twistSource i c F, U)), φ.app U m = coverSec i c F a U h m := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover (coverOpen i c)
    (exists_mem_coverOpen i c hcharts) (coverSec i c F) ?_ ?_ ?_ ?_
  · rintro (_ | a) U h m m'
    · exact (add_zero 0).symm
    · exact chartSec_add F a.2 U h m m'
  · rintro (_ | a) U h r m
    · exact (smul_zero r).symm
    · exact chartSec_smul F a.2 U h r m
  · rintro (_ | a) U V hUV hV m
    · exact (map_zero _).symm
    · exact chartSec_restrict F a.2 hUV hV m
  · rintro (_ | a) (_ | b) U ha hb m
    · rfl
    · exact (coverSec_eq_zero_of_le_offZero i c F (some b) hb ha m).symm
    · exact coverSec_eq_zero_of_le_offZero i c F (some a) ha hb m
    · exact chartSec_agree F a.2 b.2 ha hb m

/-- **The glued twisted class**
`i_*(⋀^c(𝒞_{Z/X})^∨ ⊗_{𝒪_Z} i^*ℱ) ⟶ ℋ^c_Z(ℱ)`. -/
def twistMap : twistSource i c F ⟶ supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ) :=
  (exists_twistMap i c F hcharts).choose

/-- On each open of the covering `coverOpen i c`, `twistMap` is the local map `coverSec`. -/
theorem twistMap_app (a : Option (ChartIndex i c)) (U : X.Opens) (h : U ≤ coverOpen i c a)
    (m : Γ(twistSource i c F, U)) :
    (twistMap i c F hcharts).app U m = coverSec i c F a U h m :=
  (exists_twistMap i c F hcharts).choose_spec a U h m

/-- On a chart, the glued map is the twisted class of the chart. -/
theorem twistMap_app_chart {W : X.Opens} {f : Fin c → Γ(X, W)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f) (U : X.Opens) (hU : U ≤ W)
    (m : Γ(twistSource i c F, U)) :
    (twistMap i c F hcharts).app U m = chartSec F hgen U hU m :=
  twistMap_app i c F hcharts (some ⟨⟨W, f⟩, hgen⟩) U hU m

include hcharts in
/-- The opens `coverOpen i c a` cover `X`. -/
theorem coverOpen_covers : ∀ x : X, ∃ a, x ∈ coverOpen i c a :=
  exists_mem_coverOpen i c hcharts

/-- **The glued map is natural in the module.** -/
theorem twistMap_natural {F F' : X.Modules} (φ : F ⟶ F') :
    (twistFunctor i c).map φ ≫ twistMap i c F' hcharts =
      twistMap i c F hcharts ≫ supportCohomologySheafMap (isClosed_zeroLocus i) φ (c : ℤ) := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover (coverOpen i c)
    (coverOpen_covers i c hcharts) fun a U h => ?_
  ext m
  show (twistMap i c F' hcharts).app U (((twistFunctor i c).map φ).app U m) =
    (supportCohomologySheafMap (isClosed_zeroLocus i) φ (c : ℤ)).app U
      ((twistMap i c F hcharts).app U m)
  refine (twistMap_app i c F' hcharts a U h _).trans ?_
  refine Eq.trans ?_ (congrArg _ (twistMap_app i c F hcharts a U h m)).symm
  rcases a with _ | a
  · exact (map_zero _).symm
  · exact chartSec_natural φ a.2 U h m

end Glue

end Stacks.Perfect.ConormalClass
