module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartData
public import
  StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafDegreeZeroMap
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.BaseSectionDictionary

/-!
# The charts of a relative projective spectrum lie over the base, on sections

For an affine open `W` of the base and a section `c` of `𝒜_d` over `W`, `d ≥ 1`, the chart over
`W` followed by the structure morphism acts on a function `r` on `W` as the degree-zero fraction
`r / 1` over `D₊(c)`. Consequently a morphism `h` into the relative projective spectrum lying over
`f` and factoring as `g ≫ chart W` satisfies the base identity of a chart datum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

variable {s : Stacks.RelativeProj.Situation.{u}} (W : s.base.affineOpens) {d : ℕ}
  (c : s.sectionPieces W.1 d)

/-- The chart over `W` followed by the structure morphism maps all of `Proj` into `W`. -/
theorem le_preimage_chart_toBase :
    (⊤ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens) ≤
      (relativeProjChart s W ≫ relativeProjToBase s) ⁻¹ᵁ W.1 := by
  intro x _
  have hw := (relativeProjChart_isPullback s W).w
  change (relativeProjChart s W ≫ relativeProjToBase s).base x ∈ W.1
  rw [hw]
  exact ((projInclusionToOpen s W.1 W.2).base x).2

private alias appLE_congr_of_eq := Stacks.RelativeProj.Situation.appLE_eq_of_eq

/-- **The chart over `W` followed by the structure morphism, on sections over `D₊(c)`.** -/
theorem chart_toBase_appLE_hom (hd : 0 < d)
    (e : Proj.basicOpen (s.sectionRingGrading W.1) (cHom W.1 c) ≤
      (relativeProjChart s W ≫ relativeProjToBase s) ⁻¹ᵁ W.1) :
    (relativeProjChart s W ≫ relativeProjToBase s).appLE W.1 _ e =
      sectionRingZeroMap s W.1 ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (s.sectionRingGrading W.1)
          (Submonoid.powers (cHom W.1 c))) ≫ Proj.awayToSection _ _ := by
  rw [appLE_congr_of_eq (relativeProjChart_comp_relativeProjToBase s W)]
  have e1 : (⊤ : (Spec Γ(s.base, W.1)).Opens) ≤ W.2.fromSpec ⁻¹ᵁ W.1 :=
    W.2.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Spec (CommRingCat.of (s.sectionRingGrading W.1 0))).Opens) ≤
      (Spec.map (sectionRingZeroMap s W.1) ≫ W.2.fromSpec) ⁻¹ᵁ W.1 :=
    fun x _ => e1 (Set.mem_univ ((Spec.map (sectionRingZeroMap s W.1)).base x))
  rw [← Scheme.Hom.appLE_comp_appLE (Proj.toSpecZero (s.sectionRingGrading W.1))
    (Spec.map (sectionRingZeroMap s W.1) ≫ W.2.fromSpec) W.1 ⊤
    (Proj.basicOpen (s.sectionRingGrading W.1) (cHom W.1 c)) e2 le_top,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map (sectionRingZeroMap s W.1)) W.2.fromSpec W.1 ⊤ ⊤ e1
      le_top]
  have h1 := Stacks.BaseSectionDictionary.fromSpec_appLE_top W.2 e1
  have h3 := Stacks.BaseSectionDictionary.toSpecZero_appLE_basicOpen (s.sectionRingGrading W.1)
    (cHom_mem W.1 c) hd le_top
  have e3 : (Spec.map (sectionRingZeroMap s W.1)).appLE ⊤ ⊤ le_top =
      (Spec.map (sectionRingZeroMap s W.1)).appTop := by
    change (Spec.map (sectionRingZeroMap s W.1)).app ⊤ ≫ (Spec _).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of (s.sectionRingGrading W.1 0))).Opens) ≤
        _)).op = (Spec.map (sectionRingZeroMap s W.1)).app ⊤
    rw [show (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of (s.sectionRingGrading W.1 0))).Opens) ≤
        _)).op = 𝟙 _ from Subsingleton.elim _ _]
    exact (congrArg (Scheme.Hom.app (Spec.map (sectionRingZeroMap s W.1)) ⊤ ≫ ·)
      ((Spec (CommRingCat.of (s.sectionRingGrading W.1 0))).presheaf.map_id _)).trans
        (Category.comp_id _)
  have e4 := Scheme.ΓSpecIso_naturality (sectionRingZeroMap s W.1)
  have e5 : ((Scheme.ΓSpecIso Γ(s.base, W.1)).inv ≫ (Spec.map (sectionRingZeroMap s W.1)).appTop) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (s.sectionRingGrading W.1 0))).hom ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (s.sectionRingGrading W.1)
          (Submonoid.powers (cHom W.1 c))) ≫ Proj.awayToSection _ _ =
      sectionRingZeroMap s W.1 ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (s.sectionRingGrading W.1)
          (Submonoid.powers (cHom W.1 c))) ≫ Proj.awayToSection _ _ := by
    rw [Category.assoc, reassoc_of% e4, Iso.inv_hom_id_assoc]
  exact (congrArg₂ (· ≫ ·) (congrArg₂ (· ≫ ·) h1 e3) h3).trans e5

/-- The image of a function `r` on `W` in degree zero of the localization at `c` is the fraction
`baseFrac W c r`, that is `r / 1`. -/
theorem fromZero_sectionRingZeroMap (r : s.base.ringCatSheaf.obj.obj (op W.1)) :
    HomogeneousLocalization.fromZeroRingHom (s.sectionRingGrading W.1)
        (Submonoid.powers (cHom W.1 c)) (sectionRingZeroMap s W.1 r) = baseFrac W c r := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  change (Localization.mk ((sectionRingZeroMap s W.1 r : s.sectionRingGrading W.1 0) :
      s.sectionRing W.1) 1 : Localization.Away (cHom W.1 c)) = _
  have hmem := sectionRingBaseMap_mem_zero s W.1 r
  have e : ((sectionRingZeroMap s W.1 r : s.sectionRingGrading W.1 0) : s.sectionRing W.1) =
      s.sectionRingBaseMap W.1 r :=
    DirectSum.decompose_of_mem_same _ hmem
  rw [e]
  congr 1

/-- **The chart over `W` followed by the structure morphism, on a function**: `r ↦ r / 1`. -/
theorem chart_toBase_appLE (hd : 0 < d)
    (e : Proj.basicOpen (s.sectionRingGrading W.1) (cHom W.1 c) ≤
      (relativeProjChart s W ≫ relativeProjToBase s) ⁻¹ᵁ W.1)
    (r : s.base.ringCatSheaf.obj.obj (op W.1)) :
    (relativeProjChart s W ≫ relativeProjToBase s).appLE W.1 _ e r =
      Proj.awayToSection _ _ (baseFrac W c r) :=
  (congrArg (fun φ => φ r) (chart_toBase_appLE_hom W c hd e)).trans
    (congrArg (Proj.awayToSection _ _) (fromZero_sectionRingZeroMap W c r))

/-- **A morphism into `Proj_S(𝒜)` over `f`, factoring through the chart over `W`, satisfies the
base identity of a chart datum.** -/
theorem hgf_of_fac (hd : 0 < d) {T : Scheme.{u}} (f : T ⟶ s.base) {h : T ⟶ relativeProj s}
    (hπ : h ≫ relativeProjToBase s = f)
    (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1))
    (fac : h = g ≫ relativeProjChart s W) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ W.1)
    (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading W.1) (cHom W.1 c))
    (r : s.base.ringCatSheaf.obj.obj (op W.1)) :
    f.appLE W.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac W c r)) := by
  have hfg : f = g ≫ (relativeProjChart s W ≫ relativeProjToBase s) := by
    rw [← hπ, fac, Category.assoc]
  have e := (le_preimage_chart_toBase W).trans' (le_top :
    Proj.basicOpen (s.sectionRingGrading W.1) (cHom W.1 c) ≤ ⊤)
  refine (congrArg (fun φ => φ r) (appLE_congr_of_eq hfg W.1 ⊤ hf)).trans ?_
  refine (congrArg (fun φ => φ r) (Scheme.Hom.appLE_comp_appLE g
    (relativeProjChart s W ≫ relativeProjToBase s) W.1 _ ⊤ e hg).symm).trans ?_
  exact congrArg (g.appLE _ ⊤ hg) (chart_toBase_appLE W c hd e r)

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
