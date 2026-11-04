module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChartRegular
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Open
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.BaseSectionDictionary

/-!
# The structure map on the chart `D₊(T)` of the projective completion

Over an affine open `V` of `X`, with `R = Γ(X, V)` and `M = Γ(𝒞, V)`, the identification
`Γ(E, W) ≅ Sym_R(M)` of `Stacks.Chow.ProjectiveCompletion.coordRingEquiv` carries the pullback
`π^* : R ⟶ Γ(E, W)` of functions to the structure map `R ⟶ Sym_R(M)`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.coordRingEquiv_proj_app`: `π^*r ↦ r`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V : X.Opens}
  (hV : IsAffineOpen V)

/-- The structure map `Γ(X, V) ⟶ Γ(V, Sym^*(𝒞 ⊕ 𝒪_X))_0`. -/
def strZeroV : Γ(X, V) ⟶ CommRingCat.of ((symAlg 𝒞).grading V 0) :=
  (symAlg 𝒞).toGradedAlgebra.strZero ⟨V, hV⟩

/-- The degree-zero structure map `strZeroV`, viewed in `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X))`, is the structure
map `strHom`. -/
theorem coe_strZeroV (r : Γ(X, V)) :
    ((strZeroV 𝒞 hV r : (symAlg 𝒞).grading V 0) : (symAlg 𝒞).sectionRing V) =
      (symAlg 𝒞).strHom V r :=
  Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.coe_strZero_apply
    (symAlg 𝒞).toGradedAlgebra ⟨V, hV⟩ r

/-- The chart over `V` followed by the projection is the structure morphism of the chart. -/
theorem chart_comp_proj :
    chart 𝒞 V hV ≫ proj 𝒞 =
      AlgebraicGeometry.Proj.toSpecZero ((symAlg 𝒞).grading V) ≫
        Spec.map (strZeroV 𝒞 hV) ≫ hV.fromSpec :=
  Stacks.AlgebraicGeometry.RelativeProjMapDomain.chart_comp_toBase (symAlg 𝒞) V hV

/-- The degree-zero structure map lands, under `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X)) ≅ Sym_R(M × R)`, on the
scalars. -/
theorem chartRingHom_strHom (r : Γ(X, V)) :
    chartRingHom 𝒞 hV ((symAlg 𝒞).strHom V r) =
      algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) (Γ(𝒞, V) × Γ(X, V))) r := by
  have h1 : AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))
      ((symAlg 𝒞).strHom V r) = algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(module 𝒞, V)) r := by
    let := AffinePieces.sectionAlgebra (module 𝒞) (bundlePieces (module 𝒞)) (V := V)
    have h := (AffinePieces.symSectionAlgEquiv (module 𝒞) hV (bundlePieces (module 𝒞))).commutes r
    rw [AffinePieces.algebraMap_sectionRingAlgebra] at h
    exact h
  show SymPow.symAlgMap (sectionsSplit 𝒞 V).toLinearMap
    (AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))
      ((symAlg 𝒞).strHom V r)) = _
  rw [h1]
  exact AlgHom.commutes _ r

/-- **The fraction `r / 1` of a scalar corresponds to the scalar `r` of `Sym_R(M)`.** -/
theorem chartAwayEquiv_fromZeroRingHom (r : Γ(X, V)) :
    chartAwayEquiv 𝒞 hV (HomogeneousLocalization.fromZeroRingHom ((symAlg 𝒞).grading V)
        (Submonoid.powers ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V))
        (strZeroV 𝒞 hV r)) =
      algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(𝒞, V)) r := by
  have h : chartAwayHom 𝒞 hV (HomogeneousLocalization.fromZeroRingHom ((symAlg 𝒞).grading V)
      (Submonoid.powers ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V))
      (strZeroV 𝒞 hV r)) =
        algebraMap Γ(X, V) (Stacks.SymAdjoinChart.prodChartRing Γ(X, V) Γ(𝒞, V)) r := by
    refine HomogeneousLocalization.val_injective _ ?_
    rw [Stacks.SymAdjoinChart.val_algebraMap_prodChartRing, ← chartRingHom_strHom 𝒞 hV r]
    show HomogeneousLocalization.val (HomogeneousLocalization.map (chartGradedHom 𝒞 hV) _
      (HomogeneousLocalization.mk ⟨0, ⟨_, (strZeroV 𝒞 hV r).2⟩,
        ⟨1, SetLike.GradedOne.one_mem⟩, Submonoid.one_mem _⟩)) = _
    rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
    rw [← Localization.mk_one_eq_algebraMap]
    congr 1
    · exact congrArg (chartRingHom 𝒞 hV) (coe_strZeroV 𝒞 hV r)
    · exact Subtype.ext (map_one (chartGradedHom 𝒞 hV))
  rw [chartAwayEquiv, RingEquiv.trans_apply, RingEquiv.ofRingHom_apply, h]
  exact AlgEquiv.commutes _ r

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- Equal morphisms of schemes have equal maps `appLE` on sections. -/
theorem appLE_congr_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h
  rfl

/-- **The chart over `V` followed by the projection, on sections over `D₊(T)`**: a function `r`
on `V` goes to `r / 1`. -/
theorem chart_comp_proj_appLE
    (e : chartD 𝒞 (V := V) ≤ (chart 𝒞 V hV ≫ proj 𝒞) ⁻¹ᵁ V) :
    (chart 𝒞 V hV ≫ proj 𝒞).appLE V _ e =
      strZeroV 𝒞 hV ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom ((symAlg 𝒞).grading V)
          (Submonoid.powers ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) :
            (symAlg 𝒞).sectionRing V))) ≫ AlgebraicGeometry.Proj.awayToSection _ _ := by
  rw [appLE_congr_of_eq (chart_comp_proj 𝒞 hV)]
  have e1 : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have e2 : (⊤ : (Spec (CommRingCat.of ((symAlg 𝒞).grading V 0))).Opens) ≤
      (Spec.map (strZeroV 𝒞 hV) ≫ hV.fromSpec) ⁻¹ᵁ V :=
    fun x _ => e1 (Set.mem_univ ((Spec.map (strZeroV 𝒞 hV)).base x))
  rw [← Scheme.Hom.appLE_comp_appLE (AlgebraicGeometry.Proj.toSpecZero ((symAlg 𝒞).grading V))
    (Spec.map (strZeroV 𝒞 hV) ≫ hV.fromSpec) V ⊤
    (chartD 𝒞 (V := V)) e2 le_top,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map (strZeroV 𝒞 hV))
      hV.fromSpec V ⊤ ⊤ e1 le_top]
  have h1 := Stacks.BaseSectionDictionary.fromSpec_appLE_top hV e1
  have h3 := Stacks.BaseSectionDictionary.toSpecZero_appLE_basicOpen ((symAlg 𝒞).grading V)
    (chartT 𝒞 V).2 one_pos le_top
  have e3 : (Spec.map (strZeroV 𝒞 hV)).appLE ⊤ ⊤ le_top =
      (Spec.map (strZeroV 𝒞 hV)).appTop := by
    show (Spec.map (strZeroV 𝒞 hV)).app ⊤ ≫ (Spec _).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of ((symAlg 𝒞).grading V 0))).Opens) ≤
        _)).op = (Spec.map (strZeroV 𝒞 hV)).app ⊤
    rw [show (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of ((symAlg 𝒞).grading V 0))).Opens) ≤
        _)).op = 𝟙 _ from Subsingleton.elim _ _]
    exact (congrArg (Scheme.Hom.app (Spec.map (strZeroV 𝒞 hV)) ⊤ ≫ ·)
      ((Spec (CommRingCat.of ((symAlg 𝒞).grading V 0))).presheaf.map_id _)).trans
        (Category.comp_id _)
  have e4 := Scheme.ΓSpecIso_naturality (strZeroV 𝒞 hV)
  have e5 : ∀ {A : CommRingCat.{u}} (φ : CommRingCat.of ((symAlg 𝒞).grading V 0) ⟶ A),
      ((Scheme.ΓSpecIso Γ(X, V)).inv ≫ (Spec.map (strZeroV 𝒞 hV)).appTop) ≫
        (Scheme.ΓSpecIso (CommRingCat.of ((symAlg 𝒞).grading V 0))).hom ≫ φ =
      strZeroV 𝒞 hV ≫ φ := fun φ => by
    rw [Category.assoc, reassoc_of% e4, Iso.inv_hom_id_assoc]
  exact (congrArg₂ (· ≫ ·) (congrArg₂ (· ≫ ·) h1 e3) h3).trans (e5 _)

/-- **The pullback of a function on `V` to `W`, read in `Sym_R(M)`, is the scalar.** -/
theorem coordRingEquiv_proj_app (r : Γ(X, V)) :
    coordRingEquiv 𝒞 hV ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op
        ((proj 𝒞).app V r)) =
      algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(𝒞, V)) r := by
  have e : chartD 𝒞 (V := V) ≤ (chart 𝒞 V hV ≫ proj 𝒞) ⁻¹ᵁ V := fun x hx =>
    openW_le 𝒞 hV ((Scheme.Hom.apply_mem_image_iff _).2 hx)
  have hM : ((chart 𝒞 V hV).appIso (chartD 𝒞 (V := V))).hom
      ((space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ((proj 𝒞).app V r)) =
        (chart 𝒞 V hV ≫ proj 𝒞).appLE V _ e r := by
    have key : (space 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op ≫
        (chart 𝒞 V hV).appLE (chart 𝒞 V hV ''ᵁ chartD 𝒞 (V := V)) (chartD 𝒞 (V := V))
          (Scheme.Hom.preimage_image_eq _ _).ge =
        (chart 𝒞 V hV).appLE (proj 𝒞 ⁻¹ᵁ V) (chartD 𝒞 (V := V)) e :=
      Scheme.Hom.map_appLE _ _ _
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.comp_appLE]
    exact congrArg (fun φ => φ ((proj 𝒞).app V r)) key
  have hA : (AlgebraicGeometry.Proj.basicOpenIsoAway ((symAlg 𝒞).grading V)
      ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V)
      (chartT 𝒞 V).2 one_pos).inv ((chart 𝒞 V hV ≫ proj 𝒞).appLE V _ e r) =
        HomogeneousLocalization.fromZeroRingHom ((symAlg 𝒞).grading V)
          (Submonoid.powers ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V))
          (strZeroV 𝒞 hV r) := by
    rw [chart_comp_proj_appLE 𝒞 hV e]
    exact Iso.hom_inv_id_apply (AlgebraicGeometry.Proj.basicOpenIsoAway _ _ (chartT 𝒞 V).2
      one_pos) _
  show chartAwayEquiv 𝒞 hV ((AlgebraicGeometry.Proj.basicOpenIsoAway _ _ (chartT 𝒞 V).2
    one_pos).inv (((chart 𝒞 V hV).appIso (chartD 𝒞 (V := V))).hom _)) = _
  rw [hM, hA]
  exact chartAwayEquiv_fromZeroRingHom 𝒞 hV r

end Stacks.Chow.ProjectiveCompletion
