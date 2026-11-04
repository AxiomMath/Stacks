module

public import StacksFrontier.AlgebraicGeometry.RelativeSegre.Compat
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjGeneral.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification

/-!
# Restricting an affine piece to a smaller affine open

Let `H` and `G` be quasi-coherent modules on a scheme `X`, `W ⊆ U` affine opens of `X`, and `a`,
`b` degree-one elements of `Γ(U, Sym H)` and `Γ(U, Sym G)`. Restricting `a` and `b` to `W` gives
the piece `D₊(a|_W) ×_W D₊(b|_W)`, which is the part of `D₊(a) ×_U D₊(b)` over `W`. This file
shows that on it the Segre morphism of the restricted piece is the Segre morphism of the original
one: the chart of `𝐏(H ⊗ G)` over `W` is the chart over `U` precomposed with the morphism of
projective spectra induced by restriction of sections, and the two Segre ring maps correspond
under restriction.

## Main results

* `Stacks.RelativeSegre.deg1_res`: degree-one elements of sections restrict to degree-one elements
  of the restricted sections.
* `Stacks.RelativeSegre.chartι_res`: the standard chart of `a|_W` is the standard chart of `a`
  precomposed with the induced map of spectra.
* `Stacks.RelativeSegre.pieceSegre_compat_res`: **the Segre morphisms of a piece and of its
  restriction agree.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped TensorProduct

universe u

namespace Stacks.RelativeSegre

variable {X : Scheme.{u}}

section Restriction

variable (E : X.Modules) [E.IsQuasicoherent] {U W : X.Opens} (hU : IsAffineOpen U)
  (hW : IsAffineOpen W) (hWU : W ≤ U)

/-- The degree-one element of a section is the image of the sheafification unit in degree one. -/
theorem deg1_eq_of (m : Γ(E, U)) :
    deg1 E hU m = DirectSum.of ((alg E).sectionPieces U) 1
      (Stacks.SymTwistChart.symOne E (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
        m) := by
  rw [deg1, ← Stacks.SymTwistChart.symSectionRingEquiv_of_symOne E _ hU m,
    RingEquiv.symm_apply_apply]

/-- **Degree-one elements restrict to degree-one elements.** -/
theorem deg1_res (m : Γ(E, U)) :
    (alg E).res hWU (deg1 E hU m) = deg1 E hW (E.presheaf.map (homOfLE hWU).op m) := by
  refine ((congrArg ((alg E).res hWU) (deg1_eq_of E hU m)).trans ?_).trans
    (deg1_eq_of E hW _).symm
  refine ((alg E).resRingHom_of hWU _).trans ?_
  exact congrArg (DirectSum.of ((alg E).sectionPieces W) 1)
    (Stacks.SymTwistChart.resPiece_symOne E _ hWU m : _)

/-- The restriction of a degree-one element. -/
abbrev resDeg1 (a : (alg E).grading U 1) : (alg E).grading W 1 :=
  ⟨(alg E).res hWU a, ((alg E).res hWU).map_mem a.2⟩

include hU hW in
/-- Restriction of sections satisfies the hypothesis of `AlgebraicGeometry.Proj.map`. -/
theorem irrelevant_le_map_res :
    HomogeneousIdeal.irrelevant ((alg E).grading W) ≤
      (HomogeneousIdeal.irrelevant ((alg E).grading U)).map ((alg E).res hWU) :=
  Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
    (alg E).toGradedAlgebra (U := ⟨W, hW⟩) (V := ⟨U, hU⟩) hWU

/-- The transition morphism between the charts of `𝐏(E)` over `W ⊆ U` is the morphism of
projective spectra induced by restriction of sections. -/
theorem projInclusionMap_eq_map :
    Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap (alg E) W U hWU hW hU =
      Proj.map ((alg E).res hWU) (irrelevant_le_map_res E hU hW hWU) :=
  (alg E).toGradedAlgebra.transition_eq_map (U := ⟨W, hW⟩) (V := ⟨U, hU⟩) hWU _ _

/-- The chart of `𝐏(E)` over `W` is the chart over `U` precomposed with the morphism of
projective spectra induced by restriction. -/
theorem chart_res :
    (bun E).chart W hW =
      Proj.map ((alg E).res hWU) (irrelevant_le_map_res E hU hW hWU) ≫
        (bun E).chart U hU := by
  rw [← projInclusionMap_eq_map E hU hW hWU]
  exact ((bun E).chart_transition W U hWU hW hU).symm

/-- **The standard chart of `a|_W` is the standard chart of `a` precomposed with the induced map
of spectra.** -/
theorem chartι_res (a : (alg E).grading U 1) :
    chartι E hW (resDeg1 E hWU a) =
      Spec.map (CommRingCat.ofHom (Away.map ((alg E).res hWU) (a : (alg E).sectionRing U))) ≫
        chartι E hU a := by
  have h1 := Proj.awayι_comp_map ((alg E).res hWU) (irrelevant_le_map_res E hU hW hWU)
    Nat.one_pos (a : (alg E).sectionRing U) a.2
  have h2 := chart_res E hU hW hWU
  rw [chartι, chartι, h2, ← Category.assoc, h1, Category.assoc]

/-- The ratio `h / a` restricts to the ratio `h|_W / a|_W`. -/
theorem map_ratioOf (a : (alg E).grading U 1) (h : Γ(E, U)) :
    Away.map ((alg E).res hWU) (a : (alg E).sectionRing U) (ratioOf E hU a h) =
      ratioOf E hW (resDeg1 E hWU a) (E.presheaf.map (homOfLE hWU).op h) := by
  unfold ratioOf ratio deg1'
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  congr 1
  exact deg1_res E hU hW hWU h

/-- **A ring map out of `Γ(U, Sym E)` is determined by its values on the structure map and on the
degree-one elements of sections.** -/
theorem ringHom_ext_sectionRing {S : Type*} [Semiring S] {f f' : (alg E).sectionRing U →+* S}
    (h0 : ∀ r : Γ(X, U), f ((alg E).strHom U r) = f' ((alg E).strHom U r))
    (h1 : ∀ m : Γ(E, U), f (deg1 E hU m) = f' (deg1 E hU m)) : f = f' := by
  set e := Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hU
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
  have key : f.comp e.symm.toRingHom = f'.comp e.symm.toRingHom := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => h1 m)
    have := Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap E
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) hU r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [this, h0]
  refine RingHom.ext fun x => ?_
  have := RingHom.congr_fun key (e x)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] using this

/-- The restriction map of degree-zero localizations carries the structure map over `U` to the
structure map over `W`. -/
theorem map_fromZero_strZero (a : (alg E).grading U 1) (r : Γ(X, U)) :
    Away.map ((alg E).res hWU) (a : (alg E).sectionRing U)
        (fromZeroRingHom ((alg E).grading U) _
          (Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg E) U r)) =
      fromZeroRingHom ((alg E).grading W) _
        (Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg E) W
          (X.presheaf.map (homOfLE hWU).op r)) := by
  apply HomogeneousLocalization.val_injective
  show (HomogeneousLocalization.mk _).val = (HomogeneousLocalization.mk _).val
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  refine congrArg₂ Localization.mk ?_ (Subtype.ext ?_)
  · show (alg E).res hWU ((Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf (alg E) U
        r : (alg E).grading U 0) : (alg E).sectionRing U) = _
    rw [Stacks.AlgebraicGeometry.ProjBundleSurjection.coe_strZeroSheaf_apply,
      Stacks.AlgebraicGeometry.ProjBundleSurjection.coe_strZeroSheaf_apply]
    exact (alg E).resRingHom_strHom hWU r
  · exact map_one ((alg E).res hWU)

end Restriction

/-! ### The Segre morphism of a restricted piece -/

section RestrictionSegre

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent] {U W : X.Opens}
  (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)

/-- **The Segre morphisms of a piece and of its restriction to a smaller affine open agree.** -/
theorem pieceSegre_compat_res (a : (alg H).grading U 1) (b : (alg G).grading U 1)
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of (pieceRing H G a b)))
    (s' : T ⟶ Spec (CommRingCat.of
      (pieceRing H G (resDeg1 H hWU a) (resDeg1 G hWU b))))
    (hs : s ≫ pieceMap H G hU a b =
      s' ≫ pieceMap H G hW (resDeg1 H hWU a) (resDeg1 G hWU b)) :
    s ≫ pieceSegre H G hU a b =
      s' ≫ pieceSegre H G hW (resDeg1 H hWU a) (resDeg1 G hWU b) := by
  have hL : s ≫ prL H G a b = (s' ≫ prL H G (resDeg1 H hWU a) (resDeg1 G hWU b)) ≫
      Spec.map (CommRingCat.ofHom (Away.map ((alg H).res hWU) (a : (alg H).sectionRing U))) := by
    have h := congrArg (· ≫ pullback.fst (bun H).toBase (bun G).toBase) hs
    simp only [Category.assoc, pieceMap_fst] at h
    rw [chartι_res H hU hW hWU] at h
    rw [← cancel_mono (chartι H hU a)]
    simpa only [Category.assoc] using h
  have hR : s ≫ prR H G a b = (s' ≫ prR H G (resDeg1 H hWU a) (resDeg1 G hWU b)) ≫
      Spec.map (CommRingCat.ofHom (Away.map ((alg G).res hWU) (b : (alg G).sectionRing U))) := by
    have h := congrArg (· ≫ pullback.snd (bun H).toBase (bun G).toBase) hs
    simp only [Category.assoc, pieceMap_snd] at h
    rw [chartι_res G hU hW hWU] at h
    rw [← cancel_mono (chartι G hU b)]
    simpa only [Category.assoc] using h
  rw [pieceSegre, pieceSegre, chart_res (tens H G) hU hW hWU, ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [comp_fromOfGlobalSections_segre, Category.assoc, ← Category.assoc s',
    comp_fromOfGlobalSections_segre, Proj.fromOfGlobalSections_comp_map _ _ _ _ (by
      rw [← Ideal.map_map]
      refine eq_top_iff.mpr ((map_irrelevant_fn_segre H G hW _ _ s').symm.le.trans
        (Ideal.map_mono ?_))
      exact irrelevant_le_map_res (tens H G) hU hW hWU)]
  refine Proj.fromOfGlobalSections_congr (ringHom_ext_sectionRing (tens H G) hU
    (fun r => ?_) (fun m => ?_)) _ _
  · simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom, segreRingHom_strHom]
    rw [show (alg (tens H G)).res hWU ((alg (tens H G)).strHom U r) =
      (alg (tens H G)).strHom W (X.presheaf.map (homOfLE hWU).op r) from
        (alg (tens H G)).resRingHom_strHom hWU r, segreRingHom_strHom, fn_algebraMap,
      fn_algebraMap, hL, fn_comp_SpecMap]
    exact congrArg (fn _) (map_fromZero_strZero H hWU a r)
  · obtain ⟨t, rfl⟩ := (Stacks.SectionTensorFormula.tensorSectionEquiv H G hU).surjective m
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, deg1]
    | tmul h g =>
      rw [Stacks.SectionTensorFormula.tensorSectionEquiv_tmul]
      simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom, segreRingHom_deg1,
        segreLin_tensorSection]
      rw [show (alg (tens H G)).res hWU (deg1 (tens H G) hU
          (Stacks.SectionTensorFormula.tensorSection H G h g)) =
        deg1 (tens H G) hW (Stacks.SectionTensorFormula.tensorSection H G
          (H.presheaf.map (homOfLE hWU).op h) (G.presheaf.map (homOfLE hWU).op g)) by
          rw [deg1_res (tens H G) hU hW hWU,
            Stacks.SectionTensorFormula.map_tensorSection H G (homOfLE hWU)],
        segreRingHom_deg1, segreLin_tensorSection, fn_tmul, fn_tmul, hL, hR,
        fn_comp_SpecMap (s' ≫ prL H G (resDeg1 H hWU a) (resDeg1 G hWU b)),
        fn_comp_SpecMap (s' ≫ prR H G (resDeg1 H hWU a) (resDeg1 G hWU b))]
      exact congrArg₂ (· * ·) (congrArg (fn _) (map_ratioOf H hU hW hWU a h))
        (congrArg (fn _) (map_ratioOf G hU hW hWU b g))
    | add t₁ t₂ ih₁ ih₂ =>
      rw [map_add, deg1_add, map_add, map_add, ih₁, ih₂]

end RestrictionSegre

end Stacks.RelativeSegre

end
