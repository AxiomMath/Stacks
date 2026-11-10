module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChangeOfU

/-!
# Two ingredients of shrinking the affine open of a chart datum

Let `U' ≤ U` be affine opens of the base, `r : Proj 𝒜(U') ⟶ Proj 𝒜(U)` the transition of the
charts, and `g : T ⟶ Proj 𝒜(U)`, `g' : T ⟶ Proj 𝒜(U')` with `g' ≫ r = g`.

* `moduleSheafPullbackChartIso_restrict`: the identification `h^*ℳ̃ ≅ g'^*ℳ̃(U')` is the
  identification `h^*ℳ̃ ≅ g^*ℳ̃(U)` followed by `g'^*` of the comparison `r^*ℳ̃(U) ⟶ ℳ̃(U')` of the
  chart sheaves.
* `kappaSec_restrict`, `kappa_restrict`: the functions `g^♯(a / c^i)` and the morphisms
  `κ_i : f^*𝒜_{id} ⟶ 𝒪_T` are unchanged when `U`, `c`, `g` are replaced by `U'`, `c|_{U'}`, `g'`.
* `hCP_restrict`: the chart identity `ψ(a) = g^♯(a / c^i) · w^i` over `U` gives the chart identity
  over `U'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

section ChartIso

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]
  {U U' : s.base.affineOpens} (hUU' : U'.1 ≤ U.1) {T : Scheme.{u}}
  {g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1)}
  {g' : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U'.1)}
  (hgg : g' ≫ projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 = g)

/-- **The identification `h^*ℳ̃ ≅ g'^*ℳ̃(U')` through the smaller chart** is the identification
through the larger chart followed by the comparison of the chart sheaves along the transition. -/
theorem moduleSheafPullbackChartIso_restrict {h : T ⟶ relativeProj s}
    (fac : h = g ≫ relativeProjChart s U) (fac' : h = g' ≫ relativeProjChart s U') :
    (moduleSheafPullbackChartIso ℳ U' g' fac').hom =
      (moduleSheafPullbackChartIso ℳ U g fac).hom ≫
        (Scheme.Modules.pullbackCongr hgg).inv.app (moduleChart ℳ U) ≫
        (Scheme.Modules.pullbackComp g' (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)).inv.app
          (moduleChart ℳ U) ≫
        (Scheme.Modules.pullback g').map
          (Stacks.ProjModuleComparison.moduleMap (gradedSectionRestriction s U'.1 U.1 hUU')
            (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
            (sectionModuleRestrictₛₗ ℳ hUU') (sectionModuleRestrictₛₗ_mem_grading ℳ hUU')) := by
  have hν := pullbackCongr_inv_comp_moduleMap ℳ (W := U') (W' := U) hUU'
  refine (Scheme.Modules.pullbackIsoOfRestrictIso_refine (relativeProjChart s U)
    (moduleSheafChartIso ℳ U) (projInclusionMap s U'.1 U.1 hUU' U'.2 U.2)
    (relativeProjChart_transition s (W := U') (W' := U) hUU').symm (moduleSheafChartIso ℳ U')
    _ ?_ g' hgg fac fac').symm
  simp only [Scheme.Modules.pullbackIsoOfRestrictIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  exact hν
end ChartIso

section Kappa

variable {s : Stacks.RelativeProj.Situation.{u}}
  {U U' : s.base.affineOpens} (hUU' : U'.1 ≤ U.1) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}}
  {g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1)}
  {g' : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U'.1)}

/-- The function `g'^♯(n / y^i)` on `T` depends only on the values of `y` and `n`. -/
private theorem appLE_awayMk_congr {y y' : s.sectionRing U'.1} (ey : y = y')
    {n n' : s.sectionRing U'.1} (en : n = n') (hy : y ∈ s.sectionRingGrading U'.1 d)
    (hy' : y' ∈ s.sectionRingGrading U'.1 d) (i : ℕ)
    (hn : n ∈ s.sectionRingGrading U'.1 (i • d)) (hn' : n' ∈ s.sectionRingGrading U'.1 (i • d))
    (h₁ : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1) y)
    (h₂ : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1) y') :
    g'.appLE _ ⊤ h₁ (Proj.awayToSection _ y
        (HomogeneousLocalization.Away.mk (s.sectionRingGrading U'.1) hy i n hn)) =
      g'.appLE _ ⊤ h₂ (Proj.awayToSection _ y'
        (HomogeneousLocalization.Away.mk (s.sectionRingGrading U'.1) hy' i n' hn')) := by
  subst ey en
  rfl

/-- **The functions `g^♯(a / c^i)` are compatible with shrinking the affine open**: for
`g' ≫ r = g`, the function `g'^♯(a|_{U'} / c|_{U'}^i)` is `g^♯(a / c^i)`. -/
theorem kappaSec_restrict
    (hgg : g' ≫ projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 = g)
    (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
    (hg' : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1)
      (cHom U'.1 (resC hUU' c)))
    (i : ℕ) (a : s.sectionPieces U.1 (i * d)) :
    kappaSec U' (resC hUU' c) g' hg' i
        ((s.algebra.piece ((i * d : ℕ) : ℤ)).val.map (homOfLE hUU').op a) =
      kappaSec U c g hg i a := by
  subst hgg
  set φ := gradedSectionRestriction s U'.1 U.1 hUU'
  set r := Proj.map φ (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2)
  have hle : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1) (φ (cHom U.1 c)) :=
    hg
  have e1 : (g' ≫ r).appLE (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c)) ⊤ hg =
      r.appLE (Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
          (Proj.basicOpen (s.sectionRingGrading U'.1) (φ (cHom U.1 c))) le_rfl ≫
        g'.appLE _ ⊤ hle :=
    (Scheme.Hom.appLE_comp_appLE g' r _ _ _ le_rfl hle).symm
  have e2 := congrArg (fun ψ => ψ (algFrac U c i a))
    (congrArg CommRingCat.Hom.hom (Proj.awayToSection_comp_appLE φ
      (irrelevant_le_map_gradedSectionRestriction s U'.1 U.1 hUU' U'.2 U.2) (cHom_mem U.1 c)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at e2
  have e3 : kappaSec U c (g' ≫ r) hg i a = g'.appLE _ ⊤ hle
      (Proj.awayToSection (s.sectionRingGrading U'.1) (φ (cHom U.1 c))
        (HomogeneousLocalization.Away.mk (s.sectionRingGrading U'.1)
          (Graded.map_mem φ (cHom_mem U.1 c)) i (φ (DirectSum.of (s.sectionPieces U.1) (i * d) a))
          (Graded.map_mem φ ⟨a, rfl⟩))) := by
    change ((g' ≫ r).appLE _ ⊤ hg).hom (Proj.awayToSection _ _ (algFrac U c i a)) = _
    rw [e1, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    refine congrArg (g'.appLE _ ⊤ hle).hom (e2.trans ?_)
    exact congrArg _ (HomogeneousLocalization.Away.map_mk φ _ (cHom_mem U.1 c) i _ ⟨a, rfl⟩)
  exact (appLE_awayMk_congr (restrict_cHom hUU' c).symm
    (gradedSectionRestriction_of s U'.1 U.1 hUU' (i * d) a).symm _ _ i _ _ hg' _).trans e3.symm

end Kappa

section ChartIdentity

variable {s : Stacks.RelativeProj.Situation.{u}}
  {U U' : s.base.affineOpens} (hUU' : U'.1 ≤ U.1) {d : ℕ} (c : s.sectionPieces U.1 d)
  {T : Scheme.{u}} (f : T ⟶ s.base) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U.1)
  (hf' : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U'.1)
  {g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U.1)}
  {g' : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading U'.1)}
  (hgg : g' ≫ projInclusionMap s U'.1 U.1 hUU' U'.2 U.2 = g)
  (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U.1) (cHom U.1 c))
  (hg' : (⊤ : T.Opens) ≤ g' ⁻¹ᵁ Proj.basicOpen (s.sectionRingGrading U'.1)
    (cHom U'.1 (resC hUU' c)))
  (hgf : ∀ r : s.base.ringCatSheaf.obj.obj (op U.1),
    f.appLE U.1 ⊤ hf r = g.appLE _ ⊤ hg (Proj.awayToSection _ _ (baseFrac U c r)))
  (hgf' : ∀ r : s.base.ringCatSheaf.obj.obj (op U'.1),
    f.appLE U'.1 ⊤ hf' r = g'.appLE _ ⊤ hg' (Proj.awayToSection _ _ (baseFrac U' (resC hUU' c) r)))

include hgg in
/-- **The morphisms `κ_i : f^*𝒜_{id} ⟶ 𝒪_T` do not change when the affine open shrinks.** -/
theorem kappa_restrict (i : ℕ) :
    kappa U' (resC hUU' c) f hf' g' hg' hgf' i = kappa U c f hf g hg hgf i := by
  refine AffineOpenHomRecovery.hom_ext f U.1 hf (s.algebra.piece ((i * d : ℕ) : ℤ)) U.2
    _ fun a => ?_
  have e := Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le f
    (s.algebra.piece ((i * d : ℕ) : ℤ)) hUU' ⊤ hf hf' a
  refine (congrArg _ e.symm).trans (Eq.trans ?_ (kappa_pullbackSection U c f hf g hg hgf i a).symm)
  exact (kappa_pullbackSection U' (resC hUU' c) f hf' g' hg' hgf' i _).trans
    (kappaSec_restrict hUU' c hgg hg hg' i a)

variable {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f s.algebra (d : ℤ) L) (w : (LaurentSections.Ring L (op ⊤))ˣ)

include hgg hgf hgf' in
/-- **The chart identity survives shrinking the affine open**: if `ψ(a) = g^♯(a / c^i) · w^i`
for the sections `a` of `𝒜_{id}` over `U`, then `ψ(a') = g'^♯(a' / c|_{U'}^i) · w^i` for the
sections `a'` over `U'`. -/
theorem hCP_restrict
    (hCP : ∀ (i : ℕ) (a : s.sectionPieces U.1 (i * d)),
      ((laurent L).piece i).val.map (homOfLE hf).op (ψ.sectionHom i (op U.1) a) =
        (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from kappaSec U c g hg i a) •
          LaurentSections.pw w i) :
    ∀ (i : ℕ) (a' : s.sectionPieces U'.1 (i * d)),
      ((laurent L).piece i).val.map (homOfLE hf').op (ψ.sectionHom i (op U'.1) a') =
        (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
          kappaSec U' (resC hUU' c) g' hg' i a') • LaurentSections.pw w i := by
  intro i a'
  have hψ := twisting_app_eq U c f hf g hg hgf ψ w hCP i
  rw [← kappa_restrict hUU' c f hf hf' hgg hg hg' hgf hgf' i] at hψ
  have e1 : (ψ.app i).val.app (op ⊤) (Scheme.Modules.pullbackSection f _ U'.1 ⊤ hf' a') =
      ((laurent L).piece i).val.map (homOfLE hf').op (ψ.sectionHom i (op U'.1) a') :=
    PresheafOfModules.naturality_apply (ψ.app i).val (homOfLE hf').op _
  have etop : ∀ x : ((laurent L).piece i).val.obj (op ⊤),
      ((laurent L).piece i).val.restrictₛₗ (LaurentSections.topRes T (op ⊤)) x = x := by
    intro x
    have h1 : LaurentSections.topRes T (op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    change ((laurent L).piece i).val.map (LaurentSections.topRes T (op ⊤)) x = x
    rw [h1, PresheafOfModules.map_id]
    rfl
  have e2 : (kappa U' (resC hUU' c) f hf' g' hg' hgf' i ≫
      LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U'.1 ⊤ hf' a') =
      (show (structureRingSheaf T.toRingedSpace).obj.obj (op ⊤) from
        kappaSec U' (resC hUU' c) g' hg' i a') • LaurentSections.pw w i := by
    change (LaurentSections.secHom ((laurent L).piece i) (LaurentSections.pw w i)).val.app (op ⊤)
      ((kappa U' (resC hUU' c) f hf' g' hg' hgf' i).val.app (op ⊤)
        (Scheme.Modules.pullbackSection f _ U'.1 ⊤ hf' a')) = _
    rw [kappa_pullbackSection]
    exact (LaurentSections.secHom_app _ _ _ _).trans (congrArg _ (etop _))
  rw [← e1, hψ]
  exact e2

end ChartIdentity

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
