module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTensorFormsAmbient
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FMapGlobalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsComparison

/-!
# [Stacks, Tag 07IZ] is natural in the object of `Cris(X/S)`

Fix a global crystalline situation of [Stacks, Tag 07MF] and a morphism `g : B ⟶ A` of the small
crystalline site, with ambient morphism `g : T_B ⟶ T_A`.  The comparison
`Ω_{X/S}(A|_W) ⟶ Γ(W, Ω_{T_A/S,δ})` of [Stacks, Tag 07IZ] carries the transition map of
`Ω_{X/S}` along `g` to the map `dg : Ω_{T_A/S,δ} ⟶ g_* Ω_{T_B/S,δ}` of
`Crystalline.GlobalCrystallineSituation.dpDifferentialsMapSheaf`.

## Main results

* `...SmallSite.restrictedToSheaf_crysDifferentials_map` — the comparison commutes with `g`.

## References

* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A B : CrystallineThickening S} (g : B ⟶ A)
  (W : A.obj.thickening.target.scheme.Opens)

/-- **The ring map of the restriction of `g` over `W` is the comorphism of `g` over `W`**, read
through `Crystalline.openTopRes`. -/
theorem appTop_restrictOpenMap_openTopRes (r : Γ(A.obj.thickening.target.scheme, W)) :
    ((CrystallineThickening.restrictOpenMap g W).hom.targetHom.hom.appTop).hom
        ((openTopRes W).hom r) =
      (openTopRes (g.hom.targetHom.hom ⁻¹ᵁ W)).hom ((g.hom.targetHom.hom.app W).hom r) := by
  rw [← topIso_inv_eq_openTopRes, ← topIso_inv_eq_openTopRes]
  exact (congrArg (fun k ↦ (Scheme.Hom.appTop k).hom (W.topIso.inv.hom r))
    (Thickening.restrictOpenMap_targetHom g.hom W)).trans
    (morphismRestrict_appTop_topIso_apply g.hom.targetHom.hom W r)

/-- **The ring map of the restriction of `g` over `W` is the comorphism of `g` over `W`**, read
through `Crystalline.openTopResInv`. -/
theorem openTopResInv_appTop_restrictOpenMap
    (c : Γ((A.restrictOpen W).obj.thickening.target.scheme, ⊤)) :
    (openTopResInv (g.hom.targetHom.hom ⁻¹ᵁ W)).hom
        (((CrystallineThickening.restrictOpenMap g W).hom.targetHom.hom.appTop).hom c) =
      (g.hom.targetHom.hom.app W).hom ((openTopResInv W).hom c) := by
  have h := appTop_restrictOpenMap_openTopRes g W ((openTopResInv W).hom c)
  have e : (openTopRes W).hom ((openTopResInv W).hom c) = c := openTopRes_openTopResInv_apply W c
  rw [e] at h
  rw [h]
  exact openTopResInv_openTopRes_apply _ _

/-- **[Stacks, Tag 07IZ] is natural**: the comparison `Ω_{X/S}(A|_W) ⟶ Γ(W, Ω_{T_A/S,δ})` carries
the transition map of `Ω_{X/S}` along `g` to `dg`. -/
theorem restrictedToSheaf_crysDifferentials_map
    (ω : (crysDifferentials S).obj (op (A.restrictOpen W))) :
    ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ W))).hom
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op ω) =
      (dpDifferentialsMapSheaf g.hom).app W (((restrictedToSheaf A.obj).app (op W)).hom ω) := by
  have hspan := dpConstDifferentials_span
    (crysBaseAppLE S (A.restrictOpen W).obj) (crysDividedPowers S (A.restrictOpen W).obj)
    (crysBaseSections S (A.restrictOpen W).obj)
  refine Submodule.span_induction
    (p := fun (ω : crysDifferentialsObj S (A.restrictOpen W).obj) _ ↦
      ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ W))).hom
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op
          (show (crysDifferentials S).obj (op (A.restrictOpen W)) from ω)) =
      (dpDifferentialsMapSheaf g.hom).app W (((restrictedToSheaf A.obj).app (op W)).hom
        (show (restrictedCrysDifferentials S A.obj).obj (op W) from ω)))
    ?_ ?_ ?_ ?_ (Submodule.eq_top_iff'.mp hspan ω)
  · rintro _ ⟨b, rfl⟩
    obtain ⟨r, rfl⟩ : ∃ r, (openTopRes W).hom r = b :=
      ⟨(openTopResInv W).hom b, openTopRes_openTopResInv_apply W b⟩
    have h1 : (crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op
        ((crysDifferentialsD S (A.restrictOpen W).obj).d ((openTopRes W).hom r)) =
          (crysSDerivation S).app (B.restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W)).obj
            ((openTopRes (g.hom.targetHom.hom ⁻¹ᵁ W)).hom ((g.hom.targetHom.hom.app W).hom r)) :=
      (crysDifferentialsMap_d S (CrystallineThickening.restrictOpenMap g W).hom _).trans
        (congrArg (crysDifferentialsD S (B.restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ W)).obj).d
          (appTop_restrictOpenMap_openTopRes g W r))
    refine (congrArg _ h1).trans ?_
    refine (restrictedToSheaf_app_d B.obj (g.hom.targetHom.hom ⁻¹ᵁ W) _).trans ?_
    refine Eq.trans ?_ (congrArg ((dpDifferentialsMapSheaf g.hom).app W)
      (restrictedToSheaf_app_d A.obj W r)).symm
    exact (dpDifferentialsMapSheaf_sheafApp g.hom W r).symm
  · exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  · intro x y _ _ hx hy
    exact (congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans
        ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm))
  · intro c x _ hx
    set V' := g.hom.targetHom.hom ⁻¹ᵁ W
    let r' : Γ((B.restrictOpen V').obj.thickening.target.scheme, ⊤) :=
      ((CrystallineThickening.restrictOpenMap g W).hom.targetHom.hom.appTop).hom c
    let sB : ↑(B.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op V')) :=
      (openTopResInv V').hom r'
    let sA : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)) :=
      (openTopResInv W).hom c
    have hs : (show Γ(B.obj.thickening.target.scheme, V') from sB) =
        (g.hom.targetHom.hom.app W).hom sA := openTopResInv_appTop_restrictOpenMap g W c
    let y : (crysDifferentials S).obj (op (B.restrictOpen V')) :=
      (crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op x
    have e1 : (crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op
        (show (crysDifferentials S).obj (op (A.restrictOpen W)) from c • x) =
        (show (restrictedCrysDifferentials S B.obj).obj (op V') from sB •
          (show (restrictedCrysDifferentials S B.obj).obj (op V') from y)) :=
      ((crysDifferentials S).map_smul (CrystallineThickening.restrictOpenMap g W).op c x).trans
        (congrArg (fun t : crysFormRing S (B.restrictOpen V') ↦ t • y)
          (openTopRes_openTopResInv_apply V' r').symm)
    have e2 : (show (restrictedCrysDifferentials S A.obj).obj (op W) from c • x) =
        (show (restrictedCrysDifferentials S A.obj).obj (op W) from sA •
          (show (restrictedCrysDifferentials S A.obj).obj (op W) from x)) :=
      congrArg (fun t : Γ((A.restrictOpen W).obj.thickening.target.scheme, ⊤) ↦ t • x)
        (openTopRes_openTopResInv_apply W c).symm
    refine (congrArg _ e1).trans ?_
    refine (((restrictedToSheaf B.obj).app (op V')).hom.map_smul sB _).trans ?_
    refine Eq.trans ?_ (congrArg (fun z ↦ (dpDifferentialsMapSheaf g.hom).app W
      (((restrictedToSheaf A.obj).app (op W)).hom z)) e2).symm
    refine Eq.trans ?_ (congrArg ((dpDifferentialsMapSheaf g.hom).app W)
      (((restrictedToSheaf A.obj).app (op W)).hom.map_smul sA _)).symm
    refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul (dpDifferentialsMapSheaf g.hom) sA _).symm
    rw [hs]
    exact congrArg (fun z ↦ ((g.hom.targetHom.hom.app W).hom sA) • z) hx

end Crystalline.GlobalCrystallineSituation.SmallSite

end
