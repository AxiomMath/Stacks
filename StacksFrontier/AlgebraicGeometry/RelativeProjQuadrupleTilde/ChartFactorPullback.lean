module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart

/-!
# The pullback of a sheaf along a morphism factoring through a chart, along a further pullback

For an open immersion `f : Y ⟶ S`, an identification `e : N|_Y ≅ M` and a morphism
`h = g ≫ f : T ⟶ S`, `Scheme.Modules.pullbackIsoOfRestrictIso` identifies `h^*N` with `g^*M`.
This file proves that the identification is compatible with pulling back along a further
morphism `k : T' ⟶ T`: the identification for `k ≫ g` is the pullback along `k` of the one for
`g`, read through the composition laws `k^*h^* ≅ (k ≫ h)^*` and `k^*g^* ≅ (k ≫ g)^*`. In
particular this holds for `ℳ̃` on the relative homogeneous spectrum and the chart sheaves,
`Stacks.RelativeProj.Situation.moduleSheafPullbackChartIso_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S Y T T' : Scheme.{u}}

/-- **The identification of `h^*N` with `g^*M` is compatible with a further pullback.** -/
theorem pullbackIsoOfRestrictIso_comp (f : Y ⟶ S) [IsOpenImmersion f] {N : S.Modules}
    {M : Y.Modules} (e : N.restrict f ≅ M) (g : T ⟶ Y) {h : T ⟶ S} (hfac : h = g ≫ f)
    (k : T' ⟶ T) {h' : T' ⟶ S} (hk : k ≫ h = h') (hfac' : h' = (k ≫ g) ≫ f) :
    pullbackIsoOfRestrictIso f e (k ≫ g) hfac' =
      (pullbackCompIsoOfEq k h hk N).symm ≪≫
        (pullback k).mapIso (pullbackIsoOfRestrictIso f e g hfac) ≪≫ (pullbackComp k g).app M := by
  subst hfac' hfac
  ext : 1
  have hassoc := congrArg (fun φ => φ.app N) (pseudofunctor_associativity k g f)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hassoc
  have hassoc' : (pullbackComp k (g ≫ f)).inv.app N ≫
      (pullback k).map ((pullbackComp g f).inv.app N) ≫
        (pullbackComp k g).hom.app ((pullback f).obj N) =
      eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (k ≫ g) f).inv.app N := by
    rw [← cancel_mono ((pullbackComp (k ≫ g) f).hom.app N)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact hassoc
  set φ := (((restrictFunctorIsoPullback f).app N).symm ≪≫ e).hom with hφ
  have hnat := (pullbackComp k g).hom.naturality φ
  simp only [Functor.comp_map] at hnat
  change (pullbackCongr (rfl : (k ≫ g) ≫ f = (k ≫ g) ≫ f)).hom.app N ≫
      (pullbackComp (k ≫ g) f).inv.app N ≫ (pullback (k ≫ g)).map φ =
    ((pullbackCongr hk).inv.app N ≫ (pullbackComp k (g ≫ f)).inv.app N) ≫
      (pullback k).map ((pullbackCongr (rfl : g ≫ f = g ≫ f)).hom.app N ≫
        (pullbackComp g f).inv.app N ≫ (pullback g).map φ) ≫ (pullbackComp k g).hom.app M
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.map_comp, Category.assoc, eqToIso.inv]
  rw [hnat, reassoc_of% hassoc']
  simp

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} {T T' : Scheme.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- **`h^*ℳ̃ ≅ g^*ℳ̃(W)` along a further pullback.** -/
theorem moduleSheafPullbackChartIso_comp (W : s.base.affineOpens)
    (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) {h : T ⟶ relativeProj s}
    (hfac : h = g ≫ relativeProjChart s W) (k : T' ⟶ T) {h' : T' ⟶ relativeProj s}
    (hk : k ≫ h = h') (hfac' : h' = (k ≫ g) ≫ relativeProjChart s W) :
    moduleSheafPullbackChartIso ℳ W (k ≫ g) hfac' =
      (pullbackCompIsoOfEq k h hk (moduleSheaf ℳ)).symm ≪≫
        (Scheme.Modules.pullback k).mapIso (moduleSheafPullbackChartIso ℳ W g hfac) ≪≫
          (Scheme.Modules.pullbackComp k g).app (moduleChart ℳ W) :=
  Scheme.Modules.pullbackIsoOfRestrictIso_comp _ _ g hfac k hk hfac'

end Stacks.RelativeProj.Situation

end
