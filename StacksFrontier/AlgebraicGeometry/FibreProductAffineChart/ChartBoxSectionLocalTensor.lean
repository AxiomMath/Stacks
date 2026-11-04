module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.LocalBoxSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBoxProductOperator

/-!
# The section of a box product on a chart attached to a pair of local sections

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` and `G` be quasi-coherent modules on `X` and on `Y`, and
let `c` be a chart of `X ×_S Y` with `R = Γ(S, W)`, `A = Γ(X, U)`, `B = Γ(Y, V)`. A section `s` of
`F` over an open `U'` of `X` containing the first factor of the chart, and a section `t` of `G`
over an open `V'` containing its second factor, give a global section of `F ⊠ G` on the chart.
This file evaluates `Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv` — the `A ⊗_R B`-linear
identification of those sections with `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` — on that section: the answer
is the pure tensor of the two sections, read as global sections of the inverse images on `Spec A`
and on `Spec B`.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.boxSectionLocal`: the global section of `F ⊠ G` on a
  chart attached to `s` and `t`, in the spelling of the chart morphism
  `(c.specIso hl hr).inv ≫ c.ι` that `Chart.boxSectionsEquiv` is stated at.

## Main results

* `Stacks.FibreProductAffineChart.Chart.preimage_specIso_inv_ι_inf_eq_top`: the chart's preimage
  of `pr₁⁻¹U' ∩ pr₂⁻¹V'` is everything as soon as the preimages of `U'` in `Spec A` and of `V'` in
  `Spec B` are.
* `Stacks.FibreProductAffineChart.Chart.pullbackCongr_hom_boxSectionLocal`: the local box section
  in the chart spelling corresponds to `Stacks.FibreProductAffineChart.chartBoxSectionLocal` in the
  affine-chart spelling.
* `Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv_boxSectionLocal`: the identification of
  the sections of `F ⊠ G` on a chart with `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` carries
  `Chart.boxSectionLocal` to the pure tensor of the two sections.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.Tag01VSPullbackTensor

/-- **The identification of the pullbacks along two equal morphisms, on a global restriction of a
pullback-unit image.** For equal morphisms `f = g` and an open `U` whose two preimages both
contain the whole source, it carries the restriction to `⊤` of the unit image of a section over
`U` along `f` to the restriction to `⊤` of its unit image along `g`. -/
theorem modulesPullbackUnit_pullbackCongr_hom_map_top {Z W : Scheme.{u}} {f g : Z ⟶ W}
    (hf : f = g) (M : W.Modules) (U : W.Opens) (s : Γ(M, U)) (hUf : ⊤ ≤ f ⁻¹ᵁ U)
    (hUg : ⊤ ≤ g ⁻¹ᵁ U) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hf).hom.app M) ⊤
        (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hUf).op
          (modulesPullbackUnit f M U s))
      = ((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hUg).op
          (modulesPullbackUnit g M U s) := by
  subst hf
  rfl

end Stacks.Tag01VSPullbackTensor

namespace Stacks.FibreProductAffineChart

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower
attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower
attribute [local instance] boxModuleAlg boxModuleBase boxTower

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
  (F : X.Modules) (G : Y.Modules)

/-- If an open `U'` of `X` pulls back to all of the first factor of a chart and an open `V'` of
`Y` to all of its second factor, then `pr₁⁻¹U' ∩ pr₂⁻¹V'` pulls back to all of the chart. -/
theorem preimage_specIso_inv_ι_inf_eq_top (U' : X.Opens) (V' : Y.Opens)
    (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤) (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤) :
    ((c.specIso hl hr).inv ≫ c.ι) ⁻¹ᵁ
        (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V') = ⊤ := by
  rw [c.specIso_inv_ι_eq hl hr]
  exact preimage_affineChart_inf_eq_top a b Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)
    c.fromSpecLeft c.fromSpecRight c.fromSpecBase (c.fromSpecLeft_comp_eq hl).symm
    (c.fromSpecRight_comp_eq hr).symm U' V' hU hV

/-- The global section of `F ⊠ G` on a chart attached to a section `s` of `F` over an open `U'`
whose preimage in the chart's first factor is everything and a section `t` of `G` over an open
`V'` with the same property on the second factor: the section of `F ⊠ G` over
`pr₁⁻¹U' ∩ pr₂⁻¹V'` coming from the pure tensor of the pullbacks of `s` and `t`, pulled back
along the chart morphism `(c.specIso hl hr).inv ≫ c.ι` and read over `⊤`. -/
def boxSectionLocal (U' : X.Opens) (V' : Y.Opens) (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤)
    (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤) (s : Γ(F, U')) (t : Γ(G, V')) :
    Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj
        (externalTensorProduct a b F G), ⊤) :=
  ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj
      (externalTensorProduct a b F G)).presheaf.map
    (homOfLE (c.preimage_specIso_inv_ι_inf_eq_top hl hr U' V' hU hV).ge).op
    (modulesPullbackUnit ((c.specIso hl hr).inv ≫ c.ι) (externalTensorProduct a b F G)
      (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V')
      (externalTensorSection a b F G s t
        (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V') inf_le_left inf_le_right))

/-- `Stacks.FibreProductAffineChart.Chart.boxSectionLocal` written out. -/
theorem boxSectionLocal_eq (U' : X.Opens) (V' : Y.Opens) (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤)
    (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤) (s : Γ(F, U')) (t : Γ(G, V')) :
    c.boxSectionLocal hl hr F G U' V' hU hV s t =
      ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj
          (externalTensorProduct a b F G)).presheaf.map
        (homOfLE (c.preimage_specIso_inv_ι_inf_eq_top hl hr U' V' hU hV).ge).op
        (modulesPullbackUnit ((c.specIso hl hr).inv ≫ c.ι) (externalTensorProduct a b F G)
          (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V')
          (externalTensorSection a b F G s t
            (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V') inf_le_left inf_le_right)) := rfl

/-- **The two spellings of a local box section on a chart agree.** The identification of the
pullbacks along the chart morphism in its spectrum-of-a-tensor-product spelling and in its
affine-chart spelling carries `Stacks.FibreProductAffineChart.Chart.boxSectionLocal` to
`Stacks.FibreProductAffineChart.chartBoxSectionLocal`. -/
theorem pullbackCongr_hom_boxSectionLocal (U' : X.Opens) (V' : Y.Opens)
    (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤) (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤)
    (s : Γ(F, U')) (t : Γ(G, V')) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackCongr (c.specIso_inv_ι_eq hl hr)).hom.app
          (externalTensorProduct a b F G)) ⊤
        (c.boxSectionLocal hl hr F G U' V' hU hV s t)
      = chartBoxSectionLocal a b Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)
          c.fromSpecLeft c.fromSpecRight c.fromSpecBase (c.fromSpecLeft_comp_eq hl).symm
          (c.fromSpecRight_comp_eq hr).symm F G U' V' hU hV s t := by
  rw [c.boxSectionLocal_eq hl hr F G U' V' hU hV s t, chartBoxSectionLocal_eq]
  exact modulesPullbackUnit_pullbackCongr_hom_map_top (c.specIso_inv_ι_eq hl hr)
    (externalTensorProduct a b F G)
    (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V')
    (externalTensorSection a b F G s t
      (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V') inf_le_left inf_le_right)
    (c.preimage_specIso_inv_ι_inf_eq_top hl hr U' V' hU hV).ge
    (by
      rw [← c.specIso_inv_ι_eq hl hr]
      exact (c.preimage_specIso_inv_ι_inf_eq_top hl hr U' V' hU hV).ge)

variable [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- **The section of a box product on a chart attached to a pair of local sections, under the
chart identification.** The `Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`-linear identification of the sections
of `F ⊠ G` on a chart with `Γ(Spec Γ(X, U), F) ⊗_{Γ(S, W)} Γ(Spec Γ(Y, V), G)` carries the
section attached to a section `s` of `F` over `U'` and a section `t` of `G` over `V'` to the pure
tensor of the corresponding global sections of the inverse images. -/
theorem boxSectionsEquiv_boxSectionLocal (U' : X.Opens) (V' : Y.Opens)
    (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤) (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤)
    (s : Γ(F, U')) (t : Γ(G, V')) :
    c.boxSectionsEquiv hl hr F G (c.boxSectionLocal hl hr F G U' V' hU hV s t)
      = ((modulesPullbackUnitTop c.fromSpecLeft F U' hU s) ⊗ₜ[Γ(S, c.base)]
          (modulesPullbackUnitTop c.fromSpecRight G V' hV t) :
        Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) ⊗[Γ(S, c.base)]
          Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)) := by
  have a1 := moduleSpecΓFunctor_mapIso_app_hom_apply
    (Scheme.Modules.pullbackCongr (c.specIso_inv_ι_eq hl hr))
    (externalTensorProduct a b F G) (c.boxSectionLocal hl hr F G U' V' hU hV s t)
  have a2 := c.pullbackCongr_hom_boxSectionLocal hl hr F G U' V' hU hV s t
  have k2 := moduleIsoTrans_apply _ _ (a1.trans a2)
    (chartExternalTensorSectionsIso_hom_chartBoxSectionLocal a b Γ(S, c.base) Γ(X, c.left)
      Γ(Y, c.right) c.fromSpecLeft c.fromSpecRight c.fromSpecBase
      (c.fromSpecLeft_comp_eq hl).symm (c.fromSpecRight_comp_eq hr).symm F G U' V' hU hV s t)
  have hx : c.boxSectionsIso hl hr F G =
      moduleSpecΓFunctor.mapIso
        ((Scheme.Modules.pullbackCongr (c.specIso_inv_ι_eq hl hr)).app
          (externalTensorProduct a b F G)) ≪≫
      chartExternalTensorSectionsIso a b Γ(S, c.base) Γ(X, c.left)
        Γ(Y, c.right) c.fromSpecLeft c.fromSpecRight c.fromSpecBase
        (c.fromSpecLeft_comp_eq hl).symm (c.fromSpecRight_comp_eq hr).symm F G := rfl
  have hcross := (congrArg
    (fun e ↦ e.hom (c.boxSectionLocal hl hr F G U' V' hU hV s t)) hx).trans k2
  have k3 := moduleIsoTrans_apply (c.boxSectionsIso hl hr F G)
    (MonoidalCategory.tensorIso
      (Stacks.TensorProductPushout.extendScalarsObjIso
        (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback c.fromSpecLeft).obj F)))
      (Stacks.TensorProductPushout.extendScalarsObjIso
        (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback c.fromSpecRight).obj G)))) hcross
    (moduleTensorIso_hom_tmul _ _
      (Stacks.TensorProductPushout.extendScalarsObjIso_hom_tmul _ _ _)
      (Stacks.TensorProductPushout.extendScalarsObjIso_hom_tmul _ _ _))
  have hb : ∀ (z : Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj
        (externalTensorProduct a b F G), ⊤)),
      c.boxSectionsEquiv hl hr F G z =
        Stacks.TensorProductPushout.cancelBaseChangePushout Γ(S, c.base) Γ(X, c.left)
          Γ(Y, c.right) Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤)
          Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)
          ((c.boxSectionsIso hl hr F G ≪≫
            MonoidalCategory.tensorIso
              (Stacks.TensorProductPushout.extendScalarsObjIso
                (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
                (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback c.fromSpecLeft).obj F)))
              (Stacks.TensorProductPushout.extendScalarsObjIso
                (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
                (moduleSpecΓFunctor.obj
                  ((Scheme.Modules.pullback c.fromSpecRight).obj G)))).hom z) :=
    fun _ ↦ rfl
  exact (hb _).trans
    ((congrArg (fun z ↦ Stacks.TensorProductPushout.cancelBaseChangePushout Γ(S, c.base)
        Γ(X, c.left) Γ(Y, c.right) Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤)
        Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤) z) k3).trans
      (Stacks.TensorProductPushout.cancelBaseChangePushout_one_tmul _ _ _ _ _))

end Chart

end Stacks.FibreProductAffineChart

end
