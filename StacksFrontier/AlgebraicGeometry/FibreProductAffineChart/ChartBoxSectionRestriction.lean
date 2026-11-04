module

public import StacksFrontier.AlgebraicGeometry.CoefficientIso.Unit
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionLocalTensor

/-!
# The local box section of a chart, as a section of the box product over the chart

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` and `G` be modules on `X` and on `Y`, and let `c` be a
chart of `X ×_S Y`. The comparison `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`
of the restriction along the chart morphism with the inverse image along it carries the section
`Stacks.Tag01VSPullbackTensor.externalTensorSection` of `F ⊠ G` attached to a pair of local
sections, read over the image of the chart, to
`Stacks.FibreProductAffineChart.Chart.boxSectionLocal`.

## Main results

* `Stacks.Tag01VSPullbackTensor.externalTensorSection_presheaf_map`: the section of `F ⊠ G`
  attached to a pair of local sections is compatible with restriction of the open it is read over.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnitTop_restrictFunctorIsoPullback`: for an open
  immersion and an open of the target whose preimage is the whole source, the global section of
  the inverse image attached to a section over that open is the comparison applied to its
  restriction to the image of the immersion.
* `Stacks.FibreProductAffineChart.Chart.restrictFunctorIsoPullback_hom_externalTensorSection`:
  the comparison carries the external tensor section over the image of a chart to the chart's
  local box section.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- The restriction to a smaller open of the section of `F ⊠ G` attached to a pair of local
sections is the section attached to the same pair. -/
theorem externalTensorSection_presheaf_map {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (x : Γ(F, U)) (y : Γ(G, V))
    {W W' : (pullback p q).Opens} (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) (hW'₁ : W' ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW'₂ : W' ≤ pullback.snd p q ⁻¹ᵁ V) (i : W' ⟶ W) :
    (externalTensorProduct p q F G).presheaf.map i.op
        (externalTensorSection p q F G x y W hW₁ hW₂)
      = externalTensorSection p q F G x y W' hW'₁ hW'₂ := by
  have h1 := toTensorSheafSection_presheaf_map
    ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
    ((Scheme.Modules.pullback (pullback.snd p q)).obj G) i
    (((Scheme.Modules.pullback (pullback.fst p q)).obj F).presheaf.map (homOfLE hW₁).op
      (modulesPullbackUnit (pullback.fst p q) F U x))
    (((Scheme.Modules.pullback (pullback.snd p q)).obj G).presheaf.map (homOfLE hW₂).op
      (modulesPullbackUnit (pullback.snd p q) G V y))
  have h2 := presheaf_map_map ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
    (homOfLE hW₁) i (homOfLE hW'₁) (modulesPullbackUnit (pullback.fst p q) F U x)
  have h3 := presheaf_map_map ((Scheme.Modules.pullback (pullback.snd p q)).obj G)
    (homOfLE hW₂) i (homOfLE hW'₂) (modulesPullbackUnit (pullback.snd p q) G V y)
  refine h1.trans (congrArg₂
    (fun (z : Γ((Scheme.Modules.pullback (pullback.fst p q)).obj F, W'))
        (w : Γ((Scheme.Modules.pullback (pullback.snd p q)).obj G, W')) ↦
      toTensorSheafSection (pullback p q).toRingedSpace
        ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
        ((Scheme.Modules.pullback (pullback.snd p q)).obj G) (op W') (z ⊗ₜ w)) h2 h3)

/-- For an open immersion `j` and an open `U` of the target whose preimage is the whole source,
the global section of `j ^* M` attached to a section `s` of `M` over `U` is the image under the
comparison of the restriction of `s` to the image of `j`. -/
theorem modulesPullbackUnitTop_restrictFunctorIsoPullback {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] (M : W.Modules) (U : W.Opens) (hU : j ⁻¹ᵁ U = ⊤) (s : Γ(M, U))
    (hle : j ''ᵁ (⊤ : Z.Opens) ≤ U) :
    ((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE hU.ge).op
        (modulesPullbackUnit j M U s)
      = Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback j).app M).hom ⊤
          (M.presheaf.map (homOfLE hle).op s) := by
  have key : modulesPullbackUnit j M U s =
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M) (j ⁻¹ᵁ U)
        (M.presheaf.map (homOfLE (j.image_preimage_le U)).op s) :=
    (ConcreteCategory.congr_hom
      (Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app_app j M U) s).trans
      (ConcreteCategory.comp_apply _ _ s)
  have h2 := presheaf_map_map M (homOfLE (j.image_preimage_le U))
    (homOfLE (show j ''ᵁ (⊤ : Z.Opens) ≤ j ''ᵁ (j ⁻¹ᵁ U) from j.image_mono hU.ge))
    (homOfLE hle) s
  have h1 := homApp_presheaf_map
    ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M) (homOfLE hU.ge)
    (M.presheaf.map (homOfLE (j.image_preimage_le U)).op s)
  rw [key]
  exact h1.symm.trans (congrArg
    (fun w ↦ Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M) ⊤ w) h2)

end Stacks.Tag01VSPullbackTensor

namespace Stacks.FibreProductAffineChart

open Stacks.Tag01VSPullbackTensor

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
  (F : X.Modules) (G : Y.Modules)

/-- The comparison of the restriction along the chart morphism with the inverse image along it
carries the section of `F ⊠ G` attached to a section `s` of `F` over `U'` and a section `t` of `G`
over `V'`, read over the image of the chart, to
`Stacks.FibreProductAffineChart.Chart.boxSectionLocal`. -/
theorem restrictFunctorIsoPullback_hom_externalTensorSection (U' : X.Opens) (V' : Y.Opens)
    (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤) (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤)
    (s : Γ(F, U')) (t : Γ(G, V'))
    (h₁ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ V') :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback ((c.specIso hl hr).inv ≫ c.ι)).app
          (externalTensorProduct a b F G)).hom ⊤
        (externalTensorSection a b F G s t (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) h₁ h₂)
      = c.boxSectionLocal hl hr F G U' V' hU hV s t := by
  have h3a := externalTensorSection_presheaf_map a b F G s t
    (inf_le_left (a := pullback.fst a b ⁻¹ᵁ U') (b := pullback.snd a b ⁻¹ᵁ V'))
    (inf_le_right (a := pullback.fst a b ⁻¹ᵁ U') (b := pullback.snd a b ⁻¹ᵁ V'))
    h₁ h₂ (homOfLE (le_inf h₁ h₂))
  have h3b := modulesPullbackUnitTop_restrictFunctorIsoPullback
    ((c.specIso hl hr).inv ≫ c.ι) (externalTensorProduct a b F G)
    (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V')
    (c.preimage_specIso_inv_ι_inf_eq_top hl hr U' V' hU hV)
    (externalTensorSection a b F G s t
      (pullback.fst a b ⁻¹ᵁ U' ⊓ pullback.snd a b ⁻¹ᵁ V') inf_le_left inf_le_right)
    (le_inf h₁ h₂)
  rw [c.boxSectionLocal_eq hl hr F G U' V' hU hV s t]
  exact (congrArg
    (fun w ↦ Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback ((c.specIso hl hr).inv ≫ c.ι)).app
        (externalTensorProduct a b F G)).hom ⊤ w) h3a).symm.trans h3b.symm

end Chart

end Stacks.FibreProductAffineChart

end
