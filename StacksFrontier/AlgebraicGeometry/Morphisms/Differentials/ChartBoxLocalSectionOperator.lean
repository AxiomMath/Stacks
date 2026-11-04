module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBoxTensorEvaluation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartLeftOperatorSections

/-!
# Chart base change of a differential operator on the sections of a pair of local sections

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F`, `F'` be quasi-coherent `𝒪_X`-modules, let `G` be a
quasi-coherent `𝒪_Y`-module, let `D : F ⟶ F'` be a differential operator of order at most `k` on
`X/S` and let `c` be an affine chart of `X ×_S Y`. The chart base change of `D` is characterised by
its values on the pure tensors of `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`. This file turns that
characterisation into one on the sections of `F ⊠ G`: the operator carries the section of `F ⊠ G`
attached to a section `s` of `F` over an open `U'` containing the chart's first factor and a
section `t` of `G` over an open `V'` containing its second factor to the section attached to `D s`
and `t`.

## Main results

* `Stacks.FibreProductAffineChart.Chart.left_le_of_preimage_eq_top` and
  `Stacks.FibreProductAffineChart.Chart.opensRange_ι_le_preimage_fst`: an open of `X` whose
  preimage in the chart's first factor is everything contains that factor, so the chart lies in its
  preimage under the first projection; likewise on the second factor.
* `Stacks.FibreProductAffineChart.Chart.image_specIso_inv_ι_top`: the image of a chart read as the
  spectrum of a tensor product is the range of the chart.
* `Stacks.FibreProductAffineChart.Chart.boxDiffOpEquiv_apply_boxSectionLocal`: the chart base
  change of `D`, read as an operator on the sections of `F ⊠ G` over the chart, carries
  `Stacks.FibreProductAffineChart.Chart.boxSectionLocal` of `s` and `t` to that of `D s` and `t`.
* `Stacks.FibreProductAffineChart.Chart.apply_externalTensorSection_image`: the same statement for
  the operator itself, acting on the sections of `F ⊠ G` over the image of the chart.
* `Stacks.FibreProductAffineChart.Chart.apply_externalTensorSection`: the same over any open
  contained in the chart and in `pr₁⁻¹U' ∩ pr₂⁻¹V'`.

## References

* [Stacks Project, Tag 0G37](https://stacks.math.columbia.edu/tag/0G37)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

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

section Opens

variable (U' : X.Opens) (V' : Y.Opens) (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤)
  (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤)

include hU in
/-- An open of `X` whose preimage in the first factor of a chart is everything contains that
factor. -/
theorem left_le_of_preimage_eq_top : c.left ≤ U' := by
  rw [← c.isAffineOpen_left.opensRange_fromSpec, ← Scheme.Hom.image_top_eq_opensRange, ← hU]
  exact c.fromSpecLeft.image_preimage_le U'

include hV in
/-- An open of `Y` whose preimage in the second factor of a chart is everything contains that
factor. -/
theorem right_le_of_preimage_eq_top : c.right ≤ V' := by
  rw [← c.isAffineOpen_right.opensRange_fromSpec, ← Scheme.Hom.image_top_eq_opensRange, ← hV]
  exact c.fromSpecRight.image_preimage_le V'

include hU in
/-- A chart lies inside the preimage under the first projection of any open of `X` whose preimage
in the chart's first factor is everything. -/
theorem opensRange_ι_le_preimage_fst : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ U' := by
  rw [c.opensRange_ι]
  exact inf_le_left.trans
    (Scheme.Hom.preimage_mono _ (c.left_le_of_preimage_eq_top U' hU))

include hV in
/-- A chart lies inside the preimage under the second projection of any open of `Y` whose preimage
in the chart's second factor is everything. -/
theorem opensRange_ι_le_preimage_snd : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ V' := by
  rw [c.opensRange_ι]
  exact inf_le_right.trans
    (Scheme.Hom.preimage_mono _ (c.right_le_of_preimage_eq_top V' hV))

end Opens

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
  (F F' : X.Modules) (G : Y.Modules)
  [F.IsQuasicoherent] [F'.IsQuasicoherent] [G.IsQuasicoherent] (k : ℕ)
  (D : DiffOp.GlobalOp F F')
  (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D)
  (E : {E : DiffOp.RawOp (externalTensorProduct a b F G)
      (externalTensorProduct a b F' G) c.ι.opensRange //
    DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E})
  (hE : ∀ (s : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤))
      (t : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)),
      (c.boxDiffOpTensorEquiv hl hr F G F' k E).1 (s ⊗ₜ[Γ(S, c.base)] t) =
        (c.leftDiffOpEquiv hl F F' k
            ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1 s
          ⊗ₜ[Γ(S, c.base)] t)
  (U' : X.Opens) (V' : Y.Opens) (hU : c.fromSpecLeft ⁻¹ᵁ U' = ⊤)
  (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤) (s : Γ(F, U')) (t : Γ(G, V'))

include hE in
/-- **The chart base change of a differential operator on the section attached to a pair of local
sections.** Read as an operator on the sections of `F ⊠ G` over the chart, it carries the section
attached to a section `s` of `F` over `U'` and a section `t` of `G` over `V'` to the section
attached to `D s` and `t`. -/
theorem boxDiffOpEquiv_apply_boxSectionLocal :
    (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
        (externalTensorProduct a b F' G) k E).1
        (c.boxSectionLocal hl hr F G U' V' hU hV s t) =
      c.boxSectionLocal hl hr F' G U' V' hU hV (D (op U') s) t := by
  have h0 := c.boxSectionsEquiv_boxSectionLocal hl hr F G U' V' hU hV s t
  have h0' : (c.boxSectionsEquiv hl hr F G).symm
      ((modulesPullbackUnitTop c.fromSpecLeft F U' hU s) ⊗ₜ[Γ(S, c.base)]
        (modulesPullbackUnitTop c.fromSpecRight G V' hV t)) =
      c.boxSectionLocal hl hr F G U' V' hU hV s t :=
    (c.boxSectionsEquiv hl hr F G).symm_apply_eq.2 h0.symm
  have h1 := c.boxDiffOpTensorEquiv_coe_apply hl hr F G F' k E
    ((modulesPullbackUnitTop c.fromSpecLeft F U' hU s) ⊗ₜ[Γ(S, c.base)]
      (modulesPullbackUnitTop c.fromSpecRight G V' hV t))
  have h2 := hE (modulesPullbackUnitTop c.fromSpecLeft F U' hU s)
    (modulesPullbackUnitTop c.fromSpecRight G V' hV t)
  have h3 := c.leftDiffOpEquiv_apply_modulesPullbackUnitTop hl F F' k D hD U' hU s
  have h4 := c.boxSectionsEquiv_boxSectionLocal hl hr F' G U' V' hU hV (D (op U') s) t
  refine (c.boxSectionsEquiv hl hr F' G).injective ?_
  refine Eq.trans (congrArg (fun y ↦ c.boxSectionsEquiv hl hr F' G
    ((c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
      (externalTensorProduct a b F' G) k E).1 y)) h0'.symm) ?_
  exact (h1.symm.trans (h2.trans (congrArg
    (fun y ↦ y ⊗ₜ[Γ(S, c.base)] (modulesPullbackUnitTop c.fromSpecRight G V' hV t)) h3))).trans
    h4.symm

/-- The image of a chart, read as the spectrum of a tensor product, is the range of the chart. -/
theorem image_specIso_inv_ι_top :
    ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) = c.ι.opensRange := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]

/-- The comparison of the restriction along a chart with the inverse image along it, followed by
its inverse, is the identity on the sections over the chart. -/
theorem restrictFunctorIsoPullback_app_inv_hom (M : (pullback a b).Modules)
    (x : Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤)) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback
          ((c.specIso hl hr).inv ≫ c.ι)).app M).inv ⊤
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback
            ((c.specIso hl hr).inv ≫ c.ι)).app M).hom ⊤ x) = x :=
  congrArg
    (fun φ : Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι) ⟶
        Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι) ↦
      Scheme.Modules.Hom.app φ ⊤ x)
    ((Scheme.Modules.restrictFunctorIsoPullback
      ((c.specIso hl hr).inv ≫ c.ι)).app M).hom_inv_id

/-- If the comparison of the restriction along a chart with the inverse image carries `x` to `y`,
then its inverse carries `y` to `x`. -/
private theorem restrictFunctorIsoPullback_app_inv_eq (M : (pullback a b).Modules)
    {x : Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤)}
    {y : Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤)}
    (h : Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback
        ((c.specIso hl hr).inv ≫ c.ι)).app M).hom ⊤ x = y) :
    Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback
        ((c.specIso hl hr).inv ≫ c.ι)).app M).inv ⊤ y = x :=
  h ▸ c.restrictFunctorIsoPullback_app_inv_hom hl hr M x

omit [F.IsQuasicoherent] [G.IsQuasicoherent] in
include hU hV in
/-- **The local box section of a chart, back across the comparison.** The inverse of the comparison
of the restriction along the chart with the inverse image along it carries
`Stacks.FibreProductAffineChart.Chart.boxSectionLocal` of `s` and `t` to the chart-independent
section of `F ⊠ G` attached to `s` and `t` over the image of the chart. -/
theorem restrictFunctorIsoPullback_inv_boxSectionLocal
    (h₁ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ V') :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback
          ((c.specIso hl hr).inv ≫ c.ι)).app (externalTensorProduct a b F G)).inv ⊤
        (c.boxSectionLocal hl hr F G U' V' hU hV s t) =
      externalTensorSection a b F G s t (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) h₁ h₂ :=
  c.restrictFunctorIsoPullback_app_inv_eq hl hr _
    (c.restrictFunctorIsoPullback_hom_externalTensorSection hl hr F G U' V' hU hV s t h₁ h₂)

include hE hU hV in
/-- **The chart base change of a differential operator on the external tensor section over the
image of the chart.** It carries the section of `F ⊠ G` attached to `s` and `t` to the one attached
to `D s` and `t`. -/
theorem apply_externalTensorSection_image
    (hW : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
      Γ(Y, c.right)))).Opens) ≤ c.ι.opensRange)
    (h₁ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ V') :
    E.1 (Over.mk (homOfLE hW))
        (externalTensorSection a b F G s t (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) h₁ h₂) =
      externalTensorSection a b F' G (D (op U') s) t
        (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) h₁ h₂ := by
  have htgt := c.restrictFunctorIsoPullback_hom_externalTensorSection hl hr F' G U' V' hU hV
    (D (op U') s) t h₁ h₂
  have hkey := c.boxDiffOpEquiv_apply_boxSectionLocal hl hr F F' G k D hD E hE U' V' hU hV s t
  have hval := c.boxDiffOpEquiv_apply_coe_apply hl hr (externalTensorProduct a b F G)
    (externalTensorProduct a b F' G) k E (c.boxSectionLocal hl hr F G U' V' hU hV s t) hW
  have hinvsrc := c.restrictFunctorIsoPullback_inv_boxSectionLocal hl hr F G U' V' hU hV s t
    h₁ h₂
  have hcomb := hval.trans (congrArg
    (fun y ↦ Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback
          ((c.specIso hl hr).inv ≫ c.ι)).app (externalTensorProduct a b F' G)).hom ⊤
      (E.1 (Over.mk (homOfLE hW)) y)) hinvsrc)
  exact ((c.restrictFunctorIsoPullback_app_inv_eq hl hr _
    (hcomb.symm.trans (hkey.trans htgt.symm))).symm.trans
      (c.restrictFunctorIsoPullback_app_inv_hom hl hr _ _))

include hE hU hV in
/-- **The chart base change of a differential operator on the external tensor section over any open
of the chart.** Over an open of `X ×_S Y` contained in the chart and in `pr₁⁻¹U' ∩ pr₂⁻¹V'`, the
operator carries the section of `F ⊠ G` attached to `s` and `t` to the one attached to `D s` and
`t`. -/
theorem apply_externalTensorSection (W : (pullback a b).Opens) (hW : W ≤ c.ι.opensRange)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    E.1 (Over.mk (homOfLE hW)) (externalTensorSection a b F G s t W hW₁ hW₂) =
      externalTensorSection a b F' G (D (op U') s) t W hW₁ hW₂ := by
  have himg := c.image_specIso_inv_ι_top hl hr
  have hiR : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
      Γ(Y, c.right)))).Opens) ≤ c.ι.opensRange := himg.le
  have h₁ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
      Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ U' :=
    himg.le.trans (c.opensRange_ι_le_preimage_fst U' hU)
  have h₂ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
      Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ V' :=
    himg.le.trans (c.opensRange_ι_le_preimage_snd V' hV)
  have hWimg : W ≤ ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left)
      ⊗[Γ(S, c.base)] Γ(Y, c.right)))).Opens) := hW.trans himg.ge
  have hbase := c.apply_externalTensorSection_image hl hr F F' G k D hD E hE U' V' hU hV s t
    hiR h₁ h₂
  have hnat := DiffOp.RawOp.isNatural_of_isDiffOpOfOrder
    (pullback.snd a b).relativeStructureSheafMap k E.1 E.2
    (Over.mk (homOfLE hW)) (Over.mk (homOfLE hiR))
    (Over.homMk (homOfLE hWimg) (Subsingleton.elim _ _))
    (externalTensorSection a b F G s t (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) h₁ h₂)
  have hres := externalTensorSection_presheaf_map a b F G s t h₁ h₂ hW₁ hW₂
    (homOfLE hWimg)
  have hres' := externalTensorSection_presheaf_map a b F' G (D (op U') s) t h₁ h₂ hW₁ hW₂
    (homOfLE hWimg)
  refine (congrArg (fun y ↦ E.1 (Over.mk (homOfLE hW)) y) hres.symm).trans ?_
  exact hnat.trans ((congrArg
    (fun y ↦ (externalTensorProduct a b F' G).presheaf.map (homOfLE hWimg).op y) hbase).trans
      hres')

end Chart

end Stacks.FibreProductAffineChart

end
