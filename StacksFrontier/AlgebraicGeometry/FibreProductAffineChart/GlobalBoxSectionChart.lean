module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.BoxSectionsAffine
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.GlobalBoxSections

/-!
# A global box section, read over an affine chart

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` and `G` be quasi-coherent modules on `X` and on `Y`, and
let `c` be an affine chart of `X ×_S Y`. The sections of `F ⊠ G` over the image of `c` are
`Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` by
`Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor`, which the library already knew to be
surjective. This file adds that it is *injective* — it is built from a linear equivalence and an
isomorphism, so this is only a matter of running
`Stacks.FibreProductAffineChart.Chart.restrictFunctorIsoPullback_app_inv_hom` the other way — and
then identifies what a *global* box section becomes under it: the restriction to the chart of the
section attached to a pair of global sections is the chart's box section of the pure tensor of
their restrictions to the chart's two factors.

That identification is the comparison through which a statement about `Γ(X ×_S Y, F ⊠ G)`
becomes a statement about one chart, and the only facts it needs are that the section attached to
a pair of local sections is compatible with shrinking the open it is read over
(`Stacks.Tag01VSPullbackTensor.externalTensorSection_presheaf_map`) and with shrinking the opens
its two arguments are read over, which is the content of the first two results below.

## Main results

* `Stacks.Tag01VSPullbackTensor.externalTensorSection_restrict_left` and `..._restrict_right`:
  the section of `F ⊠ G` attached to a pair of local sections is unchanged when one of the two
  arguments is replaced by its restriction to a smaller open. In other words it depends only on
  the germs of its arguments along the open it is read over.
* `Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor_injective`: **every section of
  `F ⊠ G` over the image of a chart comes from a unique element of
  `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`.**
* `Stacks.FibreProductAffineChart.Chart.presheaf_map_externalTensorSection_top`: **the
  restriction of a global box section to a chart is the chart's box section of the pure tensor of
  the restricted sections.**

## Implementation notes

The two `restrict` lemmas are the naturality of the unit of `g ^* ⊣ g _*` in the open
(`Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_map`) followed by the collapse of two nested
restrictions (`Stacks.Tag01VSPullbackTensor.presheaf_map_map`); the two inclusions of preimages
that appear are proof-irrelevant, so no compatibility between them has to be stated.

`Stacks.FibreProductAffineChart.Chart.presheaf_map_externalTensorSection_top` is proved as a
chain of four equalities in term mode rather than by rewriting: the opens `⊤`, `c.left` and the
chart's image all occur as implicit arguments of `externalTensorSection` together with the
inclusions between them, and a rewrite that changes one of them leaves a motive that is not
type-correct.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- The unit image of a restricted section, read over a smaller open, is the unit image of the
section itself restricted to it. -/
private theorem presheaf_map_unit_restrict {Z P : Scheme.{u}} (g : Z ⟶ P) (F : P.Modules)
    {U U' : P.Opens} (hU : U' ≤ U) (x : Γ(F, U)) (W : Z.Opens) (hW : W ≤ g ⁻¹ᵁ U)
    (hW' : W ≤ g ⁻¹ᵁ U') :
    ((Scheme.Modules.pullback g).obj F).presheaf.map (homOfLE hW').op
        (modulesPullbackUnit g F U' (F.presheaf.map (homOfLE hU).op x))
      = ((Scheme.Modules.pullback g).obj F).presheaf.map (homOfLE hW).op
        (modulesPullbackUnit g F U x) := by
  rw [modulesPullbackUnit_map]
  exact presheaf_map_map _ _ _ _ _

/-- **The section of `F ⊠ G` attached to a pair of local sections only depends on the germ of
its first argument.** Shrinking the open the first section is read over, and restricting it, does
not change the section of the box product. -/
theorem externalTensorSection_restrict_left {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U U' : P.Opens} (hU : U' ≤ U) {V : Q.Opens}
    (x : Γ(F, U)) (y : Γ(G, V)) (W : (pullback p q).Opens)
    (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U) (hW₁' : W ≤ pullback.fst p q ⁻¹ᵁ U')
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    externalTensorSection p q F G (F.presheaf.map (homOfLE hU).op x) y W hW₁' hW₂
      = externalTensorSection p q F G x y W hW₁ hW₂ := by
  unfold externalTensorSection
  rw [presheaf_map_unit_restrict _ F hU _ _ hW₁ hW₁']

/-- **The section of `F ⊠ G` attached to a pair of local sections only depends on the germ of
its second argument.** -/
theorem externalTensorSection_restrict_right {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V V' : Q.Opens} (hV : V' ≤ V)
    (x : Γ(F, U)) (y : Γ(G, V)) (W : (pullback p q).Opens)
    (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V)
    (hW₂' : W ≤ pullback.snd p q ⁻¹ᵁ V') :
    externalTensorSection p q F G x (G.presheaf.map (homOfLE hV).op y) W hW₁ hW₂'
      = externalTensorSection p q F G x y W hW₁ hW₂ := by
  unfold externalTensorSection
  rw [presheaf_map_unit_restrict _ G hV _ _ hW₂ hW₂']

end Stacks.Tag01VSPullbackTensor

namespace Stacks.FibreProductAffineChart

open Stacks.Tag01VSPullbackTensor

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

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
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- **Every section of `F ⊠ G` over the image of a chart comes from a *unique* element of
`Γ(Spec A, F) ⊗_R Γ(Spec B, G)`.** -/
theorem boxSectionOfTensor_injective :
    Function.Injective (c.boxSectionOfTensor hl hr F G) := fun z₁ z₂ h => by
  have key : (c.boxSectionsEquiv hl hr F G).symm z₁ = (c.boxSectionsEquiv hl hr F G).symm z₂ :=
    ((c.restrictFunctorIsoPullback_app_hom_inv hl hr (externalTensorProduct a b F G) _).symm.trans
      (congrArg
        (fun y ↦ Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback
            ((c.specIso hl hr).inv ≫ c.ι)).app (externalTensorProduct a b F G)).hom ⊤ y)
        h)).trans
      (c.restrictFunctorIsoPullback_app_hom_inv hl hr (externalTensorProduct a b F G) _)
  exact (c.boxSectionsEquiv hl hr F G).symm.injective key

/-- **The restriction of a global box section to a chart is the chart's box section of the pure
tensor of the restricted sections.** -/
theorem presheaf_map_externalTensorSection_top
    (h₁ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ c.left)
    (h₂ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ c.right)
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    (externalTensorProduct a b F G).presheaf.map (homOfLE (le_top (a :=
          ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
            Γ(Y, c.right)))).Opens)))).op
        (externalTensorSection a b F G s t ⊤
          (Scheme.Hom.preimage_top (pullback.fst a b)).ge
          (Scheme.Hom.preimage_top (pullback.snd a b)).ge)
      = c.boxSectionOfTensor hl hr F G
          (modulesPullbackUnitTop c.fromSpecLeft F c.left c.preimage_fromSpecLeft_left
              (F.presheaf.map (homOfLE (le_top (a := c.left))).op s)
            ⊗ₜ[Γ(S, c.base)]
            modulesPullbackUnitTop c.fromSpecRight G c.right c.preimage_fromSpecRight_right
              (G.presheaf.map (homOfLE (le_top (a := c.right))).op t)) := by
  have hA : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
      Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ (⊤ : X.Opens) :=
    le_top.trans (Scheme.Hom.preimage_top (pullback.fst a b)).ge
  have hB : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
      Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ (⊤ : Y.Opens) :=
    le_top.trans (Scheme.Hom.preimage_top (pullback.snd a b)).ge
  refine (externalTensorSection_presheaf_map a b F G s t
    (Scheme.Hom.preimage_top (pullback.fst a b)).ge
    (Scheme.Hom.preimage_top (pullback.snd a b)).ge hA hB (homOfLE le_top)).trans ?_
  refine (externalTensorSection_restrict_left a b F G (le_top (a := c.left)) s t _
    hA h₁ hB).symm.trans ?_
  refine (externalTensorSection_restrict_right a b F G (le_top (a := c.right))
    (F.presheaf.map (homOfLE (le_top (a := c.left))).op s) t _ h₁ hB h₂).symm.trans ?_
  exact (c.boxSectionOfTensor_tmul hl hr F G h₁ h₂ _ _).symm

end Chart

end Stacks.FibreProductAffineChart

end
