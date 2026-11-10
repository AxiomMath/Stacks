module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.BoxSectionsAffine
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxSectionsOpens
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGluedModule
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseRingAddEquiv

/-!
# The box-section comparison over a pair of affine opens is bijective

Let `k` be a field, let `a : X ⟶ Spec k` and `b : Y ⟶ Spec k`, let `P` and `Q` be quasi-coherent
modules on `X` and on `Y`, and let `U` of `X` and `V` of `Y` be **affine** opens. Then

`Γ(P, U) ⊗_k Γ(Q, V) ⟶ Γ(P ⊠ Q, pr₁⁻¹U ⊓ pr₂⁻¹V)`

is **bijective**. This is the local half of the Künneth statement in degree zero:
`pr₁⁻¹U ⊓ pr₂⁻¹V` is the image of the chart of the pair `(U, V)` over the affine base `Spec k`,
and over a chart the sections of `P ⊠ Q` are a tensor product by
`Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv`.

Three bijections are composed. The chart identification
`Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor` is bijective — surjective already in
the tree, injective by `Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor_injective`. Its
source is a tensor product over `Γ(Spec k, ⊤)` of the sections of the two *inverse images* along
the chart's structure maps, and
`Stacks.FibreProductAffineChart.Chart.bijective_modulesPullbackUnitTop_left` and `..._right`
identify those with the sections over `U` and over `V`; the change of base ring from `k` to
`Γ(Spec k, ⊤)` is `TensorProduct.addEquivOfRingEquiv` along `AlgebraicGeometry.Scheme.ΓSpecIso`.
Finally the chart's image and `pr₁⁻¹U ⊓ pr₂⁻¹V` are equal opens, so the restriction between them
is bijective.

## Main results

* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnitTop_add`: the unit comparison on global
  sections is additive.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnitTop_fromSpec_smul`: **for an affine open the
  unit comparison is semilinear along `AlgebraicGeometry.Scheme.ΓSpecIso`** — the one fact that
  lets the chart's tensor product be compared with a tensor product over the ground field.
* `Stacks.FibreProductAffineChart.Chart.bijective_boxSectionOfTensor_restrict`: the chart
  identification, read over an open equal to the chart's image, is bijective.
* `Stacks.FibreProductAffineChart.Chart.presheaf_map_boxSectionOfTensor_tmul`: its value on a pure
  tensor of unit images, read over that open, is the box section of the pair.
* `AlgebraicGeometry.bijective_boxSectionMapOpens_of_isAffineOpen`: **the comparison over a pair
  of affine opens is bijective.**

## Implementation notes

The chart of the pair is introduced by `let` rather than by `set`. The instances the chart's
tensor product carries — `Stacks.FibreProductAffineChart.Chart.leftModuleBase`,
`Stacks.FibreProductAffineChart.Chart.boxModuleBase`, the pushout module of
`Stacks.TensorProductPushout`, and the two `Algebra Γ(Spec k, ⊤) Γ(X, U)` structures that
`Stacks.FibreProductAffineChart.Chart.specIso` needs — must all be in scope together, and the two
`Algebra` ones are supplied as local `letI`s whose types are written with the chart's *fields*,
`c.base` and `c.left`, rather than with `⊤` and `U`. That is forced:
`Stacks.FibreProductAffineChart.Chart.ofAffineOpens` is a plain definition, so `c.base` reduces
to `⊤` only at default transparency, and an instance stated at `⊤` would not be found for a goal
stated at `c.base`. For the same reason `c` is a `let` and not a `set`: the ground-field ring
isomorphism `k ≃+* Γ(Spec k, c.base)` is type-correct only because `c.base` unfolds.

The two semilinearity hypotheses of `TensorProduct.addEquivOfRingEquiv` are then discharged by
`Stacks.Tag01VSPullbackTensor.modulesPullbackUnitTop_fromSpec_smul` with no rewriting at all: the
`k`-action on `Γ(P, U)` is the action of `AlgebraicGeometry.sectionsScalars` and the
`Γ(Spec k, ⊤)`-action on the chart's side is `Module.compHom` along
`algebraMap Γ(Spec k, ⊤) Γ(X, U)`, which the chart's algebra instance makes the chart's own
structure map; the two scalars are therefore definitionally the same element of `Γ(X, U)`.

The two statements about the chart identification are proved over an arbitrary base scheme, before
the ground field is in play, and the composite is assembled as an `AddMonoidHom` so that the two
easy cases of `TensorProduct.induction_on` are `map_zero` and `map_add` on both sides. Both
choices are to keep the elaborator's unifier away from the chart's instance stack: stated
inline, the `zero` and `add` cases of that induction exhaust the heartbeat budget.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- The unit comparison on global sections is additive. -/
theorem modulesPullbackUnitTop_add {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (hU : g ⁻¹ᵁ U = ⊤) (s t : Γ(F, U)) :
    modulesPullbackUnitTop g F U hU (s + t)
      = modulesPullbackUnitTop g F U hU s + modulesPullbackUnitTop g F U hU t :=
  (congrArg _ (map_add _ s t)).trans (map_add _ _ _)

/-- **For an affine open the unit comparison on global sections is semilinear along
`AlgebraicGeometry.Scheme.ΓSpecIso`.** The scalars of `Γ(P, U)` are `Γ(X, U)`, those of the
global sections of the inverse image along `U`'s own `Spec` are `Γ(Spec Γ(X, U), ⊤)`, and the
comparison carries one action to the other along the canonical isomorphism of those two rings. -/
theorem modulesPullbackUnitTop_fromSpec_smul {X : Scheme.{u}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (P : X.Modules) (g : Γ(X, U)) (s : Γ(P, U)) :
    modulesPullbackUnitTop hU.fromSpec P U hU.fromSpec_preimage_self (g • s)
      = (Scheme.ΓSpecIso Γ(X, U)).inv.hom g •
          modulesPullbackUnitTop hU.fromSpec P U hU.fromSpec_preimage_self s := by
  unfold modulesPullbackUnitTop
  rw [modulesPullbackUnit_smul, Scheme.Modules.map_smul]
  refine congrArg (fun r => r • _) ?_
  rw [AlgebraicGeometry.IsAffineOpen.fromSpec_app_self, ConcreteCategory.comp_apply]
  exact AlgebraicGeometry.ringPresheaf_map_map_self _ _ _

/-- A bijective unit comparison on global sections, as an additive equivalence. -/
private def modulesPullbackUnitTopAddEquiv {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules)
    (U : Y.Opens) (hU : g ⁻¹ᵁ U = ⊤) (h : Function.Bijective (modulesPullbackUnitTop g F U hU)) :
    Γ(F, U) ≃+ Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' _ (modulesPullbackUnitTop_add g F U hU)) h

end Stacks.Tag01VSPullbackTensor

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart.Chart

attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower
attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower
attribute [local instance] boxModuleAlg boxModuleBase boxTower

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)
  [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- **The chart identification, read over an open equal to the chart's image, is bijective.** -/
theorem bijective_boxSectionOfTensor_restrict {W : (pullback a b).Opens}
    (hWi : W ≤ ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤)
    (hiW : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤ ≤ W) :
    Function.Bijective (fun y => (externalTensorProduct a b F G).presheaf.map (homOfLE hWi).op
      (c.boxSectionOfTensor hl hr F G y)) :=
  have hrestr : Function.Bijective
      (fun y : Γ(externalTensorProduct a b F G, ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) =>
        (externalTensorProduct a b F G).presheaf.map (homOfLE hWi).op y) :=
    ⟨Function.LeftInverse.injective (g := (externalTensorProduct a b F G).presheaf.map
        (homOfLE hiW).op) (presheaf_map_map_self _ (homOfLE hWi) (homOfLE hiW)),
      Function.RightInverse.surjective (g := (externalTensorProduct a b F G).presheaf.map
        (homOfLE hiW).op) (presheaf_map_map_self _ (homOfLE hiW) (homOfLE hWi))⟩
  hrestr.comp ⟨c.boxSectionOfTensor_injective hl hr F G,
    c.boxSectionOfTensor_surjective hl hr F G⟩

/-- The chart identification of a pure tensor of unit images, read over an open contained in the
chart's image, is the box section of the pair. -/
theorem presheaf_map_boxSectionOfTensor_tmul {W : (pullback a b).Opens}
    (hWi : W ≤ ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤)
    (h₁ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ c.left)
    (h₂ : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ c.right)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ c.left) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ c.right)
    (s : Γ(F, c.left)) (t : Γ(G, c.right)) :
    (externalTensorProduct a b F G).presheaf.map (homOfLE hWi).op
        (c.boxSectionOfTensor hl hr F G
          (modulesPullbackUnitTop c.fromSpecLeft F c.left c.preimage_fromSpecLeft_left s
            ⊗ₜ[Γ(S, c.base)]
            modulesPullbackUnitTop c.fromSpecRight G c.right c.preimage_fromSpecRight_right t))
      = externalTensorSection a b F G s t W hW₁ hW₂ :=
  (congrArg (fun y => (externalTensorProduct a b F G).presheaf.map (homOfLE hWi).op y)
      (c.boxSectionOfTensor_tmul hl hr F G h₁ h₂ s t)).trans
    (externalTensorSection_presheaf_map a b F G s t h₁ h₂ hW₁ hW₂ (homOfLE hWi))

end Stacks.FibreProductAffineChart.Chart

namespace AlgebraicGeometry

open Stacks.FibreProductAffineChart

attribute [local instance] Chart.leftModuleAlg Chart.leftModuleBase Chart.leftTower
attribute [local instance] Chart.rightModuleAlg Chart.rightModuleBase Chart.rightTower
attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower
attribute [local instance] Chart.boxModuleAlg Chart.boxModuleBase Chart.boxTower

/-- **The box-section comparison over a pair of affine opens is bijective.** For `U` an affine
open of `X` and `V` an affine open of `Y`, the sections of `P ⊠ Q` over `pr₁⁻¹U ⊓ pr₂⁻¹V` are
exactly `Γ(P, U) ⊗_k Γ(Q, V)`. -/
theorem bijective_boxSectionMapOpens_of_isAffineOpen (k : Type u) [Field k] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k)) (P : X.Modules) (Q : Y.Modules)
    [P.IsQuasicoherent] [Q.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) {W : (pullback a b).Opens}
    (hW : W = pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V) :
    Function.Bijective (boxSectionMapOpens k a b P Q U V W hW₁ hW₂) := by
  let c : Chart a b := Chart.ofAffineOpens hU hV
  let instL : Algebra ↑Γ(Spec (.of k), c.base) ↑Γ(X, c.left) := (c.leftHom).hom.toAlgebra
  let instR : Algebra ↑Γ(Spec (.of k), c.base) ↑Γ(Y, c.right) := (c.rightHom).hom.toAlgebra
  have hl : ofHom (algebraMap ↑Γ(Spec (.of k), c.base) ↑Γ(X, c.left)) = c.leftHom := rfl
  have hr : ofHom (algebraMap ↑Γ(Spec (.of k), c.base) ↑Γ(Y, c.right)) = c.rightHom := rfl
  let rho : k ≃+* ↑Γ(Spec (.of k), c.base) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let eN : ↑(sectionsOverField k a P U) ≃+
      Γ((Scheme.Modules.pullback c.fromSpecLeft).obj P, ⊤) :=
    modulesPullbackUnitTopAddEquiv _ P c.left c.preimage_fromSpecLeft_left
      (c.bijective_modulesPullbackUnitTop_left P)
  let eM : ↑(sectionsOverField k b Q V) ≃+
      Γ((Scheme.Modules.pullback c.fromSpecRight).obj Q, ⊤) :=
    modulesPullbackUnitTopAddEquiv _ Q c.right c.preimage_fromSpecRight_right
      (c.bijective_modulesPullbackUnitTop_right Q)
  have hN : ∀ (r : k) (n : ↑(sectionsOverField k a P U)), eN (r • n) = rho r • eN n :=
    fun r => modulesPullbackUnitTop_fromSpec_smul hU P (sectionsScalars k a U r)
  have hM : ∀ (r : k) (m : ↑(sectionsOverField k b Q V)), eM (r • m) = rho r • eM m :=
    fun r => modulesPullbackUnitTop_fromSpec_smul hV Q (sectionsScalars k b V r)
  let e := TensorProduct.addEquivOfRingEquiv rho eN eM hN hM
  have himg : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ :
      (Spec (.of (Γ(X, c.left) ⊗[Γ(Spec (.of k), c.base)] Γ(Y, c.right)))).Opens) = W := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso (c.specIso hl hr).inv c.ι, Chart.opensRange_ι, hW]
    rfl
  let gh : (↑(sectionsOverField k a P U) ⊗[k] ↑(sectionsOverField k b Q V)) →+
      Γ(externalTensorProduct a b P Q, W) :=
    AddMonoidHom.mk'
      (fun z => (externalTensorProduct a b P Q).presheaf.map (homOfLE himg.ge).op
        (c.boxSectionOfTensor hl hr P Q (e z)))
      (fun z z' => by
        rw [map_add e, c.boxSectionOfTensor_add hl hr P Q, map_add])
  have hval : ∀ z, boxSectionMapOpens k a b P Q U V W hW₁ hW₂ z = gh z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s t =>
      exact (c.presheaf_map_boxSectionOfTensor_tmul hl hr P Q himg.ge (himg.le.trans hW₁)
        (himg.le.trans hW₂) hW₁ hW₂ s t).symm
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']; rfl
  rw [funext hval]
  exact (c.bijective_boxSectionOfTensor_restrict hl hr P Q himg.ge himg.le).comp e.bijective

end AlgebraicGeometry

end
