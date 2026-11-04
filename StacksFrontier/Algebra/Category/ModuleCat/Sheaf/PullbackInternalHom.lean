module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback and the internal Hom of sheaves of modules

For a morphism of ringed spaces `f : X ⟶ Y` and a sheaf of `𝒪_Y`-modules `F`,
`f_* 𝓗om_{𝒪_X}(f^*F, G) ≅ 𝓗om_{𝒪_Y}(F, f_*G)`, naturally in the `𝒪_X`-module `G`.

## Main definitions

* `Stacks.PullbackSheafTensor.pullbackTensorLeftIso`: `f^*(F ⊗ -) ≅ f^*F ⊗ f^*(-)`.
* `Stacks.PullbackSheafTensor.pushforwardInternalHomPullbackIso`: the isomorphism above.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.InternalHom Stacks.RingedSpace

universe u

namespace Stacks.PullbackSheafTensor

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `f^*(F ⊗ -) ≅ f^*F ⊗ f^*(-)`, as an isomorphism of functors. -/
def pullbackTensorLeftIso (F : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj F ⋙ modulePullback f ≅
      modulePullback f ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
        ((modulePullback f).obj F) :=
  NatIso.ofComponents (fun T => sheafTensorComparisonIso f F T)
    (fun w => (sheafTensorComparison_naturality_right f F w).symm)

/-- **The internal adjunction of pullback and pushforward**:
`f_* 𝓗om(f^*F, G) ≅ 𝓗om(F, f_*G)`, naturally in `G`. -/
@[sga "4 IV 13.4" "special case"]
def pushforwardInternalHomPullbackIso (F : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    modulePushforward f ⋙ internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology Y.carrier) Y.sheaf F ≅
      internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology X.carrier) X.sheaf
        ((modulePullback f).obj F) ⋙ modulePushforward f :=
  Adjunction.rightAdjointUniq
    ((sheafTensorHomAdjunction Y.sheaf F).comp (modulePullbackPushforwardAdjunction f))
    (Adjunction.ofNatIsoLeft
      ((modulePullbackPushforwardAdjunction f).comp
        (sheafTensorHomAdjunction X.sheaf ((modulePullback f).obj F)))
      (pullbackTensorLeftIso f F).symm)

end Stacks.PullbackSheafTensor
