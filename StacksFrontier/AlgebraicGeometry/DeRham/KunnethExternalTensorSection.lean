module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedge
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections

/-!
# The local sections of an external tensor product are sheafification units of pure tensors

`Stacks.Tag01VSPullbackTensor.externalTensorSection` attaches to a local section `x` of `F` over
an open `U` of `P`, a local section `y` of `G` over an open `V` of `Q`, and an open `W` of
`P ×_S Q` inside `pr₁⁻¹U ∩ pr₂⁻¹V` a local section of `F ⊠ G` over `W`. This file records that
it is the image under the unit exhibiting the tensor product sheaf as a sheafification of the
pure tensor of the two pullback-unit images, restricted to `W`.

## Main results

* `Stacks.Tag01VSPullbackTensor.externalTensorSection_eq_tensorSheafUnit`: the section of
  `F ⊠ G` attached to a pair of local sections is the sheafification unit of the pure tensor of
  their pullback-unit images.

## Implementation notes

The identity holds by `rfl`: `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`
and `PresheafOfModules.tensorSheafUnit` are two spellings of the same sheafification unit, the
first typed through `Stacks.RingedSpace.structureRingSheaf` of the underlying ringed space of the
scheme and the second through `CategoryTheory.Sheaf.toRingCat` of its structure sheaf. Those
spellings are not interchangeable by `rewrite` or `simp`, so the passage is made once by a
term-mode identity.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- **The section of `F ⊠ G` attached to a pair of local sections is a sheafification unit.** It
is the image of the pure tensor of the pullback-unit images of `x` along `pr₁` and of `y` along
`pr₂`, each restricted to `W`, under the unit exhibiting `pr₁^*F ⊗ pr₂^*G` as the sheafification
of the objectwise tensor product. -/
theorem externalTensorSection_eq_tensorSheafUnit {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (x : Γ(F, U)) (y : Γ(G, V))
    (W : (pullback p q).Opens) (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    externalTensorSection p q F G x y W hW₁ hW₂ =
      (PresheafOfModules.tensorSheafUnit
          ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
          ((Scheme.Modules.pullback (pullback.snd p q)).obj G)).app (op W)
        (((Scheme.Modules.pullback (pullback.fst p q)).obj F).presheaf.map (homOfLE hW₁).op
            (modulesPullbackUnit (pullback.fst p q) F U x) ⊗ₜ
          ((Scheme.Modules.pullback (pullback.snd p q)).obj G).presheaf.map (homOfLE hW₂).op
            (modulesPullbackUnit (pullback.snd p q) G V y)) :=
  rfl

end Stacks.Tag01VSPullbackTensor

end
