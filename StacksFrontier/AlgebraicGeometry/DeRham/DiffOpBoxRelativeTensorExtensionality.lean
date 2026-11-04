module

public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxRelativeTensor
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackUnitTensorExtensionality

/-!
# Extensionality for morphisms out of `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖`

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a`. Two morphisms of `f^{-1}𝒪_S`-modules out of the source
`p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖` of
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` which agree on
the images of pure tensors of pullback-unit local sections are equal.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeInverseImageTensor_hom_ext`:
  two morphisms out of `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖` which agree on pure tensors of
  pullback-unit sections are equal.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
open Stacks.DeRhamDirectImage
open Stacks.PullbackUnitGenerators

universe u

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- Two morphisms out of the tensor product `φ^{-1}A ⊗_{𝒪_Z} ψ^{-1}B` of the pullbacks of
`A` and `B` along `φ : Z ⟶ Z₁` and `ψ : Z ⟶ Z₂` which agree on pure tensors of pullback-unit
sections are equal. -/
private theorem tensor_hom_ext_of_unitSections_tensorSheaf
    {Z Z₁ Z₂ : RingedSpace.{u}} (φ : Z ⟶ Z₁) (ψ : Z ⟶ Z₂)
    (A : Modules Z₁) (B : Modules Z₂) {C : Modules Z}
    {u v : ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf, ((Z)).IsSheaf⟩))).obj
        ((_root_.pullback φ).obj A, (_root_.pullback ψ).obj B) ⟶ C}
    (h : ∀ (U : (Opens Z.carrier)ᵒᵖ)
        (x : ((_root_.pullback φ).obj A).val.obj U)
        (y : ((_root_.pullback ψ).obj B).val.obj U),
        x ∈ unitSections φ A U → y ∈ unitSections ψ B U →
      tensorEvalMap u U (x ⊗ₜ[Z.presheaf.obj U] y) =
        tensorEvalMap v U (x ⊗ₜ[Z.presheaf.obj U] y)) :
    u = v :=
  tensor_hom_ext_of_unitSections φ ψ A B h

/-- **Two morphisms out of `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖` which agree on pure tensors of
pullback-unit local sections are equal.** The unit sections are those of the inverse image along
the first projection of `𝓕` read over `a^{-1}𝒪_S`, and of the inverse image along the second
projection of `𝓖` read over `b^{-1}𝒪_S`. -/
theorem relativeInverseImageTensor_hom_ext (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b)
    {C : Modules (inverseImageBase (pullback.fst a b ≫ a))}
    {u v : (relativeInverseImageTensor a b).obj (F, G) ⟶ C}
    (h : ∀ (U : (Opens (inverseImageBase (pullback.fst a b ≫ a)).carrier)ᵒᵖ)
        (x : ((leftRelativeInverseImage a b).obj F).val.obj U)
        (y : ((rightRelativeInverseImage a b).obj G).val.obj U),
        x ∈ unitSections (relativeInverseImageProjection (pullback.fst a b) a)
              ((toInverseImageModules a).obj F) U →
        y ∈ unitSections (sndRelativeInverseImageProjection a b)
              ((toInverseImageModules b).obj G) U →
      tensorEvalMap u U
          (x ⊗ₜ[(inverseImageBase (pullback.fst a b ≫ a)).presheaf.obj U] y) =
        tensorEvalMap v U
          (x ⊗ₜ[(inverseImageBase (pullback.fst a b ≫ a)).presheaf.obj U] y)) :
    u = v :=
  tensor_hom_ext_of_unitSections_tensorSheaf
    (relativeInverseImageProjection (pullback.fst a b) a)
    (sndRelativeInverseImageProjection a b) ((toInverseImageModules a).obj F)
    ((toInverseImageModules b).obj G) h

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
