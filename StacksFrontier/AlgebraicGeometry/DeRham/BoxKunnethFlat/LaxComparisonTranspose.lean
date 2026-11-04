module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Deformation.RingedSpaceThickening.ModuleExtension

/-!
# The lax comparison of the direct image to `(X, f^{-1}𝒪_S)`, by its transpose

Let `f : X ⟶ S` be a morphism of schemes and `τ : (X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` the morphism of
ringed spaces which is the identity on spaces.  Its direct image `τ_*` is restriction of
scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, and the lax comparison
`τ_*M ⊗_{f^{-1}𝒪_S} τ_*N ⟶ τ_*(M ⊗_{𝒪_X} N)`,
`Stacks.DeRhamDirectImage.inverseImageTensorLax`, sends a pure tensor of sections to the same
pure tensor.  This file identifies it with the transpose along `τ^* ⊣ τ_*` of the comparison of
[Stacks, Tag 01CD] followed by the two counits: both send `m ⊗ n` to `m ⊗ n`.

## Main results

* `Stacks.DeRhamDirectImage.inverseImageTensorLax_eq_comparisonTranspose`: the identification.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct
open _root_.AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped CategoryTheory.Prod

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRhamDirectImage

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The lax comparison is the transpose of the comparison of Stacks 01CD followed by the two
counits.** -/
theorem inverseImageTensorLax_eq_comparisonTranspose (M N : Modules X.toRingedSpace) :
    inverseImageTensorLax f M N =
      Stacks.RingedSpace.comparisonTranspose (toInverseImageBase f)
          ((pushforward (toInverseImageBase f)).obj M)
          ((pushforward (toInverseImageBase f)).obj N) ≫
        (Stacks.RingedSpace.pushforwardFunctor (toInverseImageBase f)).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase f)).counit.app M ×ₘ
              (Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase f)).counit.app N)) := by
  refine AlgebraicGeometry.RingedSpaceThickening.tensorSheaf_hom_ext (Y := inverseImageBase f)
    (fun V m n => ?_)
  refine (inverseImageTensorLax_toTensorSheafSection f M N (op V) m n m n HEq.rfl HEq.rfl).trans
    ?_
  have h (P : Modules X.toRingedSpace) (p) :
      ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase f)).counit.app P).val.app
        (op V) (Stacks.RingedSpace.pullbackUnit (toInverseImageBase f)
          ((pushforward (toInverseImageBase f)).obj P) (op V) p) = p :=
    congrArg (fun t => t.val.app (op V) p)
      ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase f)).right_triangle_components P)
  have hT := tensorSheafMap_app_toTensorSheafSection X.toRingedSpace _ _ M N
    ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase f)).counit.app M)
    ((Stacks.RingedSpace.pullbackAdjunction (toInverseImageBase f)).counit.app N) V
    (Stacks.RingedSpace.pullbackUnit (toInverseImageBase f)
      ((pushforward (toInverseImageBase f)).obj M) (op V) m)
    (Stacks.RingedSpace.pullbackUnit (toInverseImageBase f)
      ((pushforward (toInverseImageBase f)).obj N) (op V) n)
  have hC := Stacks.RingedSpace.comparisonTranspose_unit_tmul (toInverseImageBase f)
    ((pushforward (toInverseImageBase f)).obj M) ((pushforward (toInverseImageBase f)).obj N)
    (op V) m n
  rw [h M m, h N n] at hT
  refine Eq.trans ?_ (congrArg (fun t => t) (Eq.trans (congrArg _ hC) hT)).symm
  rfl

end Stacks.DeRhamDirectImage

end
