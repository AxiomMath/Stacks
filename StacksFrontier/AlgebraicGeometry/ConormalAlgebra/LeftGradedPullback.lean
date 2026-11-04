module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.LeftGradedModule

/-!
# Pullback of a left graded module along a morphism of schemes

`Stacks.RingedSpace.pullbackLeftGradedModule` pulls a left graded module over a sheaf of graded
algebras back along a morphism of ringed spaces. This file reads that construction in the
vocabulary of schemes, over `Stacks.Conormal.gradedPullback`, and adds that the pieces stay
quasi-coherent ([Stacks, Tag 01BG]).

## Main definitions

* `Stacks.Conormal.leftGradedPullback`: the pullback of a left graded module along a morphism of
  schemes, a left graded module over the pulled-back graded algebra.

## Main results

* `Stacks.Conormal.leftGradedPullback_isQuasicoherent`: the pieces of the pullback are
  quasi-coherent as soon as those of the module are.
* `Stacks.Conormal.leftGradedPullback_smul_pullbackSection`: **the pulled-back action on
  pulled-back sections** is the pullback of the action.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (g : Z ⟶ X) {A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **The pullback of a left graded module along a morphism of schemes.** -/
noncomputable def leftGradedPullback (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A) :
    SheafOfModules.LeftGradedModule.{u, u, u} (gradedPullback g A) :=
  Stacks.RingedSpace.pullbackLeftGradedModule g.toLRSHom.toShHom A ℳ

/-- The degree `n` piece of the pullback of `ℳ` is the pullback of the degree `n` piece of `ℳ`. -/
@[simp] lemma leftGradedPullback_piece (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A)
    (n : ℤ) : (leftGradedPullback g ℳ).piece n = (Scheme.Modules.pullback g).obj (ℳ.piece n) :=
  rfl

/-- The pieces of the pullback are quasi-coherent as soon as those of the module are. This is
[Stacks, Tag 01BG]. -/
instance leftGradedPullback_isQuasicoherent (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A)
    [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] (n : ℤ) :
    ((leftGradedPullback g ℳ).piece n).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g (ℳ.piece n)

/-- **The pulled-back action on pulled-back sections.** The action of the pullback of a
homogeneous section of the algebra on the pullback of a homogeneous section of the module, over
the whole preimage of an open `U`, is the pullback of the action. -/
lemma leftGradedPullback_smul_pullbackSection (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A)
    (i n : ℤ) (U : X.Opens) (a : (A.piece i).val.obj (op U)) (x : (ℳ.piece n).val.obj (op U)) :
    (leftGradedPullback g ℳ).smul i n (op (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackSection g (A.piece i) U (g ⁻¹ᵁ U) le_rfl a)
        (Scheme.Modules.pullbackSection g (ℳ.piece n) U (g ⁻¹ᵁ U) le_rfl x) =
      Scheme.Modules.pullbackSection g (ℳ.piece (i + n)) U (g ⁻¹ᵁ U) le_rfl
        (ℳ.smul i n (op U) a x) := by
  rw [pullbackSection_self g (A.piece i) U a, pullbackSection_self g (ℳ.piece n) U x,
    pullbackSection_self g (ℳ.piece (i + n)) U (ℳ.smul i n (op U) a x)]
  exact Stacks.RingedSpace.pullbackLeftGradedModule_smul_pullbackUnit g.toLRSHom.toShHom A ℳ
    i n U a x

end Stacks.Conormal

end
