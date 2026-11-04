module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring with a finite locally free module preserves injectivity

Let `(X, O_X)` be a ringed space, let `I` be an injective `O_X`-module and let `E` be a finite
locally free `O_X`-module. Stacks 01E7 asserts that `E ⊗ I` is injective.

## Main results

* `Stacks.SheafOfModules.OnSpace.injective_tensorSheaf_of_finiteLocallyFree`: `E ⊗ I` is injective.

## References

* [Stacks Project, Tag 01E7](https://stacks.math.columbia.edu/tag/01E7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
  MonoidalCategory

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] monoidal

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The functors `D ⊗ -` and `- ⊗ D` are isomorphic. -/
noncomputable def tensorLeftTensorRightIso
    (D : SheafOfModules.{u} (structureSheafRing X)) :
    tensorLeft D ≅ tensorRight D :=
  NatIso.ofComponents (fun A => TensorPresentations.tensorSheafSwap X D A) (by
    intro A B f
    change (D ◁ f) ≫ (TensorPresentations.tensorSheafSwap X D B).hom =
      (TensorPresentations.tensorSheafSwap X D A).hom ≫ (f ▷ D)
    rw [← id_tensorHom, ← tensorHom_id, tensorHom_eq, tensorHom_eq]
    exact (TensorPresentations.tensorSheafSwap_naturality X (𝟙 D) f).symm)

/-- Tensoring an injective sheaf of modules with a finite locally free sheaf of modules preserves
injectivity. -/
@[stacks 01E7]
theorem injective_tensorSheaf_of_finiteLocallyFree
    (I E : SheafOfModules.{u} (structureSheafRing X))
    [Injective I] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    Injective ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (E)).obj (I))) := by
  let D : SheafOfModules.{u} (structureSheafRing X) := dualSheaf X E
  let _ : ExactPairing E D :=
    dualSheafExactPairing X E (isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X E)
  let _ : Functor.IsRightAdjoint (tensorRight D) :=
    ⟨⟨tensorRight E, ⟨tensorRightAdjunction E D⟩⟩⟩
  let _ : Functor.PreservesMonomorphisms (tensorLeft D) :=
    Functor.PreservesMonomorphisms.of_iso (tensorLeftTensorRightIso X D).symm
  exact ((Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (tensorLeftAdjunction E D)).injective_obj ‹Injective I› : Injective (E ⊗ I))

end Stacks.SheafOfModules.OnSpace
