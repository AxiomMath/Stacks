module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback of a tensor product of module sheaves

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. For sheaves of `𝒪_Y`-modules `A`
and `B`, the canonical comparison `f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` is an isomorphism
[Stacks, Tag 01CD]. Its invertibility follows from the stalk formula
`(f^*G)_x ≅ G_{f(x)} ⊗_{𝒪_{Y,f(x)}} 𝒪_{X,x}` for the pullback of a sheaf of modules
[Stacks, Tag 0098].

## Main definitions

* `Stacks.RingedSpace.pullbackTensorIsoApp`: the isomorphism
  `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B` whose forward map is the canonical comparison.

## Main results

* `Stacks.RingedSpace.pullbackStalkFormula'`: the stalk formula for the pullback, with the
  module structure on a stalk given by Mathlib.
* `Stacks.RingedSpace.pullbackStalkFormula`: the stalk formula for the pullback, with the
  module structure on a stalk of [Stacks, Tag 01CB].
* `Stacks.RingedSpace.isIso_comparison`: the canonical comparison
  `f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` is an isomorphism.
* `Stacks.RingedSpace.isIso_comparisonNatTrans_app`: every component of the comparison natural
  transformation is an isomorphism.

## Implementation notes

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, where the carrier, ring
and module universes coincide; this is the universe setting of the pullback of sheaves of
modules [Stacks, Tag 0096].

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u
namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The stalk formula `(f^*G)_x ≅ G_{f(x)} ⊗_{𝒪_{Y,f(x)}} 𝒪_{X,x}` for the pullback of a sheaf
of modules along `f`, with Mathlib's module structure on the stalk of a sheaf of modules. -/
@[ega "0 4.3.1", ega "0 6.7.2" "special case"]
theorem pullbackStalkFormula' : PullbackStalkFormula' f :=
  fun G x ↦ exists_modulePullbackStalkLinearEquiv f G x

/-- The stalk formula `(f^*G)_x ≅ G_{f(x)} ⊗_{𝒪_{Y,f(x)}} 𝒪_{X,x}` for the pullback of a sheaf
of modules along `f`, with the module structure on the stalk of [Stacks, Tag 01CB]. -/
theorem pullbackStalkFormula : PullbackStalkFormula f :=
  pullbackStalkFormula_of_mathlib f (pullbackStalkFormula' f)

/-- The canonical comparison `f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` is an isomorphism. -/
instance isIso_comparison (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    IsIso (comparison f A B) :=
  isIso_comparison_of_pullbackStalkFormula f (pullbackStalkFormula f) A B

/-- The isomorphism `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B` given by the canonical comparison. -/
noncomputable def pullbackTensorIsoApp (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B) :=
  @asIso _ _ _ _ (comparison f A B) (isIso_comparison f A B)

/-- The forward map of `pullbackTensorIsoApp f A B` is the canonical comparison. -/
@[simp]
lemma pullbackTensorIsoApp_hom (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackTensorIsoApp f A B).hom = comparison f A B := rfl

end Stacks.RingedSpace

end
