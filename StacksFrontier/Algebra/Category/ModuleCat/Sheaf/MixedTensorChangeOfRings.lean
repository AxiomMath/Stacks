module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MixedTensorProduct

/-!
# The mixed tensor product of sheaves of modules

Let `α : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`, let `H` be
a sheaf of `O₂`-modules and let `G` be a sheaf of `O₁`-modules.  The mixed tensor product

`H ⊗_{O₁} G`

is the sheafification of the presheaf of `O₂`-modules `Stacks.MixedTensor.mixedTensorObj`, whose
sections are `H(X) ⊗_{O₁(X)} G(X)` with the `O₂(X)`-action of the first factor.  It is a sheaf
of `O₂`-modules, and the cancellation of a base change identifies it with
`H ⊗_{O₂} (O₂ ⊗_{O₁} G)` as such.

## Main definitions

* `Stacks.MixedTensor.sheafMixedTensorRight`: the endofunctor `H ↦ H ⊗_{O₁} G` of sheaves of
  `O₂`-modules.

## Main results

* `Stacks.MixedTensor.sheafMixedBaseChangeIso`: **the `O₂`-linear cancellation of a base change
  for sheaves of modules**, `H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`.

## Implementation notes

The cancellation is the presheaf-level `Stacks.MixedTensor.mixedBaseChangeNatIso` sheafified,
preceded by `Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso`, which replaces the
sectionwise extension of scalars `O₂ ⊗_{p,O₁} G` by its sheafification `O₂ ⊗_{O₁} G` inside the
second tensor variable.  Both of those are statements over `O₂`, so no comparison of
sheafifications over the two rings arises here; that comparison —
`Stacks.Cohomology.MixedDerivedTensor.SheafifyCommutesRestrictScalars` — is what the
`O₁`-linear form of the cancellation needs, and the `O₂`-linear form does not.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.MixedTensor

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂)
  (G : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O₁))

/-- **Tensoring sheaves of `O₂`-modules on the right by a sheaf of `O₁`-modules**: the
sectionwise mixed tensor product, sheafified. -/
noncomputable def sheafMixedTensorRight :
    SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O₂) ⥤
      SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O₂) :=
  SheafOfModules.forget (Stacks.commRingSheafToRingSheaf O₂) ⋙
    mixedTensorRight α.hom G.val ⋙ Stacks.moduleSheafification O₂

/-- **The `O₂`-linear cancellation of a base change for sheaves of modules**:
`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`, naturally in the sheaf `H` of `O₂`-modules. -/
noncomputable def sheafMixedBaseChangeIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).flip.obj
        ((Stacks.FlatChangeOfRings.extendScalars α).obj G)) ≅
      sheafMixedTensorRight α G :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (Stacks.commRingSheafToRingSheaf O₂))
    ((Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso α G).symm ≪≫
      Functor.isoWhiskerRight (mixedBaseChangeNatIso α.hom G.val)
        (Stacks.moduleSheafification O₂))

end Stacks.MixedTensor

end
