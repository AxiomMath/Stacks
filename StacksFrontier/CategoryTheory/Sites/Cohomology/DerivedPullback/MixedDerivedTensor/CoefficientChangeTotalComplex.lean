module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.MixedTensorTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SecondVariableOnSheaves

/-!
# The identity of total tensor complexes at a change of coefficient rings

Let `α : O₁ ⟶ O₂` be a map of sheaves of commutative rings on a site `(C, J)`. Restriction of
scalars along `α`, extension of scalars along `α` and the cancellation of a base change
`H|_{O₁} ⊗_{O₁} G ≅ (H ⊗_{O₂} (O₂ ⊗_{O₁} G))|_{O₁}` form a
`Stacks.Cohomology.MixedDerivedTensor.MixedTensorSetup`, so the identity of total tensor
complexes proved there holds at a coefficient change:

`Tot(F|_{O₁} ⊗_{O₁} G) ≅ Tot(F ⊗_{O₂} (O₂ ⊗_{O₁} G))|_{O₁}`

for unbounded cochain complexes `F` of `O₂`-modules and `G` of `O₁`-modules.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.setupOfCoefficientChange`: the datum at a coefficient
  change.

## Implementation notes

This is the second instance of `MixedTensorSetup`, the first being `setupOfHom` at a morphism of
ringed topoi. The two differ in what plays the part of the third sheaf of rings: there it is
`f⁻¹O'`, the inverse image of the structure sheaf of the target, and here it is `O₁` itself,
the source of the coefficient change — so nothing on this route ever leaves the given site or
mentions an auxiliary topos. The functor on the second tensor factor landing in `O₁`-modules is
the identity, the underived identity is
`Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso`, which is unconditional, and
its naturality in that factor is `tensorBaseChangeLinearIso_naturality_snd`.

Both the ring sheaves and the tensor bifunctors are written in two ways across the two chains —
`Stacks.commRingSheafToRingSheaf` against `Stacks.SheafOfModules.Tensor.ringSheaf`, and
`Stacks.sheafTensorRight` against `Stacks.SheafOfModules.Tensor.sheafTensor` flipped. The ring
sheaves agree definitionally, so the instance fields are filled by ascription. The tensor
functors are identified by `Stacks.SheafOfModules.FlatCoproduct.sheafTensorRightIso`, which
conjugates `tensorBaseChangeLinearIso` on both sides, as
`Stacks.Cohomology.MixedDerivedTensor.mixedTensorModuleIso` does for the morphism-of-ringed-topoi
chain.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.FlatChangeOfRings

universe u

namespace Stacks.Cohomology.MixedDerivedTensor

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₁ O₂ : Sheaf J CommRingCat.{u}}

/-- **Extension of scalars is additive**, being a left adjoint between preadditive categories. -/
instance additive_extendScalars (α : O₁ ⟶ O₂) : (extendScalars α).Additive :=
  (extendScalarsAdjunction α).left_adjoint_additive

/-- **The datum of the identity of total tensor complexes at a change of coefficient rings.**
Restriction of scalars along `α : O₁ ⟶ O₂`, extension of scalars along `α` on the second tensor
factor, the identity functor in its place over `O₁`, and the cancellation of a base change as
the underived identity. -/
def setupOfCoefficientChange (α : O₁ ⟶ O₂) : MixedTensorSetup O₁ O₂ O₁ where
  res := SheafOfModules.restrictScalars.{u} (ringSheafMap α)
  resAdditive := inferInstanceAs (SheafOfModules.restrictScalars.{u} (ringSheafMap α)).Additive
  resPreserves _ := inferInstanceAs
    (PreservesColimitsOfShape _ (SheafOfModules.restrictScalars.{u} (ringSheafMap α)))
  pb := extendScalars α
  pbPreservesZero := inferInstanceAs (extendScalars α).PreservesZeroMorphisms
  ii := 𝟭 _
  iiPreservesZero := inferInstance
  iso G := tensorBaseChangeLinearIso α G
  iso_naturality_snd γ M := tensorBaseChangeLinearIso_naturality_snd α γ M

end Stacks.Cohomology.MixedDerivedTensor

end
