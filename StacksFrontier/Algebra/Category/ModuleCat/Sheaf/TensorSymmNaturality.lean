module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor

/-!
# Naturality of the symmetry of a tensor product of sheaves of modules

The symmetry `M ⊗_O N ≅ N ⊗_O M` of the tensor product of (pre)sheaves of modules is natural in
both factors. This file records the two squares in which a morphism is moved between the
functor position and the object position of the tensor product, at the presheaf level and after
sheafification.

## Main results

* `Stacks.tensorRight_map_comp_tensorCommHom`: under the symmetry of the tensor product of
  presheaves of modules, tensoring a morphism in the first variable becomes tensoring it in the
  second variable; the other orientation of `Stacks.tensorCommHom_comp_tensorRight_map`.
* `Stacks.FlatChangeOfRings.sheafTensorMapRight_comp_sheafTensorSymmIso_hom` and
  `Stacks.FlatChangeOfRings.sheafTensorRight_map_comp_sheafTensorSymmIso_hom`: **naturality of
  the symmetry of the tensor product sheaf in the factor which crosses between the functor
  position and the object position**, in its two orientations. These are the sheafifications of
  the presheaf-level squares `Stacks.tensorCommHom_comp_tensorRight_map` and
  `Stacks.tensorRight_map_comp_tensorCommHom`.

## Implementation notes

The sheaf-level squares are stated where the ring sheaf `O` is a variable rather than at the
application: at a ringed space the sheafification functor's arguments are not determined by the
statement and the unifier does not terminate inside the budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w z

namespace Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Under the symmetry of the tensor product, tensoring a morphism in the first variable
becomes tensoring it in the second variable. This is
`Stacks.tensorCommHom_comp_tensorRight_map` with the symmetry read in the other direction;
`Stacks.tensorObjComm` makes the two mutually inverse, but the two squares have the morphism
tensored on opposite sides of the composite, so neither is an instance of the other. -/
lemma tensorRight_map_comp_tensorCommHom (M : PresheafOfModules.{z} (ringPresheaf O))
    {N N' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') :
    (tensorRight M).map α ≫ tensorCommHom N' M =
      tensorCommHom N M ≫ tensorMapRight M α := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

end Stacks

namespace Stacks.FlatChangeOfRings

open Stacks
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Naturality of the symmetry of the tensor product sheaf in the factor it moves out of the
functor position.** For `β : B ⟶ B'`, tensoring `A` on the right by `β` and then exchanging the
two factors is exchanging them and then applying the endofunctor `· ⊗_{O} A` to `β`.

Both vertical maps are the image under sheafification of a morphism of objectwise tensor
products, so this is the sheafification of the presheaf-level square
`Stacks.tensorCommHom_comp_tensorRight_map`. -/
lemma sheafTensorMapRight_comp_sheafTensorSymmIso_hom (O : Sheaf J CommRingCat.{w})
    (A : SheafOfModules.{w} (commRingSheafToRingSheaf O))
    {B B' : SheafOfModules.{w} (commRingSheafToRingSheaf O)} (β : B ⟶ B') :
    ((sheafTensor O).obj A).map β ≫ (sheafTensorSymmIso O B' A).hom =
      (sheafTensorSymmIso O B A).hom ≫ ((sheafTensor O).flip.obj A).map β :=
  map_comp_eq_map_comp (moduleSheafification O)
    (tensorCommHom_comp_tensorRight_map (O := O.obj) A.val β.val)

/-- **Naturality of the symmetry of the tensor product sheaf in the factor it moves into the
functor position**, the other orientation of
`Stacks.FlatChangeOfRings.sheafTensorMapRight_comp_sheafTensorSymmIso_hom`. For `β : B ⟶ B'`,
applying the endofunctor `· ⊗_{O} A` to `β` and then exchanging the two factors is exchanging
them and then tensoring `A` on the right by `β`.

It is the sheafification of `Stacks.tensorRight_map_comp_tensorCommHom`. The two squares are not
instances of one another even though the two symmetries are mutually inverse, because the
morphism `β` is tensored on opposite sides of the composite in the two. -/
lemma sheafTensorRight_map_comp_sheafTensorSymmIso_hom (O : Sheaf J CommRingCat.{w})
    (A : SheafOfModules.{w} (commRingSheafToRingSheaf O))
    {B B' : SheafOfModules.{w} (commRingSheafToRingSheaf O)} (β : B ⟶ B') :
    ((sheafTensor O).flip.obj A).map β ≫ (sheafTensorSymmIso O A B').hom =
      (sheafTensorSymmIso O A B).hom ≫ ((sheafTensor O).obj A).map β :=
  map_comp_eq_map_comp (moduleSheafification O)
    (tensorRight_map_comp_tensorCommHom (O := O.obj) A.val β.val)

end Stacks.FlatChangeOfRings

end
