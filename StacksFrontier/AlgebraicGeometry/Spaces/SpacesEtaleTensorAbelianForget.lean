module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCharacterTwistTorsor
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSignTwist

/-!
# The underlying abelian sheaf of a module tensored with an abelian sheaf

Let `R` be a sheaf of rings on a site, let `M` be a sheaf of `R`-modules and let `L` be a
presheaf of abelian groups.  The sheaf of modules `Stacks.SheafOfModules.tensorAbelianModule M L`
is the sheafification, as a presheaf of modules, of the objectwise tensor product over `ℤ` of
`M` with `L`.  Forgetting the module structure, it is the abelian tensor product of the
underlying abelian sheaf of `M` with `L`: the sheafification, as a presheaf of abelian groups, of
that same objectwise tensor product.

## Main definitions

* `Stacks.SheafOfModules.toSheafTensorAbelianModuleIso`: the underlying abelian sheaf of
  `M ⊗_ℤ L` is the abelian tensor product of the underlying abelian sheaf of `M` with `L`.
* `Stacks.SheafOfModules.toSheafTensorAbelianModuleCharacterTwistIso`: the same comparison with
  `L` the character twist `ℤ(χ)`, in the form
  `CategoryTheory.characterTwistTensor` in which the alternating Čech development uses it.

## Implementation notes

The comparison is the presheaf-level identity `PresheafOfModules.sheafificationCompToSheaf`
evaluated at the objectwise tensor product; that identity is an isomorphism of *functors*, so
the two sides of the statement below are definitionally equal.  Comparing them directly is
nevertheless expensive, because the `CategoryTheory.Sheaf` structures involved carry
`ModuleCat.restrictScalars` wrappers; following
`Stacks.SheafOfModules.toSheafPushforwardIso`, the isomorphism is therefore *built* out of the
functor-level one rather than asserted.

For the character twist there is one more step: `CategoryTheory.characterTwistTensor` tensors
with the twist *presheaf* before sheafifying, whereas `tensorAbelianModule` is applied to the
twist *sheaf*.  The two agree by `CategoryTheory.characterTwistTensorIso`.

## References

* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u u₁ u₂ r

namespace Stacks.SheafOfModules

open AddCommGrpCat

/-! ### The general comparison -/

section General

variable {C : Type u₁} [Category.{u₂} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

/-- **Forgetting the module structure of a module tensored with an abelian sheaf gives the
abelian tensor product.**  The underlying abelian sheaf of `M ⊗_ℤ L` is the sheafification of
the objectwise tensor product over `ℤ` of the underlying abelian sheaf of `M` with `L`.

This is `PresheafOfModules.sheafificationCompToSheaf` evaluated at the objectwise tensor
product. -/
def toSheafTensorAbelianModuleIso (M : _root_.SheafOfModules.{u + 1} R)
    (L : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (_root_.SheafOfModules.toSheaf.{u + 1} R).obj (tensorAbelianModule M L) ≅
      (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
        (presheafTensor ((_root_.SheafOfModules.toSheaf.{u + 1} R).obj M).obj L) :=
  (PresheafOfModules.sheafificationCompToSheaf.{u + 1} (𝟙 R.obj)).app
    (tensorAbelianPresheaf M L)

end General

/-! ### The comparison at the character twist -/

section CharacterTwist

variable {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] {R : Sheaf J RingCat.{r}}
    {W : C} {G : Type w} [Group G]

/-- **The underlying abelian sheaf of a module tensored with the character twist is the abelian
twist of its underlying abelian sheaf.**  Combining
`Stacks.SheafOfModules.toSheafTensorAbelianModuleIso` with
`CategoryTheory.characterTwistTensorIso`, which moves the sheafification of the twist across
the tensor product. -/
def toSheafTensorAbelianModuleCharacterTwistIso (M : _root_.SheafOfModules.{u + 1} R)
    (act : G →* Aut W) (χ : G →* ℤˣ) :
    (_root_.SheafOfModules.toSheaf.{u + 1} R).obj
        (tensorAbelianModule M (characterTwist W act χ J).obj) ≅
      characterTwistTensor ((_root_.SheafOfModules.toSheaf.{u + 1} R).obj M).obj act χ J :=
  toSheafTensorAbelianModuleIso M _ ≪≫
    (characterTwistTensorIso (χ := χ)
      (F := ((_root_.SheafOfModules.toSheaf.{u + 1} R).obj M).obj) (act := act)).symm

end CharacterTwist

end Stacks.SheafOfModules

end
