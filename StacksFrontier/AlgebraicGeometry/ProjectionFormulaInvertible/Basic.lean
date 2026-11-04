module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# Stacks 0FZE for an invertible module: the projection formula is an isomorphism

Let `f : X ⟶ Y` be a morphism of ringed spaces, `G` a sheaf of `𝒪_X`-modules and `H` an
*invertible* sheaf of `𝒪_Y`-modules. This file proves that the projection formula morphism of
[Stacks, Tag 0FZE],

`f_* G ⊗_{𝒪_Y} H ⟶ f_* (G ⊗_{𝒪_X} f^* H)`,

is an isomorphism — with no hypothesis on `f` or on `G` whatsoever.

## Main results

* `Stacks.ProjectionFormula.isIso_projectionFormulaMap`: **the projection formula for an
  invertible `H`**, [Stacks, Tag 01E8] in that case.
* `Stacks.ProjectionFormula.projectionFormulaIso`: the same read as an isomorphism.

## The inputs

The abstract statement `Stacks.ProjectionFormula.isIso_adjunctionTensorMap` asks for three
things, and the morphism itself is `Stacks.ProjectionFormula.projectionFormulaMap'`.

* The comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` is invertible: this is [Stacks, Tag 01CD]
  (`Stacks.RingedSpace.comparisonNatTrans_app_isIso`, proved stalkwise).
* Tensoring on the right by `H` is an equivalence of `Mod(𝒪_Y)`: this is invertibility of `H`
  in the sense of [Stacks, Tag 01CS], via
  `Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` for
  `(Tensor.sheafTensor _).flip.obj H`, transported to the uncurried bifunctor of the
  projection-formula morphism along `CategoryTheory.Functor.tensorRightOfUncurryIso`.
* Tensoring on the right by `f^* H` is an equivalence of `Mod(𝒪_X)`: this is [Stacks, Tag
  0B8L], `Stacks.InvertiblePullback.isInvertible_pullback`, for any morphism of ringed
  spaces.

So no monoidal structure on `SheafOfModules`, no associator or unitor, and no inverse object
is used: the only place the invertible object enters is as "tensoring by it is an equivalence",
which is how [Stacks, Tag 01CS] is stated here.

## Scope

[Stacks, Tag 0FZE] in full asserts the isomorphism for an affine morphism `f` and
quasi-coherent `G`, `H`, where `H` need not be invertible. That is strictly more general than
the invertible case treated here, which is the case in which the statement holds for *every*
morphism of ringed spaces.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

attribute [local implicit_reducible] TopCat.Sheaf TopCat.Presheaf.IsSheaf
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The projection formula for an invertible module -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Tensoring on the right by an invertible sheaf, as the uncurried bifunctor, is an
equivalence. -/
private theorem isEquivalence_tensorRightOf_uncurry {Z : RingedSpace.{u, u}}
    (H : SheafOfModules.{u} (structureRingSheaf Z))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj (structureRingSheaf Z).property H] :
    (tensorRightOf (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩)) H).IsEquivalence :=
  @Functor.isEquivalence_of_iso _ _ _ _ _ _
    (Functor.tensorRightOfUncurryIso
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩) H).symm
    (Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor Z.sheaf.obj
      (structureRingSheaf Z).property H)

/-- **[Stacks, Tag 0FZE] / [Stacks, Tag 01E8] for an invertible second argument.** For every
morphism of ringed spaces `f : X ⟶ Y`, every sheaf of `𝒪_X`-modules `G` and every *invertible*
sheaf of `𝒪_Y`-modules `H`, the projection formula morphism

`f_* G ⊗_{𝒪_Y} H ⟶ f_* (G ⊗_{𝒪_X} f^* H)`

is an isomorphism.

The three inputs are [Stacks, Tag 01CD], invertibility of `H`, and
[Stacks, Tag 0B8L] for `f^* H`; see the module documentation. -/
theorem isIso_projectionFormulaMap (G : SheafOfModules.{u} (structureRingSheaf X))
    (H : SheafOfModules.{u} (structureRingSheaf Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureRingSheaf Y).property H] :
    IsIso (projectionFormulaMap' f G H) := by
  have hpull := Stacks.InvertiblePullback.isInvertible_pullback f H
  exact @isIso_adjunctionTensorMap _ _ _ _ _ _ (pullbackAdjunction f)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩))
    (comparisonNatTrans f) G H
    (isEquivalence_tensorRightOf_uncurry H) (isEquivalence_tensorRightOf_uncurry _)
    fun M => comparisonNatTrans_app_isIso f (M, H)

/-- **The projection formula isomorphism for an invertible module**,
`f_* G ⊗_{𝒪_Y} H ≅ f_* (G ⊗_{𝒪_X} f^* H)`, whose forward map is the canonical morphism
`Stacks.ProjectionFormula.projectionFormulaMap'`. -/
noncomputable def projectionFormulaIso (G : SheafOfModules.{u} (structureRingSheaf X))
    (H : SheafOfModules.{u} (structureRingSheaf Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureRingSheaf Y).property H] :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj
        ((pushforwardFunctor f).obj G, H) ≅
      (pushforwardFunctor f).obj (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).obj
          (G, (pullbackFunctor f).obj H)) :=
  haveI := isIso_projectionFormulaMap f G H
  asIso (projectionFormulaMap' f G H)

/-- **Every functor out of `Mod(𝒪_Y)` takes the projection formula morphism at an invertible
`H` to an epimorphism**, because it takes it to an isomorphism. This is the form used in the
proof of [Stacks, Tag 0B5P], with `F` the global sections functor; it is stated for an
arbitrary `F` because nothing about global sections is used. -/
theorem epi_map_projectionFormulaMap (G : SheafOfModules.{u} (structureRingSheaf X))
    (H : SheafOfModules.{u} (structureRingSheaf Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureRingSheaf Y).property H]
    {E : Type*} [Category E] (F : SheafOfModules.{u} (structureRingSheaf Y) ⥤ E) :
    Epi (F.map (projectionFormulaMap' f G H)) :=
  inferInstanceAs (Epi (F.mapIso (projectionFormulaIso f G H)).hom)

/-- The forward map of `projectionFormulaIso` is the projection formula morphism. -/
lemma projectionFormulaIso_hom (G : SheafOfModules.{u} (structureRingSheaf X))
    (H : SheafOfModules.{u} (structureRingSheaf Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureRingSheaf Y).property H] :
    (projectionFormulaIso f G H).hom = projectionFormulaMap' f G H := rfl

end Stacks.ProjectionFormula

end
