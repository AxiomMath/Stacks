module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The monoidal constraints of the tensor product of sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)`. The tensor product of two sheaves
of `O`-modules is the sheafification `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` of
  the tensor product of the
underlying presheaves of modules. The pinned Mathlib has no `MonoidalCategory` structure on
`SheafOfModules R`, so the unit and associativity constraints of this tensor product are not
available. They are built, with their pentagon and triangle coherences, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence`
(`Stacks.SheafOfModules.tensorSheafLeftUnitor` and `tensorSheafAssociator`, the right unit
constraint being `Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints`);
the braiding is `Stacks.SheafOfModules.tensorSheafBraiding`. What this
file adds is the remaining piece Tag 01CX needs, the tensor product of two *isomorphisms* of
sheaves of modules, together with the invertibility of the sheafification counit that the
constraints are stated through.

## Main definitions

* `Stacks.SheafOfModules.isIso_sheafifyAdjunction_counit` — the invertibility of the
  sheafification counit that the constraints are stated through.

## Implementation notes

The tensor product of two isomorphisms of sheaves of modules is
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerMultiplication.lean`), where its
`simp` normal form `Stacks.SheafOfModules.tensorSheafMapIso_hom_eq` and its reflexivity
lemmas also live; this file carried a second name for it in this namespace and no longer does.

The site object and morphism universes `u`, `v` are independent of the section universe `w`,
as everywhere in this development; nothing here relates `w` to the size of the site.

These are the constraints that Tag 01CX needs in order to put an abelian group structure on
the isomorphism classes of invertible sheaves of modules, and they are stated for
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` rather than for a chosen tensor functor so
  that they compose with the
tensor powers of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPower.lean`.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-- The sheafification counit is an isomorphism: the structure sheaf is already a sheaf, so the
comparison map of ring presheaves used by `PresheafOfModules.sheafification` is the identity. -/
instance isIso_sheafifyAdjunction_counit :
    IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
  change IsIso
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
  infer_instance

/-- The tensor product sheaf of two isomorphisms of sheaves of modules: tensor the underlying
presheaf isomorphisms and sheafify. It is
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso`, under the name this namespace uses. -/
noncomputable def tensorSheafMapIso
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : M ≅ M') (f : N ≅ N') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (M)).obj (N)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (M')).obj (N')) :=
  TensorPower.tensorSheafMapIso O hO e f

end Stacks.SheafOfModules
