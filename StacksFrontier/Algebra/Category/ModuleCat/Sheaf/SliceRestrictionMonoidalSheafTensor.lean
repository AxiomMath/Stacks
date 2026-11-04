module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal

/-!
# Restriction to a slice site is monoidal for the re-seated tensor product

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and `U : C`.  Restriction of sheaves
of `𝒪`-modules to the slice site `(Over U, J.over U)` is `SheafOfModules.overFunctor`, and
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal` equips it with a
`CategoryTheory.Functor.Monoidal` structure — but for
`Stacks.SheafOfModules.Strict.monoidalCategory`, the structure of Tag 01CA whose tensor product
is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`.

The *other* monoidal structure with that same tensor product,
`SheafOfModules.monoidalCategorySheafTensor`, is the one the complexes of Tag 0FPT and hence the
derived tensor product are built on: its curried tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` on the nose.  A `CategoryTheory.Functor.Monoidal` is a
structure over a *particular* pair of monoidal structures, and the two structures are not the
same term — `Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)` and
`SheafOfModules.monoidalCategorySheafTensor R` are not equal even at `with_unfolding_all`
transparency — so the instance does not transport for free.

This file carries it across.  The two structures agree on every structural morphism
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree`), so the identity
functor between them is monoidal in both directions, and restriction for the re-seated structure
is the composite

`(Mod(𝒪), sheafTensor) ⟶ (Mod(𝒪), strict) ⟶ (Mod(𝒪_U), strict) ⟶ (Mod(𝒪_U), sheafTensor)`

of three monoidal functors, whose underlying functor is `SheafOfModules.overFunctor` itself.

## Main definitions

* `Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalSheafTensor`: **restriction of
  sheaves of modules to a slice site is a monoidal functor for
  `SheafOfModules.monoidalCategorySheafTensor` on each side.**

## Implementation notes

The three monoidal structures of the composite are named by `@`-application throughout: the
source and target categories of the two identity functors are the *same* type carrying two
different monoidal structures, so instance search cannot tell which is meant and
`inferInstanceAs` — the idiom used for the analogous composite in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal`, where the intermediate
category is a nominally distinct type synonym — is not available here.

Two spellings of the slice data are crossed by the defeq check of `:=` rather than transported:
`Stacks.SheafOfModules.SliceRestriction.overFunctor 𝒪 h𝒪 U` is
`SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf R) U`, and the strict
structure of the slice site built from `sliceRingPresheaf 𝒪 U` is
`Stacks.SheafOfModules.Strict.monoidalCategory (R.over U).obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (R.over U))`.  Both are `rfl`, the sheaf
conditions involved being propositions.

Nothing here is tagged: this is the comparison of two monoidal structures already in the
library, not a clause of a tag.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 00XB](https://stacks.math.columbia.edu/tag/00XB) — the localized
  site `C/U`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u

namespace Stacks.SheafOfModules.SliceRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v}) (U : C)
  [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Restriction of sheaves of `𝒪`-modules to the slice site over `U` is a monoidal functor for
the monoidal structure whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`** —
that is, for `SheafOfModules.monoidalCategorySheafTensor` on each side.

This is `Stacks.SheafOfModules.SliceRestriction.overFunctorStrictMonoidal`, which says the same
for the structure of Tag 01CA, conjugated on both sides by the identity functor, which is
monoidal between the two structures because they agree on every structural morphism. -/
@[instance_reducible]
def overFunctorMonoidalSheafTensor :
    @Functor.Monoidal _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor (R.over U))
      (_root_.SheafOfModules.overFunctor.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R) U) :=
  @Functor.Monoidal.instComp _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor R) _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor (R.over U)) (𝟭 _) _
      (_root_.SheafOfModules.idMonoidalSheafTensorToStrict R)
    (@Functor.Monoidal.instComp _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory (R.over U).obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (R.over U))) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor (R.over U))
      (_root_.SheafOfModules.overFunctor.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R) U) (𝟭 _)
      (overFunctorStrictMonoidal R.obj (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R) U)
      (_root_.SheafOfModules.idMonoidalStrictToSheafTensor (R.over U)))

end Stacks.SheafOfModules.SliceRestriction

end
