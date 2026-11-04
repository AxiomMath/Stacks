module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RestrictModulesMonoidal

/-!
# Restriction to an open subspace, monoidal at the seating the derived cluster uses

Let `(X, O_X)` be a ringed space and `U` an open subset.
`Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidal` equips

`Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U : Mod(O_X) ⥤ Mod(O_{X|_U})`

with a `CategoryTheory.Functor.Monoidal` structure — but for
`Stacks.PullbackMonoidalSheaf.monoidalCategory`, the structure obtained by localizing the
objectwise tensor product of presheaves of modules along sheafification. The derived cluster in
which Stacks 0FPB and therefore the pairing of Stacks 0FPD live is built instead on
`SheafOfModules.monoidalCategorySheafTensor`, whose curried tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor` on the nose. A `CategoryTheory.Functor.Monoidal` is a
structure over a *particular* pair of monoidal structures, so the instance does not transport for
free. This file carries it across, which is **link 1 of the shrinking step of Stacks 0FPD,
conclusion (a)**: the proof of that conclusion replaces `X` by an open neighbourhood of a point
finitely often, and shrinking is legitimate only if the left dual shrinks with it, so the
restriction has to be monoidal at the seating the pairing is taken in.

## Main definitions

* `Stacks.Cohomology.LeftDualPerfect.restrictModulesRingStrictMonoidal`: restriction to an open
  subspace is monoidal for `Stacks.SheafOfModules.Strict.monoidalCategory`, the strict
  structure of Tag 01CA whose tensor product is the tensor product sheaf on the nose.
* `Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidalSheafTensor`: **restriction to an
  open subspace is monoidal for `SheafOfModules.monoidalCategorySheafTensor` on each side**, which
  is the seating of `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory`.

## The chain, and the three structures it crosses

Three monoidal structures on `Mod(O_X)` occur, all with the same underlying category and none
equal to another as a term:

* the **localized** one, `Stacks.SheafOfModules.monoidalCategory X.presheaf h`, restated at the
  ringed space as `Stacks.PullbackMonoidalSheaf.monoidalCategory X`. Its tensor product is the
  localization of the objectwise one; this is where `restrictModulesRing_monoidal` lives;
* the **strict** one of Tag 01CA, `Stacks.SheafOfModules.Strict.monoidalCategory` applied to
  `(X.sheaf).obj` and `(Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property`, whose tensor
  product is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`;
* the **re-seated** one, `SheafOfModules.monoidalCategorySheafTensor X.sheaf`, whose tensor
  product is `Stacks.SheafOfModules.Tensor.sheafTensor`.

The two crossings are each a pair of identity functors, already available and general:

* strict ↔ localized is `Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal` and
  `...fromLocalizedMonoidalMonoidal`, the two halves of the identity equivalence between
  `Mod(O_X)` and the type synonym `CategoryTheory.Monoidal.LocalizedMonoidal` that carries the
  localized structure;
* localized ↔ re-seated is `SheafOfModules.idMonoidalStrictToSheafTensor` and
  `...idMonoidalSheafTensorToStrict`, which exist because the strict and re-seated structures
  agree on every structural morphism.

So the content of this file is the composite of five monoidal functors whose underlying functor is
`restrictModulesRing X U` itself, and no coherence diagram is checked here. This is exactly the
shape of `Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalSheafTensor`, the same
crossing performed for restriction to a *slice site*; what is new is only that the middle functor
is restriction to an open subspace of a ringed **space**, which is where conclusion (a) of
Stacks 0FPD has to be proved (the ringed-site perfectness of Tag 08G5 is pinned to
`RingedSite.{u, u, 0}` and Tags 08G7 and 08GA to `RingedSite.{0, 0, 0}`, while Tags 08CM to 08CS
are universe-general for a ringed space).

Nothing below is a clause of a tag: it is a step of the proof of conclusion (a), so no
`@[stacks …]` attribute is attached, and no hypothesis stands in for a theorem — there are no
hypotheses beyond the ringed space and the open.

## Implementation notes

**Every monoidal structure is named by `@`-application, and `inferInstanceAs` is not used.** The
source and target of the two identity functors are the *same* type carrying different monoidal
structures, so instance search cannot tell which is meant. Worse, seating the structures with
`letI` and calling `inferInstanceAs` on the composite **fails**: the error is

```
failed to synthesize
  (SheafOfModules.Strict.toLocalizedMonoidal X.presheaf ⋯ ⋙ restrictModulesRingLocalized X U ⋙
      SheafOfModules.SliceRestriction.fromLocalizedMonoidal (SheafedSpace.restrict X ⋯).presheaf
        ⋯).Monoidal
```

because `Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal` is stated with the
strict structure at the `Stacks.SheafOfModules.Strict.monoidalCategory 𝒪 h𝒪` spelling while the
statement here applies it to `(X.sheaf).obj` and
`(Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property`; the two are definitionally equal —
the sheaf conditions involved are propositions — but have different discrimination-tree keys, so
a `letI` at one spelling is invisible to a goal at the other. Applying
`CategoryTheory.Functor.Monoidal.instComp` explicitly puts the crossing at the `:=`, where the
defeq check performs it. Two `MonoidalCategory` instances are still seated by `letI`, at the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf h` spelling of the ring
sheaf that `Strict.toLocalizedMonoidal` names in its type and instance search does not reach.

The underlying functor of the five-fold composite is `𝟭 ⋙ (𝟭 ⋙ (F ⋙ 𝟭) ⋙ 𝟭)`, which is
`F` definitionally — `Functor.comp` takes `obj` and `map` pointwise — so the ascribed type needs
no transport.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 00XB](https://stacks.math.columbia.edu/tag/00XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.RingedSpace

universe u

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u}) (U : Opens X)

/-- `Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing`, retyped between the type
synonyms carrying the localized monoidal structures of the source and target ringed spaces. It is
the same functor; only the spelling of its source and target differs. -/
abbrev restrictModulesRingLocalized :
    Stacks.SheafOfModules.SliceRestriction.localizedSrc X.presheaf
        (structureSheafRing X).property ⥤
      Stacks.SheafOfModules.SliceRestriction.localizedSrc
        (X.restrict U.isOpenEmbedding).presheaf
        (structureSheafRing (X.restrict U.isOpenEmbedding)).property :=
  Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U

/-- `Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidal`, read at the type-synonym
spelling of the localized monoidal structure. -/
@[instance_reducible]
def restrictModulesRingLocalizedMonoidal :
    (restrictModulesRingLocalized X U).Monoidal :=
  restrictModulesRing_monoidal X U

/-- **Restriction of sheaves of modules to an open subspace is monoidal for the strict monoidal
structure of Tag 01CA**, whose tensor product is the tensor product sheaf on the nose.

This is `Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidal`, which says the same for
the localized structure, conjugated on both sides by the identity functor between the strict and
localized structures (`Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal` and
`...fromLocalizedMonoidalMonoidal`). No coherence diagram is checked. -/
@[instance_reducible]
def restrictModulesRingStrictMonoidal :
    @Functor.Monoidal _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory (X.sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).property)) _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory ((X.restrict U.isOpenEmbedding).sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((X.restrict U.isOpenEmbedding).sheaf)).property))
      (Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
        (structureSheafRing X).property)) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (X.sheaf).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).property)
  letI : MonoidalCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (X.restrict U.isOpenEmbedding).presheaf
        (structureSheafRing (X.restrict U.isOpenEmbedding)).property)) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory ((X.restrict U.isOpenEmbedding).sheaf).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((X.restrict U.isOpenEmbedding).sheaf)).property)
  @Functor.Monoidal.instComp _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory (X.sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).property)) _ _ _ _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory ((X.restrict U.isOpenEmbedding).sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((X.restrict U.isOpenEmbedding).sheaf)).property))
      (Stacks.SheafOfModules.Strict.toLocalizedMonoidal X.presheaf
        (structureSheafRing X).property) _
      (Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal X.presheaf
        (structureSheafRing X).property)
    (@Functor.Monoidal.instComp _ _ _ _ _ _ _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory ((X.restrict U.isOpenEmbedding).sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((X.restrict U.isOpenEmbedding).sheaf)).property))
      (restrictModulesRingLocalized X U)
      (Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidal
        (X.restrict U.isOpenEmbedding).presheaf
        (structureSheafRing (X.restrict U.isOpenEmbedding)).property)
      (restrictModulesRingLocalizedMonoidal X U)
      (Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidalMonoidal
        (X.restrict U.isOpenEmbedding).presheaf
        (structureSheafRing (X.restrict U.isOpenEmbedding)).property))

/-- **Restriction of sheaves of modules to an open subspace of a ringed space is a monoidal
functor for `SheafOfModules.monoidalCategorySheafTensor` on each side** — that is, for the
monoidal structure whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`, which is
the one the complexes of Stacks 0FPT and hence the derived tensor product of Stacks 0FPB are
built on.

This is `Stacks.Cohomology.LeftDualPerfect.restrictModulesRingStrictMonoidal` conjugated on both
sides by the identity functor between the strict structure of Tag 01CA and the re-seated one,
which is monoidal in both directions because the two agree on every structural morphism
(`SheafOfModules.idMonoidalSheafTensorToStrict` and `...idMonoidalStrictToSheafTensor`).

It is the sheaf-level input of the derived-level shrinking step of Stacks 0FPD, conclusion (a);
it is a step of the proof and not a clause of the tag, so it carries no `@[stacks]` attribute. -/
@[instance_reducible]
def restrictModulesRing_monoidalSheafTensor :
    @Functor.Monoidal _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor
        (X.restrict U.isOpenEmbedding).sheaf)
      (Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U) :=
  @Functor.Monoidal.instComp _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf) _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory (X.sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).property)) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor
        (X.restrict U.isOpenEmbedding).sheaf) (𝟭 _) _
      (_root_.SheafOfModules.idMonoidalSheafTensorToStrict X.sheaf)
    (@Functor.Monoidal.instComp _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory (X.sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (X.sheaf)).property)) _ _
      ((Stacks.SheafOfModules.Strict.monoidalCategory ((X.restrict U.isOpenEmbedding).sheaf).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf ((X.restrict U.isOpenEmbedding).sheaf)).property))
      _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor
        (X.restrict U.isOpenEmbedding).sheaf)
      (Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U) (𝟭 _)
      (restrictModulesRingStrictMonoidal X U)
      (_root_.SheafOfModules.idMonoidalStrictToSheafTensor
        (X.restrict U.isOpenEmbedding).sheaf))

end Stacks.Cohomology.LeftDualPerfect

end
