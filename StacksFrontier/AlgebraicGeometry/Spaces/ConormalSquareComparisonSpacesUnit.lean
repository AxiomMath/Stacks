module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquareComparisonUnit
public import StacksFrontier.CategoryTheory.SquareTransportConormal

/-!
# The spaces-side square comparison of the conormal module, read at the structure sheaf

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonUnit.lean` proves the ringed-space
half of the comparison that part (2) of [Stacks Project, Tag 04G2] turns on:
`Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit`, which says that the
ringed-space square comparison of [Stacks Project, Tag 01R4] carries one composite of "pullback
of regular functions" round a commutative square to the other.  This file proves the mirror of
that statement on the small étale site of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.squarePullbackCompIso_hom`,
  `AlgebraicGeometry.Space.squarePullbackCompIso_hom_app`: the square comparison
  `AlgebraicGeometry.Space.squarePullbackCompIso` written out as the composition comparison of
  [Stacks Project, Tag 03LU] on each side of the square and the transport along the
  commutativity of the square in between.
* `AlgebraicGeometry.Space.squarePullbackCompIso_hom_app_eqToHom`: the same reading with the
  middle factor already respelled as a plain transport of the two objects, along an equality
  supplied as an argument, so that no consumer has to convert the
  `CategoryTheory.NatTrans.app` of an `eqToHom` of inverse-image functors.
* `AlgebraicGeometry.Space.eqToHom_app_unit_comp_structureModulePullbackMap`: the transport of
  `AlgebraicGeometry.Space.structureModulePullbackMap` along an equality of morphisms, read at
  the structure sheaf in the spelling that `structureModulePullbackMap` itself uses.
* `AlgebraicGeometry.Space.squarePullbackCompIso_hom_comp_structureModulePullbackMap`: **the
  spaces-side square comparison at the unit module** — going round the square by `f` and then
  `i`, the composite `f^*(i')^*𝒪_{X'} ⟶ f^*𝒪_{Z'} ⟶ 𝒪_Z` of the two maps
  `AlgebraicGeometry.Space.structureModulePullbackMap` of pullback of regular functions is, going
  round it by `g` and then `i`, the comparison `AlgebraicGeometry.Space.squarePullbackCompIso`
  followed by `i^*g^*𝒪_{X'} ⟶ i^*𝒪_X ⟶ 𝒪_Z`.

## Route

The proof is the one the ringed-space half uses, with the three spaces-side inputs in place of
the ringed-space ones: the composition law
`AlgebraicGeometry.Space.structureModulePullbackMap_comp` once on each side of the square, the
transport along the commutativity of the square in between, and the split
`AlgebraicGeometry.Space.squarePullbackCompIso_hom` of the comparison into its three factors.
All the associativity is in `CategoryTheory.eq_square_comp_of_cancel`, which is stated in an
arbitrary category.

## Implementation notes

Two measurements decide the shape of this file, and both were made declaration by declaration,
each with its own budget.

**The statement is made at `AlgebraicGeometry.Space.squarePullbackCompIso`, not at
`AlgebraicGeometry.Space.conormalPullbackCompIso`.**  The two comparisons are built by the same
three-factor formula; the difference is that `conormalPullbackCompIso` takes an
`AlgebraicGeometry.Space.ClosedSubspaces` and writes the space it is a closed subspace of as the
anonymous constructor `(⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)`, while
`squarePullbackCompIso` takes the four spaces and the four morphisms of the square as plain
variables.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonUnit.lean` record that the assembly
below is a kernel deterministic timeout in the anonymous-constructor spelling: the anonymous
constructor is what lets the kernel's conversion check take its first step, after which it
reduces `AlgebraicGeometry.Space.modulePullback` towards its construction by sheafification.
Nothing of part (2) of [Stacks Project, Tag 04G2] needs the other spelling:
`AlgebraicGeometry.Space.conormalMapOfImmersions`, which is where the tag's hypotheses live, is
built from `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, whose middle factor is
`squarePullbackCompIso`.

**Every occurrence of the structure sheaf is written
`CategoryTheory.SheafOfModules.unit (AlgebraicGeometry.Space.structureRingSheaf B S hS X')`, and
never `AlgebraicGeometry.Space.structureUnitModule`.**  The two are an `abbrev` and its body, so
they are definitionally equal; but the equation between the two spellings of a single morphism,

```
(modulePullbackCompIso B S hS f i').inv.app (structureUnitModule B S hS X') =
  (modulePullbackCompIso B S hS f i').inv.app (SheafOfModules.unit (structureRingSheaf B S hS X'))
```

elaborates by `rfl` and is then a **kernel** deterministic timeout, while every statement of this
file in the second spelling alone is free.  `attribute [local irreducible]` cannot help — it
keeps the elaborator off that route, which is why the elaboration succeeds, but no attribute
reaches the kernel.  The second spelling is the one
`AlgebraicGeometry.Space.structureModulePullbackMap` carries in its own type and the one
`AlgebraicGeometry.Space.structureModulePullbackMap_comp` is stated at, so it is the one kept
here; `AlgebraicGeometry.Space.eqToHom_app_unit_comp_structureModulePullbackMap` is the transport
restated at it, proved from scratch rather than from its `structureUnitModule` twin in
`ConormalSquareComparisonUnit.lean` for exactly that reason.

`AlgebraicGeometry.Space.modulePullback` and `AlgebraicGeometry.Space.modulePullbackCompIso` are
made locally irreducible, as they are in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreement.lean`: unfolding the inverse
image to its construction by sheafification, or the comparison to
`CategoryTheory.Adjunction.leftAdjointUniq`, does not terminate, and nothing here needs it.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

-- See the implementation notes: these keep the elaborator from unfolding the inverse image and
-- the composition comparison to their constructions, which does not terminate.
attribute [local irreducible] modulePullback modulePullbackCompIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-- **`AlgebraicGeometry.Space.squarePullbackCompIso` written out**, as the composition
comparison of [Stacks Project, Tag 03LU] on each side of the square and the transport along the
commutativity of the square in between. -/
theorem squarePullbackCompIso_hom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') :
    (squarePullbackCompIso B S hS i i' f g hsq).hom =
      (modulePullbackCompIso B S hS f i').hom ≫
        eqToHom (congrArg (fun h : Z ⟶ X' => modulePullback B S hS h) hsq.symm) ≫
          (modulePullbackCompIso B S hS i g).inv := by
  rw [squarePullbackCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]

/-- `AlgebraicGeometry.Space.squarePullbackCompIso_hom` read at one module. -/
theorem squarePullbackCompIso_hom_app (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (M : Modules.{u, u} B S hS X'.1 X'.2) :
    (squarePullbackCompIso B S hS i i' f g hsq).hom.app M =
      (modulePullbackCompIso B S hS f i').hom.app M ≫
        (eqToHom (congrArg (fun h : Z ⟶ X' => modulePullback B S hS h) hsq.symm)).app M ≫
          (modulePullbackCompIso B S hS i g).inv.app M :=
  (NatTrans.congr_app (squarePullbackCompIso_hom B S hS i i' f g hsq) M).trans
    (natTrans_comp_comp_app _ _ _ M)

/-- **`AlgebraicGeometry.Space.squarePullbackCompIso` read at one module, with its middle factor
already a plain transport of the two objects** rather than the `CategoryTheory.NatTrans.app` of an
`eqToHom` of functors, the transport being taken along an equality `hΦ` supplied as an argument.

That the respelling is the **statement** of a declaration of its own, proved here at plain
variables, is what makes the chain this serves affordable.  `.app` of an
`eqToHom` of two `AlgebraicGeometry.Space.modulePullback` functors is a projection out of a stuck
`Eq.rec`, so the kernel cannot take it and unfolds the inverse image — a left adjoint built by
sheafification — instead; `attribute [local irreducible]` does not reach the kernel.  Consuming
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_app` at a geometric instantiation in any way
that leaves that factor in a term the kernel must convert is therefore a kernel deterministic
timeout — including rewriting it into the goal together with `CategoryTheory.eqToHom_app` and then
applying a generic lemma, which elaborates and is then rejected.  Here, where the four spaces and
the four morphisms of the square are variables, the same respelling is free, and a consumer
instantiating this statement never sees the factor at all.

Likewise, the proof must not be `rw [squarePullbackCompIso_hom_app, eqToHom_app]`.  That
is a **kernel deterministic timeout even at these variables**, because the rewrite's closing `rfl`
compares the two `eqToHom` terms with the middle factor still present in the motive.  Going
through `Stacks.CategoryTheory.reading_eqToHom`, which does the respelling in a generic category
with no functor in sight, is free.

The consumer this shape is designed for is the hypothesis `hΞ` of
`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso`, which
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_squarePullbackCompIso` proves
from this statement; the section "Where the obstruction was, and what removed it" of the module
documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareTransportAgreement.lean` records what else
that assembly needed — namely that no morphism named in two spellings may be shared between two
of its hypotheses. -/
theorem squarePullbackCompIso_hom_app_eqToHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (M : Modules.{u, u} B S hS X'.1 X'.2)
    (hΦ : (modulePullback B S hS (f ≫ i')).obj M = (modulePullback B S hS (i ≫ g)).obj M) :
    (squarePullbackCompIso B S hS i i' f g hsq).hom.app M =
      (modulePullbackCompIso B S hS f i').hom.app M ≫
        eqToHom hΦ ≫ (modulePullbackCompIso B S hS i g).inv.app M :=
  Stacks.CategoryTheory.reading_eqToHom M
    (squarePullbackCompIso_hom_app B S hS i i' f g hsq M) hΦ

/-- **The comparison `p^*𝒪 ⟶ 𝒪` is transported along an equality of morphisms.**  For `e : p = q`
the transport `p^* ⟶ q^*` followed by the comparison of `q` is the comparison of `p`.

This is `AlgebraicGeometry.Space.eqToHom_app_comp_structureModulePullbackMap` with the structure
sheaf written as `CategoryTheory.SheafOfModules.unit` of the structure ring sheaf rather than as
`AlgebraicGeometry.Space.structureUnitModule`.  The implementation notes of this file record why
the two spellings cannot be bridged on this chain and why this one is the one kept. -/
theorem eqToHom_app_unit_comp_structureModulePullbackMap {W Y : AlgebraicSpaces B S hS}
    {p q : W ⟶ Y} (e : p = q) :
    (eqToHom (congrArg (fun h : W ⟶ Y ↦ modulePullback B S hS h) e)).app
          (SheafOfModules.unit (structureRingSheaf B S hS Y)) ≫
        structureModulePullbackMap B S hS q =
      structureModulePullbackMap B S hS p := by
  subst e
  exact Category.id_comp _

/-- **The spaces-side square comparison of part (2) of [Stacks Project, Tag 04G2], read at the
structure sheaf.**  Going round the square by `f` and then `i`, the composite
`f^*(i')^*𝒪_{X'} ⟶ f^*𝒪_{Z'} ⟶ 𝒪_Z` of the two maps
`AlgebraicGeometry.Space.structureModulePullbackMap` of pullback of regular functions is, going
round it by `g` and then `i`, the comparison `AlgebraicGeometry.Space.squarePullbackCompIso`
followed by `i^*g^*𝒪_{X'} ⟶ i^*𝒪_X ⟶ 𝒪_Z`.

This is the mirror of
`Stacks.ClosedImmersion.pullbackCompIso_hom_comp_modulePullbackUnitToUnit`, and the proof is the
same: the composition law `AlgebraicGeometry.Space.structureModulePullbackMap_comp` once on each
side of the square, with the transport
`AlgebraicGeometry.Space.eqToHom_app_unit_comp_structureModulePullbackMap` along the
commutativity of the square in between. -/
theorem squarePullbackCompIso_hom_comp_structureModulePullbackMap (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') :
    (modulePullback B S hS f).map (structureModulePullbackMap B S hS i') ≫
        structureModulePullbackMap B S hS f =
      (squarePullbackCompIso B S hS i i' f g hsq).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X')) ≫
        (modulePullback B S hS i).map (structureModulePullbackMap B S hS g) ≫
          structureModulePullbackMap B S hS i := by
  have hsplit := squarePullbackCompIso_hom_app B S hS i i' f g hsq
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
  have hig := structureModulePullbackMap_comp B S hS i g
  have hfi := structureModulePullbackMap_comp B S hS f i'
  have htr := eqToHom_app_unit_comp_structureModulePullbackMap B S hS hsq.symm
  have hcancel := Iso.hom_inv_id_app (modulePullbackCompIso B S hS f i')
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
  exact Eq.symm (Eq.trans (eq_whisker hsplit _)
    (eq_square_comp_of_cancel _ _ _ _ _ _ _ _ hcancel hig htr hfi).symm)

end AlgebraicGeometry.Space

end
