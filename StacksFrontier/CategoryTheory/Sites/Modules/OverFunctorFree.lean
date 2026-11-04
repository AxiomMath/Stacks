module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact

/-!
# Restriction to a slice preserves the unit and the free sheaves of modules

Let `R : Sheaf J RingCat.{u}` be a sheaf of rings on a site `C`. Restriction to the slice over
an object `x : C` is `SheafOfModules.overFunctor R x`, and extension along `f : x ⟶ y` between
slices is `SheafOfModules.overMap R f`. Mathlib records `SheafOfModules.overMapUnitIso`, which
says that `overMap R f` carries the unit to the unit, but has no analogue for `overFunctor`;
and it records `SheafOfModules.mapFreeIso`, which turns such a unit isomorphism into an
isomorphism on free sheaves of modules, but instantiates it at neither functor. This file
supplies the four missing identifications.

Each of the two unit isomorphisms is `Iso.refl`: the sections of `unit R` over an object `z`
are `R.obj.obj (op z)`, restriction along a functor of sites reindexes the sections, and the
reindexed presheaf of rings is by definition the sheaf of rings of the slice. The free
isomorphisms are then `mapFreeIso` applied to these, which is legitimate because
`overFunctor R x` and `overMap R f` are left adjoints
(`SheafOfModules.overFunctor_isLeftAdjoint` and the corresponding Mathlib instance for
`pushforward`) and so preserve the `I`-indexed coproduct defining `free I`.

The point of recording these as named declarations is that an inline `Iso.refl _` passed to
`mapFreeIso` has a type that only matches the goal after delta-unfolding `overFunctor`, which
defeats `rw` and `simp` and forces the use of `erw`. With the isomorphisms named, the
`@[reassoc]` lemmas `SheafOfModules.ιFree_mapFreeIso_hom` and
`SheafOfModules.map_ιFree_mapFreeIso_inv` apply by `rw` directly.

## Main results

* `SheafOfModules.overFunctorUnitIso`: `(overFunctor R x).obj (unit R) ≅ unit (R.over x)`.
* `SheafOfModules.overFunctorFreeIso`: `free I ≅ (overFunctor R x).obj (free I)`, over the
  sheaf of rings `R.over x` on the source.
* `SheafOfModules.overMapFreeIso`: `free I ≅ (overMap R f).obj (free I)`.
* `SheafOfModules.ιFree_overFunctorFreeIso_hom` and
  `SheafOfModules.ιFree_overMapFreeIso_hom`: the `@[reassoc]` compatibility of these
  isomorphisms with the inclusions `ιFree`, which is what the computations with them use.

## Implementation notes

The module universe is forced to be the ring universe `u`: `SheafOfModules.unit R` lives in
`SheafOfModules.{u} R`, and `SheafOfModules.free` is only available when the module universe is
the ring universe. This matches `SheafOfModules.overMapUnitIso`, which Mathlib also states at
`overMap.{u}`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

section Unit

/-- **Restriction to a slice carries the unit to the unit.** The sections of `unit R` over an
object `z` of `C` are the ring `R.obj.obj (op z)` viewed as a module over itself; restriction to
the slice over `x` reindexes these along `Over.forget x`, which is by definition the sheaf of
rings `R.over x`. This is the `overFunctor` analogue of
`SheafOfModules.overMapUnitIso`. -/
@[simps! +dsimpLhs]
noncomputable def overFunctorUnitIso (x : C) :
    (overFunctor.{u} R x).obj (unit R) ≅ unit (R.over x) :=
  Iso.refl _

end Unit

section OverFunctorFree

variable [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (x : C) [HasSheafify (J.over x) AddCommGrpCat.{u}]
  [(J.over x).WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u)

/-- **Restriction to a slice carries free sheaves of modules to free sheaves of modules.** The
free sheaf of modules on `I` is the `I`-indexed coproduct of copies of the unit; restriction to
a slice is a left adjoint, hence preserves that coproduct, and it carries the unit to the unit
by `SheafOfModules.overFunctorUnitIso`. -/
noncomputable def overFunctorFreeIso :
    free (R := R.over x) I ≅ (overFunctor.{u} R x).obj (free I) :=
  mapFreeIso (overFunctor.{u} R x) I (overFunctorUnitIso R x).symm

/-- The inclusion of the `i`-th summand into `free I` over the slice, followed by the
identification of `free I` with the restriction of `free I`, is the restriction of the `i`-th
inclusion. -/
@[reassoc]
lemma ιFree_overFunctorFreeIso_hom (i : I) :
    ιFree (R := R.over x) i ≫ (overFunctorFreeIso R x I).hom =
      (overFunctorUnitIso R x).inv ≫ (overFunctor.{u} R x).map (ιFree i) :=
  ιFree_mapFreeIso_hom _ _ _ _

/-- `SheafOfModules.ιFree_overFunctorFreeIso_hom` with the identity morphism
`(overFunctorUnitIso R x).inv` cancelled. This is the form that `rw` can use: the source of
`(overFunctor R x).map (ιFree i)` is only equal to `unit (R.over x)` after unfolding
`overFunctor`, so stating the lemma this way is what lets a rewrite in a goal mentioning
`unit (R.over x)` succeed without `erw`. -/
@[reassoc]
lemma ιFree_overFunctorFreeIso_hom' (i : I) :
    ιFree (R := R.over x) i ≫ (overFunctorFreeIso R x I).hom =
      (overFunctor.{u} R x).map (ιFree i) :=
  (ιFree_overFunctorFreeIso_hom R x I i).trans (Category.id_comp _)

end OverFunctorFree

section OverMapFree

variable [HasPullbacks C] {x y : C} (f : x ⟶ y)
  [HasSheafify (J.over y) AddCommGrpCat.{u}]
  [(J.over y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (J.over x) AddCommGrpCat.{u}]
  [(J.over x).WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u)

/-- **Extension between slices carries free sheaves of modules to free sheaves of modules.**
The same argument as for `SheafOfModules.overFunctorFreeIso`, using Mathlib's
`SheafOfModules.overMapUnitIso` on the unit. -/
noncomputable def overMapFreeIso :
    free (R := R.over x) I ≅ (overMap.{u} R f).obj (free I) :=
  mapFreeIso (overMap.{u} R f) I (overMapUnitIso f).symm

/-- The inclusion of the `i`-th summand into `free I` over the smaller slice, followed by the
identification of `free I` with the extension of `free I`, is the extension of the `i`-th
inclusion. -/
@[reassoc]
lemma ιFree_overMapFreeIso_hom (i : I) :
    ιFree (R := R.over x) i ≫ (overMapFreeIso R f I).hom =
      (overMapUnitIso f).inv ≫ (overMap.{u} R f).map (ιFree i) :=
  ιFree_mapFreeIso_hom _ _ _ _

/-- `SheafOfModules.ιFree_overMapFreeIso_hom` with the identity morphism
`(overMapUnitIso f).inv` cancelled, so that `rw` applies it to a goal mentioning
`unit (R.over x)` without `erw`. -/
@[reassoc]
lemma ιFree_overMapFreeIso_hom' (i : I) :
    ιFree (R := R.over x) i ≫ (overMapFreeIso R f I).hom =
      (overMap.{u} R f).map (ιFree i) :=
  (ιFree_overMapFreeIso_hom R f I i).trans (Category.id_comp _)

end OverMapFree

end SheafOfModules

end
