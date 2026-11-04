module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ext sheaves commute with restriction to an open

Let `(X, O_X)` be a ringed space, let `U ⊆ X` be open and let `K`, `L` be objects of `D(O_X)`.
Restriction to the opens contained in `U` carries the Ext sheaf `SheafExt^n(K, L)` to the Ext
sheaf `SheafExt^n(K|_U, L|_U)` of the restrictions:

```
SheafExt^n(K, L)|_U = SheafExt^n(K|_U, L|_U).
```

This is the cohomology-sheaf form of **Stacks 08DL**, whose own statement is the one about the
derived internal Hom, `RSheafHom(K, L)|_U = RSheafHom(K|_U, L|_U)`. The passage from the one to
the other is that restriction of sheaves of modules to a slice site is exact, so it commutes
with the cohomology of a complex.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafExtRestrictionIso`: the comparison isomorphism
  `SheafExt^n(K, L)|_U ≅ SheafExt^n(K|_U, L|_U)`.

## Main results

* `Stacks.SheafOfModules.derivedSheafExtRestrictionIso_hom`: the comparison written out as a
  composite of the two isomorphisms it is built from.
* `Stacks.SheafOfModules.derivedSheafExtRestrictionIso_natural_left` and
  `Stacks.SheafOfModules.derivedSheafExtRestrictionIso_natural_right`: it is natural in each of
  the two variables. This is what makes it *the* comparison rather than an unspecified
  isomorphism of the two sheaves.

## Implementation notes

The target is spelled with `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` of the slice
site rather than with `Stacks.SheafOfModules.derivedSheafExt`, because the latter is defined for
a ringed *space* and the opens contained in `U` form a slice site, not the site of opens of a
space. `Stacks.SheafOfModules.derivedSheafExt` of the space `X` is the same construction for
`Stacks.SheafOfModules.ringedSite` of `X`, by definition, so the two sides of the comparison are
instances of one bifunctor read at two sites.

Nothing here is re-proved. The comparison is the composite of two existing isomorphisms:
`Stacks.Homology.derivedHomologyIso`, which says an exact additive functor commutes with the
cohomology functor on the derived category, instantiated at the restriction functor; and
`Stacks.SheafOfModules.derivedSheafHomRestrictionIso`, which is Stacks 08DL itself, under the
cohomology functor. Exactness of the restriction functor is not proved either: it is the pair of
hypotheses `PreservesFiniteLimits` and `PreservesFiniteColimits` that
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens` already carries,
and which are what make `Stacks.SheafOfModules.derivedRestrict` exist in the first place.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]

/-- Sheaves of `O_X`-modules on a ringed space form a Grothendieck abelian category, which is
what supplies the derived category used below. -/
local instance isGrothendieckAbelian_structureSheafModules' :
    IsGrothendieckAbelian.{u} (StructureSheafModules Rc) :=
  _root_.SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheaf Rc)

/-- The Ext sheaves of the slice site of the opens contained in `U`: the degree-`n` cohomology
sheaf of the derived internal Hom of that site. This is the same construction as
`Stacks.SheafOfModules.derivedSheafExt`, read at the slice site rather than at the site of opens
of a space. -/
@[ega "0 12.3.1", sga "4 V 6.0" "6.0.1, special case"]
abbrev derivedSheafExtOver
    (K L : DerivedCategory (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U))) (n : ℤ) :
    _root_.SheafOfModules.{u} ((structureSheaf Rc).over U) :=
  (DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).obj
    (((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).obj (op K)).obj L)

/-- **Ext sheaves commute with restriction to an open.** For objects `K`, `L` of `D(O_X)` and an
integer `n`, restricting the Ext sheaf `SheafExt^n(K, L)` to the opens contained in `U` gives the
Ext sheaf `SheafExt^n(K|_U, L|_U)` of the restrictions.

It is the cohomology-sheaf form of Stacks 08DL: the comparison of that tag, under the degree-`n`
cohomology functor, preceded by the comparison identifying the restriction of a cohomology sheaf
with the cohomology sheaf of the restriction, restriction being exact.

This consequence of [stacks 08DL] is not registered under the tag, which is registered on
`Stacks.SheafOfModules.derivedSheafHomRestrictionIso`. -/
def derivedSheafExtRestrictionIso (K L : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).obj (derivedSheafExt Rc K L n) ≅
      derivedSheafExtOver Rc U ((derivedRestrict Rc U).obj K) ((derivedRestrict Rc U).obj L) n :=
  ((Stacks.Homology.derivedHomologyIso
        (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) n).app
      (((derivedSheafHom Rc).obj (op K)).obj L)).symm ≪≫
    (DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).mapIso
      (derivedSheafHomRestrictionIso Rc U K L)

/-- The comparison, spelled out: the inverse of the exactness comparison for the restriction
functor, followed by the degree-`n` cohomology of the comparison of Stacks 08DL. -/
theorem derivedSheafExtRestrictionIso_hom
    (K L : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    (derivedSheafExtRestrictionIso Rc U K L n).hom =
      (Stacks.Homology.derivedHomologyIso
            (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) n).inv.app
          (((derivedSheafHom Rc).obj (op K)).obj L) ≫
        (DerivedCategory.homologyFunctor
            (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map
          (derivedSheafHomRestrictionIso Rc U K L).hom :=
  rfl

/-- The comparison is natural in the contravariant variable: restricting the map of Ext sheaves
that `f : K' ⟶ K` induces gives the map induced by `f|_U`. -/
theorem derivedSheafExtRestrictionIso_natural_left
    {K K' L : DerivedCategory (StructureSheafModules Rc)} (f : K' ⟶ K) (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).map
          ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
            (((derivedSheafHom Rc).map f.op).app L)) ≫
        (derivedSheafExtRestrictionIso Rc U K' L n).hom =
      (derivedSheafExtRestrictionIso Rc U K L n).hom ≫
        (DerivedCategory.homologyFunctor
            (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map
          (((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).map
            ((derivedRestrict Rc U).map f).op).app ((derivedRestrict Rc U).obj L)) := by
  have hnat := (Stacks.Homology.derivedHomologyIso
    (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) n).inv.naturality
      (((derivedSheafHom Rc).map f.op).app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have key := congrArg
    (DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map
    (derivedSheafHomRestrictionIso_natural_left Rc U f (L := L))
  rw [derivedSheafExtRestrictionIso_hom, derivedSheafExtRestrictionIso_hom,
    ← Category.assoc, hnat, Category.assoc, Category.assoc]
  exact congrArg (fun z => (Stacks.Homology.derivedHomologyIso
      (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) n).inv.app
        (((derivedSheafHom Rc).obj (op K)).obj L) ≫ z)
    (((DerivedCategory.homologyFunctor
          (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map_comp _ _).symm.trans
      (key.trans ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map_comp _ _)))

/-- The comparison is natural in the covariant variable: restricting the map of Ext sheaves that
`g : L ⟶ L'` induces gives the map induced by `g|_U`. -/
theorem derivedSheafExtRestrictionIso_natural_right
    {K L L' : DerivedCategory (StructureSheafModules Rc)} (g : L ⟶ L') (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U).map
          ((DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
            (((derivedSheafHom Rc).obj (op K)).map g)) ≫
        (derivedSheafExtRestrictionIso Rc U K L' n).hom =
      (derivedSheafExtRestrictionIso Rc U K L n).hom ≫
        (DerivedCategory.homologyFunctor
            (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map
          (((RingedSite.derivedSheafHomBifunctor ((ringedSite Rc).over U)).obj
            (op ((derivedRestrict Rc U).obj K))).map ((derivedRestrict Rc U).map g)) := by
  have hnat := (Stacks.Homology.derivedHomologyIso
    (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) n).inv.naturality
      (((derivedSheafHom Rc).obj (op K)).map g)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have key := congrArg
    (DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map
    (derivedSheafHomRestrictionIso_natural_right Rc U g (K := K))
  rw [derivedSheafExtRestrictionIso_hom, derivedSheafExtRestrictionIso_hom,
    ← Category.assoc, hnat, Category.assoc, Category.assoc]
  exact congrArg (fun z => (Stacks.Homology.derivedHomologyIso
      (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) n).inv.app
        (((derivedSheafHom Rc).obj (op K)).obj L) ≫ z)
    (((DerivedCategory.homologyFunctor
          (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map_comp _ _).symm.trans
      (key.trans ((DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} ((structureSheaf Rc).over U)) n).map_comp _ _)))

end Stacks.SheafOfModules

end
