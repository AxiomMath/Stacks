module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointSheafStalkBridge
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentTowerConeMap

/-!
# The topological stalk of the counit of extension and restriction of scalars

Let `X` be a topological space, `x` a point of it, and `b : B ⟶ C` a morphism of sheaves of
commutative rings on `X`.  Extension of scalars along `b` is left adjoint to restriction of
scalars (Stacks 03CZ), and
`Stacks.SheafOfModules.towerExtendRestrictAdjunction` is that adjunction in the spelling the
naive cotangent complex of a tower consumes.

This file computes the stalk at `x` of the counit of that adjunction.  For a sheaf of
`C`-modules `M` the counit is `C ⊗_B M_B ⟶ M`, and its stalk is the multiplication map

`C_x ⊗_{B_x} M_x → M_x`,

read through `Opens.extendScalarsStalkFunctorIso` — the interchange of extension of scalars with
taking topological stalks — and through
`Opens.restrictScalarsStalkFunctorIso`, which is the comparison of the stalk of a restriction of
scalars with the restriction of scalars of the stalk.

## Main definitions

* `Opens.restrictScalarsStalkFunctorIso`: the stalk at `x` of a restriction of scalars of
  sheaves of modules is the restriction of scalars of the stalk, in the topological spelling.
  This is the square of right adjoints whose mate is `Opens.extendScalarsStalkFunctorIso`.

## Main results

* `Opens.mateEquiv_symm_restrictScalarsStalkFunctorIso`: **the interchange of extension of
  scalars with taking topological stalks is the mate of the restriction-of-scalars square.**
* `Opens.map_restrictScalarsStalkFunctorIso_comp_counit` and
  `Opens.stalkFunctor_map_counit_eq`: **the stalk of the counit of Stacks 03CZ is the
  multiplication map**, read through the interchange.
* `Opens.stalkFunctor_map_towerCounit_eq`: the same statement for
  `Stacks.SheafOfModules.towerExtendRestrictAdjunction`, which is the adjunction whose counit
  `Stacks.SheafOfModules.towerCounit` reads degreewise on complexes
  (`Stacks.SheafOfModules.towerCounit_f`).

## Implementation notes

Everything is deduced from the mate identification at a point of a general site,
`Stacks.Sheaves.StalkPullback.mateEquiv_symm_restrictScalarsSheafStalkNatIso`, by transporting
the unit square along the two comparisons `Opens.sheafStalkFunctorIso` of the site-point stalk
functor with the topological one.  That transport is
`CategoryTheory.unit_square_whisker`, and `Opens.extendScalarsStalkFunctorIso` and
`Opens.restrictScalarsStalkFunctorIso` are by construction exactly the whiskered squares it
produces, so no further comparison is needed.

`Stacks.SheafOfModules.towerExtendRestrictAdjunction (Opens.grothendieckTopology X) B C b` is
*definitionally* `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` along
`b.hom`: `Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.commRingSheafToRingSheaf` are the same abbreviation
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj`.  The universe instantiation is
`v := u`, `w := u`: the objects of `Opens X` for `X : TopCat.{u}` form a type in `Type u` and
`CategoryTheory.Preorder.smallCategory` puts its morphisms in `Type u` as well, so the module
universe `max u v w` of the tower is `u`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings

universe u

noncomputable section

namespace Opens

variable {X : TopCat.{u}} (x : X)
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (B C : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (b : B ⟶ C)

/-- **The stalk at `x` of a restriction of scalars of sheaves of modules is the restriction of
scalars of the stalk**, in the topological spelling: the square of right adjoints whose mate is
`Opens.extendScalarsStalkFunctorIso`.

It is `Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso` at the point of the site of
opens attached to `x`, transported along `Opens.sheafStalkFunctorIso` on both sides, in the same
shape in which `Opens.extendScalarsStalkFunctorIso` transports the interchange. -/
def restrictScalarsStalkFunctorIso :
    SheafOfModules.restrictScalars.{u}
          (commRingSheafMap (Opens.grothendieckTopology X) b.hom
            (Stacks.commRingSheafToRingSheaf B).property
            (Stacks.commRingSheafToRingSheaf C).property) ⋙
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf B) x ⋙
          ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x B).hom) ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom) ⋙
        ModuleCat.restrictScalars.{u}
          (Stacks.SitePointBaseChange.stalkRingHom b.hom (pointGrothendieckTopology x)) :=
  Functor.isoWhiskerLeft _ (sheafStalkFunctorIso x B).symm ≪≫
    Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso (pointGrothendieckTopology x)
      b.hom (Stacks.commRingSheafToRingSheaf B).property
      (Stacks.commRingSheafToRingSheaf C).property ≪≫
    Functor.isoWhiskerRight (sheafStalkFunctorIso x C) _

/-- The unit square in the topological spelling: the transport along
`Opens.sheafStalkFunctorIso` of the unit square at a point of a general site. -/
theorem unit_square_stalkFunctor
    (N : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) :
    (ModuleCat.extendRestrictScalarsAdj
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).unit.app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x B).hom).obj N) ≫
        (ModuleCat.restrictScalars.{u}
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).map
          ((extendScalarsStalkFunctorIso x B C b).inv.app N) =
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf B) x ⋙
          ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x B).hom).map
          ((extendRestrictScalarsAdjunction (Opens.grothendieckTopology X) b.hom
            (Stacks.commRingSheafToRingSheaf B).property
            (Stacks.commRingSheafToRingSheaf C).property).unit.app N) ≫
        (restrictScalarsStalkFunctorIso x B C b).hom.app
          ((extendScalars (Opens.grothendieckTopology X) b.hom
            (Stacks.commRingSheafToRingSheaf B).property
            (Stacks.commRingSheafToRingSheaf C).property).obj N) :=
  unit_square_whisker _ _ (sheafStalkFunctorIso x B) (sheafStalkFunctorIso x C) _ _
    (Stacks.Sheaves.StalkPullback.unit_square (pointGrothendieckTopology x) b.hom
      (Stacks.commRingSheafToRingSheaf B).property
      (Stacks.commRingSheafToRingSheaf C).property) N

/-- **The interchange of extension of scalars with taking topological stalks is the mate of the
restriction-of-scalars square.**  The inverse mate, under the adjunction of Stacks 03CZ for
sheaves of modules on `X` and for modules over the stalk of `b`, of
`Opens.restrictScalarsStalkFunctorIso` is `Opens.extendScalarsStalkFunctorIso` read
backwards. -/
theorem mateEquiv_symm_restrictScalarsStalkFunctorIso :
    (mateEquiv
          (extendRestrictScalarsAdjunction (Opens.grothendieckTopology X) b.hom
            (Stacks.commRingSheafToRingSheaf B).property
            (Stacks.commRingSheafToRingSheaf C).property)
          (ModuleCat.extendRestrictScalarsAdj
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x)))).symm
        (restrictScalarsStalkFunctorIso x B C b).hom =
      (extendScalarsStalkFunctorIso x B C b).inv :=
  mateEquiv_symm_eq_of_unit _ _ _ _ (unit_square_stalkFunctor x B C b)

/-- **The counit square.**  The restriction-of-scalars square, extended along the stalk of `b`
and followed by the multiplication map, is the interchange read backwards followed by the stalk
of the counit of Stacks 03CZ. -/
theorem map_restrictScalarsStalkFunctorIso_comp_counit
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C)) :
    (ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).map
          ((restrictScalarsStalkFunctorIso x B C b).hom.app M) ≫
        (ModuleCat.extendRestrictScalarsAdj
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).counit.app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf C) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).obj M) =
      (extendScalarsStalkFunctorIso x B C b).inv.app
          ((SheafOfModules.restrictScalars.{u}
            (commRingSheafMap (Opens.grothendieckTopology X) b.hom
              (Stacks.commRingSheafToRingSheaf B).property
              (Stacks.commRingSheafToRingSheaf C).property)).obj M) ≫
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf C) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).map
          ((extendRestrictScalarsAdjunction (Opens.grothendieckTopology X) b.hom
            (Stacks.commRingSheafToRingSheaf B).property
            (Stacks.commRingSheafToRingSheaf C).property).counit.app M) :=
  map_counit_comp_of_unit _ _ _ _ (unit_square_stalkFunctor x B C b) M

/-- **The topological stalk of the counit of Stacks 03CZ is the multiplication map.**  Read
through `Opens.extendScalarsStalkFunctorIso` and `Opens.restrictScalarsStalkFunctorIso`, the
stalk at `x` of the counit `C ⊗_B M_B ⟶ M` is the counit of
`ModuleCat.extendRestrictScalarsAdj`, which sends `a ⊗ m` to `a • m`
(`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul`). -/
theorem stalkFunctor_map_counit_eq
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).map
        ((extendRestrictScalarsAdjunction (Opens.grothendieckTopology X) b.hom
          (Stacks.commRingSheafToRingSheaf B).property
          (Stacks.commRingSheafToRingSheaf C).property).counit.app M) =
      ((extendScalarsStalkFunctorIso x B C b).hom.app
            ((SheafOfModules.restrictScalars.{u}
              (commRingSheafMap (Opens.grothendieckTopology X) b.hom
                (Stacks.commRingSheafToRingSheaf B).property
                (Stacks.commRingSheafToRingSheaf C).property)).obj M) ≫
          (ModuleCat.extendScalars
              (Stacks.SitePointBaseChange.stalkRingHom b.hom
                (pointGrothendieckTopology x))).map
            ((restrictScalarsStalkFunctorIso x B C b).hom.app M)) ≫
        (ModuleCat.extendRestrictScalarsAdj
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).counit.app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf C) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).obj M) := by
  rw [Category.assoc, map_restrictScalarsStalkFunctorIso_comp_counit, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp]

/-! ### The tower spelling -/

/-- The counit of `Stacks.SheafOfModules.towerExtendRestrictAdjunction` on the site of opens of
a space is the counit of `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`
along `b.hom`: the two adjunctions are the same term. -/
theorem towerExtendRestrictAdjunction_counit_app
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C)) :
    (Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
        (Opens.grothendieckTopology X) B C b).counit.app M =
      (extendRestrictScalarsAdjunction (Opens.grothendieckTopology X) b.hom
        (Stacks.commRingSheafToRingSheaf B).property
        (Stacks.commRingSheafToRingSheaf C).property).counit.app M :=
  rfl

/-- **The topological stalk of `Stacks.SheafOfModules.towerCounit` in each degree.**  The stalk
at `x` of the counit of `Stacks.SheafOfModules.towerExtendRestrictAdjunction` at a sheaf of
`C`-modules `M` is the multiplication map `C_x ⊗_{B_x} M_x → M_x`, read through
`Opens.extendScalarsStalkFunctorIso`.

By `Stacks.SheafOfModules.towerCounit_f` the degree-`i` component of
`Stacks.SheafOfModules.towerCounit` is this counit at `K.X i`, so this computes the stalk of
that chain map degreewise. -/
theorem stalkFunctor_map_towerCounit_eq
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).map
        ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology X) B C b).counit.app M) =
      ((extendScalarsStalkFunctorIso x B C b).hom.app
            ((SheafOfModules.restrictScalars.{u}
              (commRingSheafMap (Opens.grothendieckTopology X) b.hom
                (Stacks.commRingSheafToRingSheaf B).property
                (Stacks.commRingSheafToRingSheaf C).property)).obj M) ≫
          (ModuleCat.extendScalars
              (Stacks.SitePointBaseChange.stalkRingHom b.hom
                (pointGrothendieckTopology x))).map
            ((restrictScalarsStalkFunctorIso x B C b).hom.app M)) ≫
        (ModuleCat.extendRestrictScalarsAdj
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).counit.app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf C) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).obj M) :=
  stalkFunctor_map_counit_eq x B C b M

end Opens

end

end
