module

public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointSheafStalkExtendScalarsComplexes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The topological stalk of the counit of extension and restriction of scalars, on elements

Let `X` be a topological space, `x` a point of it and `b : B ⟶ C` a morphism of sheaves of
commutative rings on `X`.  `Opens.stalkFunctor_map_towerCounit_eq` computes the stalk at `x` of
the counit `C ⊗_B M_B ⟶ M` of Stacks 03CZ as a composite of three maps: the interchange
`Opens.extendScalarsStalkFunctorIso` of extension of scalars with taking stalks, extension of
scalars applied to the restriction-of-scalars comparison `Opens.restrictScalarsStalkFunctorIso`,
and the counit of `ModuleCat.extendRestrictScalarsAdj`.  This file reads that composite on
elements: the stalk of the counit sends the pure tensor `c ⊗ m` of
`Opens.stalkTowerExtendScalarsXIso` to `c • m`.

The one thing to check is that the middle map is the identity.  It is: the
restriction-of-scalars comparison of
`Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso` is the identity on carriers, and
the two comparisons `Opens.sheafStalkFunctorIso` conjugating it — for `B` and for `C` — are both
`Opens.pointFiberStalkHom` of the *same* presheaf of abelian groups, since neither restriction of
scalars nor the choice of the sheaf of rings changes the underlying presheaf of a sheaf of
modules.

## Main results

* `Opens.sheafStalkFunctorIso_hom_app_apply`: the comparison of the site-point stalk functor
  with the topological one is `Opens.pointFiberStalkHom` on elements.
* `Opens.restrictScalarsStalkFunctorIso_hom_app_apply`: **the restriction-of-scalars comparison
  is the identity on elements.**
* `ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul`: the counit of extension and
  restriction of scalars of modules is `c ⊗ m ↦ c • m`, the form
  `ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul` records only at `c = 1`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.RingedToposModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace ModuleCat

/-- **The counit of extension and restriction of scalars of modules is `c ⊗ m ↦ c • m`.**  It is
`S`-linear and sends `1 ⊗ m` to `m`
(`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul`), and `c ⊗ m` is `c • (1 ⊗ m)`
by `ModuleCat.ExtendScalars.smul_tmul`. -/
@[ega "III 6.3.10" "partial"]
theorem extendRestrictScalarsAdj_counit_app_apply_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} S) (c : S) (m : (restrictScalars f).obj M) :
    (extendRestrictScalarsAdj f).counit.app M (c ⊗ₜ[R, f] m) = c • (m : ToType M) := by
  have h := ModuleCat.ExtendScalars.smul_tmul f (M := (restrictScalars f).obj M) c 1 m
  rw [mul_one] at h
  refine Eq.trans (congrArg (fun t => (extendRestrictScalarsAdj f).counit.app M t) h.symm) ?_
  refine Eq.trans (((extendRestrictScalarsAdj f).counit.app M).hom.map_smul c _) ?_
  exact congrArg (fun t : ToType M => c • t)
    (extendRestrictScalarsAdj_counit_app_apply_one_tmul f M m)

end ModuleCat

namespace Opens

variable {X : TopCat.{u}} (x : X)
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (B C : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (b : B ⟶ C)

/-- **The comparison of the site-point stalk functor with the topological one is
`Opens.pointFiberStalkHom` on elements**: the comparison of the fibre of the underlying presheaf
of abelian groups of the sheaf of modules with its stalk.  In particular it does not depend on
the sheaf of rings the module is taken over. -/
theorem sheafStalkFunctorIso_hom_app_apply
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B))
    (m : (Stacks.Sheaves.StalkPullback.sheafStalk (pointGrothendieckTopology x) B.obj
      (Stacks.commRingSheafToRingSheaf B).property).obj M) :
    (sheafStalkFunctorIso x B).hom.app M m = pointFiberStalkHom x M.val.presheaf m := rfl

/-- The restriction-of-scalars comparison, evaluated on an element coming from the comparison of
the site-point stalk functor with the topological one for `B`: the comparison for `B` cancels
against its inverse, the middle map is the identity on carriers, and the comparison for `C` is
`Opens.pointFiberStalkHom` of the same presheaf. -/
theorem restrictScalarsStalkFunctorIso_hom_app_sheafStalkFunctorIso_hom_app
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C))
    (η : (Stacks.Sheaves.StalkPullback.sheafStalk (pointGrothendieckTopology x) B.obj
      (Stacks.commRingSheafToRingSheaf B).property).obj
        ((SheafOfModules.restrictScalars.{u}
          (commRingSheafMap (Opens.grothendieckTopology X) b.hom
            (Stacks.commRingSheafToRingSheaf B).property
            (Stacks.commRingSheafToRingSheaf C).property)).obj M)) :
    (restrictScalarsStalkFunctorIso x B C b).hom.app M
        ((sheafStalkFunctorIso x B).hom.app _ η) =
      pointFiberStalkHom x M.val.presheaf
        ((sheafStalkFunctorIso x B).inv.app _ ((sheafStalkFunctorIso x B).hom.app _ η)) := rfl

/-- **The restriction-of-scalars comparison on stalks is the identity on elements.**  The stalk
at `x` of a sheaf of `C`-modules and the stalk of the same sheaf read as a sheaf of `B`-modules
have the same elements, and the comparison between them is the identity map. -/
theorem restrictScalarsStalkFunctorIso_hom_app_apply
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C))
    (ξ : (SheafOfModules.restrictScalars.{u}
            (commRingSheafMap (Opens.grothendieckTopology X) b.hom
              (Stacks.commRingSheafToRingSheaf B).property
              (Stacks.commRingSheafToRingSheaf C).property) ⋙
          (AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x B).hom)).obj M) :
    (restrictScalarsStalkFunctorIso x B C b).hom.app M ξ = ξ := by
  obtain ⟨η, hη⟩ : ∃ η, (sheafStalkFunctorIso x B).hom.app
      ((SheafOfModules.restrictScalars.{u}
        (commRingSheafMap (Opens.grothendieckTopology X) b.hom
          (Stacks.commRingSheafToRingSheaf B).property
          (Stacks.commRingSheafToRingSheaf C).property)).obj M) η = ξ :=
    ⟨(sheafStalkFunctorIso x B).inv.app _ ξ, by
      rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app, ConcreteCategory.id_apply]⟩
  have hinv : (sheafStalkFunctorIso x B).inv.app _
      ((sheafStalkFunctorIso x B).hom.app _ η) = η := by
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app, ConcreteCategory.id_apply]
  refine Eq.trans (congrArg (fun ζ => (restrictScalarsStalkFunctorIso x B C b).hom.app M ζ)
    hη.symm) ?_
  refine Eq.trans
    (restrictScalarsStalkFunctorIso_hom_app_sheafStalkFunctorIso_hom_app x B C b M η) ?_
  refine Eq.trans (congrArg (fun ζ => pointFiberStalkHom x M.val.presheaf ζ) hinv) ?_
  exact hη

/-! ### The stalk of the counit, evaluated -/

/-- **The topological stalk of the counit of Stacks 03CZ, read through the interchange.**  For an
element `ξ` of the base change of the stalk, the stalk at `x` of the counit `C ⊗_B M_B ⟶ M`
applied to the image of `ξ` under the interchange is the multiplication map applied to the image
of `ξ` under the restriction-of-scalars comparison.

This is `Opens.stalkFunctor_map_towerCounit_eq` with the interchange cancelled against its
inverse. -/
theorem stalkFunctor_map_towerCounit_apply
    (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf C))
    (ξ : (ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x B).hom).obj
          ((SheafOfModules.restrictScalars.{u}
            (commRingSheafMap (Opens.grothendieckTopology X) b.hom
              (Stacks.commRingSheafToRingSheaf B).property
              (Stacks.commRingSheafToRingSheaf C).property)).obj M))) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).map
        ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
          (Opens.grothendieckTopology X) B C b).counit.app M)
        ((extendScalarsStalkFunctorIso x B C b).inv.app
          ((SheafOfModules.restrictScalars.{u}
            (commRingSheafMap (Opens.grothendieckTopology X) b.hom
              (Stacks.commRingSheafToRingSheaf B).property
              (Stacks.commRingSheafToRingSheaf C).property)).obj M) ξ) =
      (ModuleCat.extendRestrictScalarsAdj
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).counit.app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.commRingSheafToRingSheaf C) x ⋙
              ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x C).hom).obj M)
        ((ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).map
          ((restrictScalarsStalkFunctorIso x B C b).hom.app M) ξ) := by
  refine Eq.trans (congrArg (fun ψ => ψ
    ((extendScalarsStalkFunctorIso x B C b).inv.app _ ξ))
    (stalkFunctor_map_towerCounit_eq x B C b M)) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine congrArg (fun ζ =>
      (ModuleCat.extendRestrictScalarsAdj
        (Stacks.SitePointBaseChange.stalkRingHom b.hom
          (pointGrothendieckTopology x))).counit.app _ ζ) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine congrArg (fun ζ => (ModuleCat.extendScalars
      (Stacks.SitePointBaseChange.stalkRingHom b.hom
        (pointGrothendieckTopology x))).map
      ((restrictScalarsStalkFunctorIso x B C b).hom.app M) ζ) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ξ)
    ((extendScalarsStalkFunctorIso x B C b).inv_hom_id_app _)) ?_
  exact ConcreteCategory.id_apply _

end Opens

end

end
