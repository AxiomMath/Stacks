module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointModuleFiberStalk

/-!
# The site-point stalk of a sheaf of modules on a space is its topological stalk

Let `X` be a topological space and `x` a point of it.  Two stalk functors on sheaves of modules
over a sheaf of commutative rings on `X` are in use:

* `Stacks.Sheaves.StalkPullback.sheafStalk (Opens.pointGrothendieckTopology x)`, the fibre at the
  point of the site of opens attached to `x`, which is what the base-change interchange
  `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso` is stated about; and
* `AlgebraicGeometry.SheafOfModules.stalkFunctor`, the topological stalk, which is what the
  naive cotangent complex of a scheme is analysed with.

This file bridges them: the two functors agree up to the restriction of scalars along
`Opens.commRingFiberStalkHom`, and the stalk of a morphism of sheaves of commutative rings in the
site-point spelling, `Stacks.SitePointBaseChange.stalkRingHom`, is its topological stalk
conjugated by `Opens.pointFiberStalkIso`.  The interchange of extension of scalars with taking
stalks is then transported to the topological spelling.

## Main definitions

* `Opens.sheafStalkFunctorIso`: the site-point stalk functor on sheaves of modules is the
  topological stalk functor with scalars restricted along `Opens.commRingFiberStalkHom`.
* `Opens.extendScalarsStalkFunctorIso`: **the interchange of extension of scalars with taking
  topological stalks.**  For a morphism `b : B ⟶ C` of sheaves of commutative rings on `X`,
  taking the stalk at `x` carries extension of scalars of sheaves of modules along `b` to
  extension of scalars along the stalk of `b`.

## Main results

* `Opens.stalkRingHom_comp_pointFiberStalkHom`: the site-point stalk of a morphism of presheaves
  of commutative rings and its topological stalk agree under `Opens.pointFiberStalkHom`.
* `Opens.ofHom_stalkRingHom_eq`: the same, solved for the site-point stalk.

## Implementation notes

`Stacks.Sheaves.StalkPullback.sheafStalk Φ A h` is by definition
`Stacks.sheafModuleFiberOfCommRing Φ O` for `A = O.obj`, so `Opens.sheafStalkFunctorIso` is
`Opens.moduleFiberStalkFunctorIsoOfCommRing` read at the other spelling; the content of the
declaration is the identification of the two, which is what lets the two bodies of results be
composed.

Only the restatement `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso` of the
interchange is usable here, not `Stacks.SitePointBaseChange.extendScalarsSheafStalkNatIso`: the
latter forces the morphism universe of the site to equal the universe of the sheaves, and the
site of opens of `X : TopCat.{u}` has `Opens X : Type u` with morphisms in `Prop`.

The two restrictions of scalars in the statement of `Opens.extendScalarsStalkFunctorIso` carry
`(R := Stacks.ringFiber (Opens.pointGrothendieckTopology x) _)` explicitly.  Without it the ring
over which the composite is taken is elaborated as the image of the fibre under
`forget₂ CommRingCat RingCat`, on whose carrier the `CommRing` instance that
`ModuleCat.extendScalars` needs is not found, even though it is the same carrier.

## References

* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace Opens

variable {X : TopCat.{u}} (x : X)

/-! ### The stalk of a morphism of sheaves of commutative rings -/

/-- **The site-point stalk of a morphism of presheaves of commutative rings is its topological
stalk**, read through the identification `Opens.pointFiberStalkHom` of the fibre at the point of
the site of opens attached to `x` with the stalk at `x`.

This is `Opens.pointFiberStalkIso_natural` at `CommRingCat`, in the spelling
`Stacks.SitePointBaseChange.stalkRingHom` that the base-change interchange for sheaves of
modules uses. -/
theorem stalkRingHom_comp_pointFiberStalkHom
    {F G : X.Presheaf CommRingCat.{u}} (θ : F ⟶ G) :
    CommRingCat.ofHom
          (Stacks.SitePointBaseChange.stalkRingHom θ (pointGrothendieckTopology x)) ≫
        pointFiberStalkHom x G =
      pointFiberStalkHom x F ≫ (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map θ :=
  pointFiberStalkIso_natural x θ

/-- The site-point stalk of a morphism of presheaves of commutative rings is its topological
stalk conjugated by `Opens.pointFiberStalkIso`. -/
theorem ofHom_stalkRingHom_eq {F G : X.Presheaf CommRingCat.{u}} (θ : F ⟶ G) :
    CommRingCat.ofHom
        (Stacks.SitePointBaseChange.stalkRingHom θ (pointGrothendieckTopology x)) =
      (pointFiberStalkHom x F ≫ (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map θ) ≫
        pointFiberStalkInv x G :=
  ((pointFiberStalkIso x G).eq_comp_inv).mpr (stalkRingHom_comp_pointFiberStalkHom x θ)

/-! ### The stalk functor on sheaves of modules -/

variable (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **The site-point stalk functor on sheaves of modules over a sheaf of commutative rings on a
space is the topological stalk functor**, with scalars restricted along
`Opens.commRingFiberStalkHom`.

The site-point stalk functor of `Stacks.Sheaves.StalkPullback.sheafStalk` is by definition
`Stacks.sheafModuleFiberOfCommRing`, so this is
`Opens.moduleFiberStalkFunctorIsoOfCommRing` read at that spelling; stating it is what allows
results about the one to be composed with results about the other. -/
def sheafStalkFunctorIso :
    Stacks.Sheaves.StalkPullback.sheafStalk (pointGrothendieckTopology x) O.obj
        (Stacks.commRingSheafToRingSheaf O).property ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (Stacks.commRingSheafToRingSheaf O) x ⋙
        ModuleCat.restrictScalars.{u} (commRingFiberStalkHom x O).hom :=
  moduleFiberStalkFunctorIsoOfCommRing x O

/-! ### Extension of scalars and the topological stalk -/

variable (B C : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **The interchange of extension of scalars with taking topological stalks.**  For a morphism
`b : B ⟶ C` of sheaves of commutative rings on `X`, taking the stalk at `x` carries extension of
scalars of sheaves of modules along `b` (Stacks 03CZ) to extension of scalars along the stalk of
`b`.

This is `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso` at the point of the site of
opens attached to `x`, transported along `Opens.sheafStalkFunctorIso` to the topological stalk
functor on both sides. -/
def extendScalarsStalkFunctorIso (b : B ⟶ C) :
    Stacks.Sheaves.RingedToposModules.extendScalars (Opens.grothendieckTopology X) b.hom
          (Stacks.commRingSheafToRingSheaf B).property
          (Stacks.commRingSheafToRingSheaf C).property ⋙
        AlgebraicGeometry.SheafOfModules.stalkFunctor (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (Stacks.commRingSheafToRingSheaf B) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
            (commRingFiberStalkHom x B).hom) ⋙
        ModuleCat.extendScalars
          (Stacks.SitePointBaseChange.stalkRingHom b.hom (pointGrothendieckTopology x)) :=
  Functor.isoWhiskerLeft _ (sheafStalkFunctorIso x C).symm ≪≫
    Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso (pointGrothendieckTopology x) b.hom
      (Stacks.commRingSheafToRingSheaf B).property
      (Stacks.commRingSheafToRingSheaf C).property ≪≫
    Functor.isoWhiskerRight (sheafStalkFunctorIso x B) (ModuleCat.extendScalars _)

end Opens

end

end
