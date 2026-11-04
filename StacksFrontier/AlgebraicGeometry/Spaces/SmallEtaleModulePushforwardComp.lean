module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso

/-!
# The structure map of a composite, at the level of sheaves of rings

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in a
big fppf site `B`.  Stacks 03G8 attaches to each of them a morphism of the small étale ringed
topoi, `AlgebraicGeometry.Space.smallEtaleRingedToposHom`, and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` is its compatibility with
composition: the structure map of the composite morphism of ringed topoi, followed by the
cartesian comparison of the direct images of sheaves of *commutative* rings, is the structure map
of the morphism of ringed topoi of `f ≫ g`.

Sheaves of modules are taken over sheaves of rings, not of commutative rings, and restriction of
scalars for the direct image of modules of Stacks 03D6, part (1) is along the *ring-level*
structure map `AlgebraicGeometry.RingedToposHom.structureRingMap`.  This file carries the
composition law across that forgetful functor: `AlgebraicGeometry.Space.structureRingMap_comp`.
That is the input Stacks 03LU's composition comparison for the direct image of modules needs
beyond the general composition law
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposModulesCompIso.lean`) and the transport
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfPushforwardIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackModuleNatIso.lean`).

## Main definitions

* `AlgebraicGeometry.Space.compToposPushforwardIso`: the geometric comparison of Stacks 03G2,
  part (3), read as a comparison of the direct images of sheaves of sets of the composite of the
  morphisms of ringed topoi of `f` and `g` and of the morphism of ringed topoi of `f ≫ g`.
* `AlgebraicGeometry.Space.compStructureRingMap`: the comparison of the direct images of the
  structure sheaf of rings that it induces.

## Main results

* `AlgebraicGeometry.Space.ringSheafMap_compStructureRingMap`: on underlying sheaves of sets, the
  ring-level comparison is the geometric comparison itself.
* `AlgebraicGeometry.Space.structureRingMap_comp`: **the composition law for the structure map at
  the level of sheaves of rings**, i.e. Stacks 03G8's compatibility with composition after
  forgetting commutativity.

## Implementation notes

The three ingredients of Stacks 03LU's comparison
`f_*(-) ⋙ g_*(-) ≅ (f ≫ g)_*(-)` of direct images of modules are now all available — the general
composition law along a composite morphism of ringed topoi, the transport along a comparison of
the direct images of sheaves of sets, and (here) the ring-level composition law for the structure
map — but *assembling* them for the small étale ringed topoi of algebraic spaces is not done
here.  The obstruction is not mathematical: applying
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfPushforwardIso` at
`k = (smallEtaleRingedToposHom g).comp (smallEtaleRingedToposHom f)` and
`k' = smallEtaleRingedToposHom (f ≫ g)` sends the elaborator into an `isDefEq` that does not
terminate within ten times the default heartbeat budget, and the declaration whose type-checking
explodes is the `β` argument — the comparison of the direct images of the structure sheaf of
rings, whose type mentions `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` at the concrete
direct image.  The four arguments the transport wants are exactly the four declarations of this
file plus `compStructureRingMap`; each of them elaborates in isolation, and only the application
does not.  Whoever continues should either assemble the comparison directly at the level of a
single module — the element-level ingredients
`AlgebraicGeometry.RingedToposHom.moduleAddObj_pushforwardModules`,
`moduleSMulObj_pushforwardModules`,
`Stacks.Sheaves.ToposPullback.moduleAddObj_natTrans_app` and `moduleSMulObj_natTrans_app` are all
available — or restate the transport so that no `pullbackRingSheaf` appears in the type of its ring
comparison.

The module universe is the universe `u` of the structure rings, not a free one, and that is
forced rather than chosen: the direct image of sheaves of modules applies the direct image of
sheaves of *sets* to the sheaf underlying the module, and on the small étale site of an algebraic
space that direct image exists only at `Type u`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`.  So Stacks 03LU at an independent
module universe is not in reach by this route at all.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- The geometric comparison of Stacks 03G2, part (3), read as a comparison of the direct images
of sheaves of sets of the composite of the morphisms of ringed topoi of `f` and `g` and of the
morphism of ringed topoi of `f ≫ g`. -/
noncomputable def compToposPushforwardIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).toToposHom.pushforward ≅
      (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.pushforward :=
  smallToposMorphismTypeU_comp B S hS f g

/-- The comparison of the direct images of the structure sheaf of rings of `X` along the
composite of the morphisms of ringed topoi of `f` and `g` and along the morphism of ringed topoi
of `f ≫ g`: the one induced by the geometric comparison
`AlgebraicGeometry.Space.compToposPushforwardIso`. -/
noncomputable def compStructureRingMap (f : X ⟶ Y) (g : Y ⟶ Z) :=
  pullbackRingSheafMapOfNatTrans (smallEtaleRingedTopos B S hS Z).J
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)
    (compToposPushforwardIso B S hS f g).hom

/-- On underlying sheaves of sets, the comparison of the direct images of the structure sheaf of
rings is the geometric comparison itself. -/
theorem ringSheafMap_compStructureRingMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sheafCompose (smallEtaleRingedTopos B S hS Z).J (forget RingCat.{u})).map
        (compStructureRingMap B S hS f g) =
      (compToposPushforwardIso B S hS f g).hom.app
        ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget RingCat.{u})).obj
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (smallEtaleRingedTopos B S hS X).O)) :=
  ringSheafMap_pullbackRingSheafMapOfNatTrans (smallEtaleRingedTopos B S hS Z).J
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)
    (compToposPushforwardIso B S hS f g).hom

/-- **The composition law for the structure map, at the level of sheaves of rings.**  The
structure map of the composite of the morphisms of ringed topoi of `f` and `g`, followed by the
comparison of the direct images of the structure sheaf of rings, is the structure map of the
morphism of ringed topoi of `f ≫ g`.

This is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` — Stacks 03G8,
compatibility with composition — read at the level of sheaves of rings, which is where the
direct image of modules restricts scalars. -/
theorem structureRingMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
          (smallEtaleRingedToposHom B S hS f)).structureRingMap ≫
        compStructureRingMap B S hS f g =
      (smallEtaleRingedToposHom B S hS (f ≫ g)).structureRingMap := by
  refine (sheafCompose (smallEtaleRingedTopos B S hS Z).J
    (forget RingCat.{u})).map_injective ?_
  refine ((sheafCompose (smallEtaleRingedTopos B S hS Z).J
    (forget RingCat.{u})).map_comp _ _).trans ?_
  refine (congrArg (_ ≫ ·) (ringSheafMap_compStructureRingMap B S hS f g)).trans ?_
  refine ((congrArg (_ ≫ ·) (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
    (smallEtaleRingedTopos B S hS Z).J (smallEtaleRingedTopos B S hS X).O
    (smallToposMorphismTypeU_comp B S hS f g)).symm).trans
    ((smallEtaleRingedTopos B S hS Z).forgetRing.map_comp _ _).symm).trans
    (congrArg (smallEtaleRingedTopos B S hS Z).forgetRing.map
    (smallEtaleRingedToposHom_comp_fSharp B S hS f g))

end AlgebraicGeometry.Space

end
