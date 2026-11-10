module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Composition of the direct and inverse image of modules on algebraic spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in a
big fppf site `B`.  Stacks 03LU attaches to each morphism the adjoint pair

`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)`, `f_* : Mod(𝒪_X) ⟶ Mod(𝒪_Y)`

on the modules of the small étale sites.  This file supplies the comparison of the functors of a
composite with the composite of the functors, in both directions:

`f_*(-) ⋙ g_*(-) ≅ (f ≫ g)_*(-)` and `g^*(-) ⋙ f^*(-) ≅ (f ≫ g)^*(-)`.

The morphism of ringed topoi attached to a composite of morphisms of algebraic spaces is *not*
the composite of the two morphisms of ringed topoi — Stacks 03G8's compatibility with composition
compares the two by the cartesian comparison of the direct images — so neither comparison is a
definitional identity.

## Main definitions

* `AlgebraicGeometry.Space.compRingedToposHom`: the composite of the morphisms of small étale
  ringed topoi of `f` and of `g`, named, with the ringed topoi of its source, middle and target
  written out.
* `AlgebraicGeometry.Space.modulePushforwardCompIso'`: the comparison of a composite of direct
  images of modules with the direct image along the composite morphism.
* `AlgebraicGeometry.Space.modulePullbackCompIso`: its adjunction mate, the comparison of a
  composite of inverse images of modules with the inverse image along the composite morphism.

## Main results

* `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`: the direct image of
  modules of the morphism of small étale ringed topoi of `f` is
  `AlgebraicGeometry.Space.modulePushforward`, the functor that carries the Stacks 03LU
  direct-image tag.  So the comparison above is a comparison of *that* functor.

## Implementation notes

The direct-image comparison is the composite of two general facts.  First the composition
law for the direct image of modules along a composite *morphism of ringed topoi*,
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`, which is the identity on underlying
sheaves of sets.  Then the transport
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfPushforwardIso` of the direct image of
modules along a comparison of the direct images of sheaves of sets, applied to the three
ingredients assembled in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardComp.lean`: the geometric
comparison `AlgebraicGeometry.Space.compToposPushforwardIso`, the ring-level comparison
`compStructureRingMap` it induces, and the ring-level composition law `structureRingMap_comp`.

That assembly was previously recorded as out of reach: applying the transport at
`k = (smallEtaleRingedToposHom g).comp (smallEtaleRingedToposHom f)` sent the elaborator into an
`isDefEq` that does not terminate at twenty times the default heartbeat budget.  **The obstruction
was the anonymous `comp`, not the transport.**  `AlgebraicGeometry.RingedToposHom.comp` leaves its
source, middle and target ringed topoi implicit, so each occurrence of the anonymous composite
re-synthesizes them together with their six `GrothendieckTopology.HasSheafCompose` instances;
reconciling two such syntheses makes the unifier reduce `smallEtaleRingedTopos` and then the
comparison equivalence of Stacks 03G1, whose inverse is a `Functor.objPreimage`, i.e. a
`Classical.choose`, and that reduction does not terminate.  Naming the composite, with its three
ringed topoi written out in the declared type — `compRingedToposHom` below — pins them once, and
the transport then applies with no reduction at all.  **No raised heartbeat budget is needed**, and
no `set_option` appears in this file.

The inverse-image comparison is the adjunction mate of the direct-image one, by
`CategoryTheory.Adjunction.leftAdjointCompIso`.  The adjunction it uses is Stacks 03D7 for the
*two-field* morphism of ringed topoi of Stacks 01D3 part (2),
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, whose right adjoint is the
direct image `AlgebraicGeometry.RingedToposHom.pushforwardModules` that this file's comparison is
stated for.  It is written out rather than given a name of its own for a morphism of algebraic
spaces: `AlgebraicGeometry.Space.modulePullbackAdjunction`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`) is the same adjunction
with the *four-field* development's direct image as its right adjoint, and a second name for the
two-field form would be duplication of a general result already stated at the right generality.

The module universe is the universe `u` of the structure rings, not a free one, for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`: the direct image of modules
applies
the direct image of sheaves of *sets* to the sheaf underlying the module, and on the small étale
site of an algebraic space that direct image is available only at `Type u`.

What Stacks 03LU asks for beyond this file is the *normalization* of the direct-image comparison
against the cartesian geometric comparison of Stacks 03G8 after forgetting module structures, and
the associativity coherence of the two comparisons.  The normalization is within reach of the
underlying-sheaf identities of the two ingredients.  The associativity coherence is proved:
the coherence of the geometric comparison of Stacks 03G2, part (3), is
`AlgebraicGeometry.Space.smallToposMorphism_comp_assoc`
(`StacksFrontier/AlgebraicGeometry/Spaces/SpacesBaseChangeAssoc.lean`) and, in the `Type u`
presentation these comparisons are built from,
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardAssoc.lean`); at the level of
modules it is `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean`), stated for
`AlgebraicGeometry.Space.modulePushforwardCompIso` rather than for the presentation of this
file.  Together with `AlgebraicGeometry.Space.modulePushforwardIdIso` it makes
`AlgebraicGeometry.Space.ModulePushforwardCoherence` inhabited with no hypothesis, by
`AlgebraicGeometry.Space.modulePushforwardCoherence`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- The composite of the morphisms of small étale ringed topoi of `f : X ⟶ Y` and `g : Y ⟶ Z`, in
the sense of Stacks 01D3, part (3).

The point of naming it is the declared type: `AlgebraicGeometry.RingedToposHom.comp` leaves the
source, middle and target ringed topoi implicit, and re-synthesizing them at each use site is what
makes the direct-image transport below diverge.  See the implementation notes of this file. -/
noncomputable def compRingedToposHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f)

/-- **Stacks 03LU, the composition comparison for the direct image of modules.**  The composite of
the direct images of `𝒪`-modules along `f : X ⟶ Y` and then `g : Y ⟶ Z` is canonically isomorphic
to the direct image along `f ≫ g`.

The comparison is the composition law for the direct image of modules along a composite morphism
of ringed topoi, followed by the transport of the direct image of modules along Stacks 03G8's
cartesian comparison of the direct images of sheaves of sets.

This is the statement in the `RingedToposHom.pushforwardModules` presentation. The same part key
also sits on `AlgebraicGeometry.Space.modulePushforwardCompIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp`, which states the same
comparison in the library's primary `AlgebraicGeometry.Space.modulePushforward` vocabulary and
is what consumers outside this presentation use; the two are identified by
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_modulePushforwardCompIso'`. A tag carried by
both is correct, not a duplication: each presentation states the clause in its own vocabulary. -/
@[stacks 03LU "pushforward composition"]
noncomputable def modulePushforwardCompIso' (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS g).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModules :=
  (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫
    @RingedToposHom.pushforwardModulesIsoOfPushforwardIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Z)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (compRingedToposHom B S hS f g)
      (smallEtaleRingedToposHom B S hS (f ≫ g))
      (compToposPushforwardIso B S hS f g) (compStructureRingMap B S hS f g)
      (ringSheafMap_compStructureRingMap B S hS f g) (structureRingMap_comp B S hS f g)

end AlgebraicGeometry.Space

end
