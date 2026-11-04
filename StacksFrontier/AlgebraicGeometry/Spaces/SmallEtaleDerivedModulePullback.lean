module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The derived pullback of modules along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03G8 attaches to it a morphism of the small étale *ringed* topoi of `X` and
`Y`, `AlgebraicGeometry.Space.smallEtaleRingedToposHom`, and
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfToposHom.lean`
constructs the derived pullback of Tag 06YY for a morphism of ringed topoi with all six
universes free.  This file puts the two together: `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` for a morphism of
algebraic spaces.

That composite was previously unavailable, and the obstruction was recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedModulePushforward.lean`: the ringed-topos
construction of Tag 06YY was stated at `AlgebraicGeometry.RingedTopos.{w, w, w}` for an
`AlgebraicGeometry.RingedToposSiteHom`, whereas the small étale ringed topos of an algebraic
space is `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` and its morphisms carry no functor
between the underlying sites.  Both halves of that obstruction are dissolved by the generalized
construction, which asks for neither.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is `Lf^*`, and
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackComparison` its canonical comparison
  with degreewise pullback.

## Implementation notes

*What is and is not supplied here.*  The two definitions carry the `Prop`-valued class
`Functor.HasLeftDerivedFunctor` as an instance argument, exactly as the ringed-topos clauses of
Tag 06YY tagged in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfToposHom.lean`
do, and exactly as the derived direct image of
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedModulePushforward.lean` carries its own existence
premise.  What discharges it is a resolving datum for `f^*`, through
`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy_hasLeftDerivedFunctor`;
the resolving half at the K-flat class is Tag 06YS, which is stated in this tree only for a
site which is `CategoryTheory.SmallCategory`, and the small étale site is only *essentially*
small.  See the implementation notes of the ringed-topos file for why that is a property of the
06YS resolution and not of `Lf^*`.

*Why the universes are what they are.*  `AlgebraicGeometry.Space.smallEtaleRingedTopos` has its
objects in `Type (u + 1)` — they are the étale scheme charts, which are morphisms of presheaves
on the big fppf site — while its morphisms and the sections of its structure sheaf are in
`Type u`.  The derived categories here are therefore `DerivedCategory (SheafOfModules.{u} …)`
over a site of that shape, and the derived category model is
`CategoryTheory.HasDerivedCategory.standard`, the one the ringed-topos file is stated at.  That
local attribute is file-scoped there, so it is repeated here.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf of rings over which the sheaves of modules of the small étale *ringed topos* of an
algebraic space are taken: the structure sheaf of the small étale site with the commutativity of
its rings forgotten, in the spelling
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` resolves against.

`AlgebraicGeometry.Space.structureRingSheaf` is the same sheaf of rings reached through
`AlgebraicGeometry.RingedSite.ringSheaf` of `AlgebraicGeometry.Space.smallEtaleRingedSite`. The
two spellings *are* definitionally equal — `example : @ringedToposStructureRingSheaf =
@structureRingSheaf := rfl` elaborates — so this abbreviation is not needed to state anything.
What it is needed for is instance resolution, which matches up to reducible transparency and so
does not see that equality: with the uses below rewritten to `structureRingSheaf`, the
`Functor.HasLeftDerivedFunctor` instance arguments of
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` and of its comparison fail to
synthesize. The spelling the ringed-topos pullback is stated at is therefore the one used
throughout here. -/
abbrev ringedToposStructureRingSheaf (X : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O

variable {X Y : AlgebraicSpaces B S hS}

/-- Degreewise pullback of `𝒪_Y`-modules along a morphism of algebraic spaces, followed by
localization to the derived category of `𝒪_X`-modules.  A left derived functor of this functor
is the derived pullback `Lf^*`. -/
abbrev smallEtaleModulePullbackOnHomotopy (f : X ⟶ Y) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The quasi-isomorphisms of complexes of `𝒪_Y`-modules, the class the derived pullback is the
total left derived functor along. -/
abbrev smallEtaleModuleQuasiIso (Y : AlgebraicSpaces B S hS) :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (ComplexShape.up ℤ)

/-- **The derived pullback of modules along a morphism of algebraic spaces**, `Lf^*`.

This is Tag 06YY for the morphism of small étale ringed topoi of Stacks 03G8, which the
construction of `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback` accepts
because it fixes neither the universes of the two ringed topoi nor the presentation of the
geometric morphism by a functor of sites. -/
abbrev smallEtaleDerivedModulePullback (f : X ⟶ Y)
    [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)] :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  derivedPullback (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The canonical comparison `Lf^* ⟶ f^*` for a morphism of algebraic spaces. -/
abbrev smallEtaleDerivedModulePullbackComparison (f : X ⟶ Y)
    [(smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)] :
    DerivedCategory.Qh ⋙ smallEtaleDerivedModulePullback B S hS f ⟶
      smallEtaleModulePullbackOnHomotopy B S hS f :=
  derivedPullbackComparison (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

end AlgebraicGeometry.Space

end
