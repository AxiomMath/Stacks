module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image of modules along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03LU asserts the existence of the pair of functors

`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)`, `f_* : Mod(𝒪_X) ⟶ Mod(𝒪_Y)`

on the modules of the small étale ringed sites.  This file supplies the direct image `f_*`, in
the only form in which it is available in the library: as a functor depending on the
map of structure sheaves `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, which is supplied by Stacks 03G8 and is *not*
constructed here.

The point of the file is that this is all `f_*` needs.  The direct image of modules of Stacks
03D1 is defined by `Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` for an arbitrary
finite-product-preserving functor between categories of sheaves of sets, with no adjoint and no
left exactness assumed; so the direct image of `𝒪_X`-modules exists as soon as the direct image
of sheaves of *sets* on the small étale sites exists at the universe of the structure rings, and
that is assembled below from the comparison equivalence of Stacks 03G1 and the spaces-étale
direct image of Stacks 03G2, part (1).  In particular no morphism of small étale *topoi* at the
universe of the structure rings is needed, and hence none of the `RingedToposHom` data of
Stacks 03G8 beyond its structure map.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDirectImage` is the direct image of sheaves of sets along
  `f` on the small étale sites, at the universe of the structure rings.
* `AlgebraicGeometry.Space.structureRingSheafDirectImage` is `f_*𝒪_X` as a sheaf of rings on the
  small étale site of `Y`: the target of the structure map `f♯` of Stacks 03G8.
* `AlgebraicGeometry.Space.moduleDirectImage` is the direct image of `𝒪_X`-modules, taken over
  `f_*𝒪_X`; this is Stacks 03D1 for the small étale sites.
* `AlgebraicGeometry.Space.modulePushforwardOfStructureMap` is the direct image of
  `𝒪_X`-modules read as `𝒪_Y`-modules by restriction of scalars along a structure map
  `f♯ : 𝒪_Y ⟶ f_*𝒪_X`; this is Stacks 03D6, part (1) for the small étale sites.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDirectImage_comparison` pins the direct image down: it
  agrees, through the comparison equivalences of Stacks 03G1, with the spaces-étale direct image
  of Stacks 03G2, part (1).  So it is not an independent choice.
* `AlgebraicGeometry.Space.moduleSheaf_moduleDirectImage`: the sheaf of sets underlying the
  direct image of a module is the direct image of the sheaf of sets underlying the module.

## Implementation notes

The module universe is the universe of the structure rings, and is not free.  That is forced:
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` carries the sections of a module over
`𝒪_X` to sections over `𝒪_Y` by applying the direct image of sheaves of *sets* to the sheaf
underlying the module, so the direct image must be available at the module universe; and at the
universe of the structure rings it is, by the instances of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse`, while at a universe
unrelated to that of the schemes neither sheafification nor the comparison equivalence of
Stacks 03G1 is available on a site whose objects lie one universe higher.  So the
`AlgebraicGeometry.Space.Modules` here are those with sections in the universe of the schemes.

The direct image of sheaves of sets is the restriction along the spaces-étale base change of
Stacks 03G2, part (1), conjugated by the comparison equivalences of Stacks 03G1 — the same
recipe as `AlgebraicGeometry.Space.smallToposMorphism`, but one universe lower, and *only* for
the direct image.  The inverse image cannot be obtained this way: the spaces-étale direct image
does have a left adjoint at this universe
(`AlgebraicGeometry.Space.isRightAdjoint_sheafPushforwardContinuous_spacesBaseChange`), but that
left adjoint is not known to be left exact, so the pair is not a
`MorphismOfTopoi` and the pullback of modules of Stacks 03D6, part (2) — which transports the
ring and module operations across the product comparisons of the *inverse* image — is out of
reach.  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse` for what left exactness would
require.

Finite-product preservation of the direct image is recorded as an instance because
`AlgebraicGeometry.Space.smallEtaleDirectImage` is a definition and instance search does not
unfold it; the content is that each of its three factors preserves limits, two being halves of
equivalences and the third a restriction functor with a left adjoint.

The universes of `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` are supplied explicitly in
`AlgebraicGeometry.Space.structureRingSheafDirectImage`: the two sites of its statement are the
small étale sites, whose objects and morphisms lie in different universes, and elaboration of
the expected type defaults the universes of the source site before the functor argument is
elaborated unless they are given.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Restriction along the comparison functor of Stacks 03G1, at the universe of the structure
rings: the identification of the spaces-étale topos of an algebraic space with its small étale
topos. -/
noncomputable abbrev smallEtaleComparisonRestriction (X : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS X) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)

/-- The direct image of sheaves of sets along `f : X ⟶ Y` on the small étale sites, at the
universe of the structure rings: the spaces-étale direct image of Stacks 03G2, part (1),
conjugated by the comparison equivalences of Stacks 03G1. -/
noncomputable def smallEtaleDirectImage (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
  (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse ⋙
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
    smallEtaleComparisonRestriction B S hS Y

/-- The direct image of sheaves of sets preserves finite products: two of its three factors are
halves of equivalences and the third has a left adjoint, so all three preserve limits. -/
instance smallEtaleDirectImage_preservesFiniteProducts (f : X ⟶ Y) :
    PreservesFiniteProducts (smallEtaleDirectImage B S hS f) := by
  unfold smallEtaleDirectImage
  infer_instance

/-- The direct image of sheaves of sets on the small étale sites agrees, through the comparison
equivalences of Stacks 03G1, with the spaces-étale direct image of Stacks 03G2, part (1).  This
identifies `AlgebraicGeometry.Space.smallEtaleDirectImage` and is not an extra choice. -/
noncomputable def smallEtaleDirectImage_comparison (f : X ⟶ Y) :
    smallEtaleComparisonRestriction B S hS X ⋙ smallEtaleDirectImage B S hS f ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        smallEtaleComparisonRestriction B S hS Y :=
  Functor.isoWhiskerRight (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.symm
      (_ ⋙ smallEtaleComparisonRestriction B S hS Y) ≪≫
    Functor.leftUnitor _

/-- The direct image `f_*𝒪_X` of the structure sheaf of `X`, as a sheaf of rings on the small
étale site of `Y`.  This is the target of the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of
Stacks 03G8. -/
noncomputable abbrev structureRingSheafDirectImage (f : X ⟶ Y) :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
    (smallEtaleDirectImage B S hS f)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **Stacks 03D1** for the small étale sites of algebraic spaces: the direct image of
`𝒪_X`-modules along `f : X ⟶ Y`, taken over the direct-image sheaf of rings `f_*𝒪_X`.  Its
scalar action is the direct image of the scalar action of the original module, read through the
product comparison of the direct image. -/
noncomputable def moduleDirectImage (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (structureRingSheafDirectImage B S hS f) :=
  pullbackModuleFunctor (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImage B S hS f)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- The sheaf of sets underlying the direct image of a module is the direct image of the sheaf of
sets underlying the module: the direct image of modules only adds algebraic structure. -/
theorem moduleSheaf_moduleDirectImage (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf.moduleSheaf (structureRingSheafDirectImage B S hS f)
        ((moduleDirectImage B S hS f).obj M) =
      (smallEtaleDirectImage B S hS f).obj
        (Sheaf.moduleSheaf.{u, u, u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) M) :=
  rfl

/-- **Stacks 03D6, part (1)** for the small étale sites of algebraic spaces, and the direct-image
half of Stacks 03LU: given the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8, the direct
image of `𝒪_X`-modules read as `𝒪_Y`-modules by restriction of scalars along `f♯`.

The structure map is a parameter here, for generality, and is not an input that has to be
assumed: Stacks 03G8 is formalized, and `AlgebraicGeometry.Space.structureSharp`
(`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean`) constructs `f♯` for an arbitrary
morphism of algebraic spaces, with no hypothesis beyond `f` itself.  The unconditional
specialisation of this functor along that structure map is
`AlgebraicGeometry.Space.modulePushforward`, in the same file, which carries the direct-image
part-string of Stacks 03LU.  The `CommRingCat`-valued form of the same map is the `fSharp` field
of `AlgebraicGeometry.Space.smallEtaleRingedToposHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHom.lean`), and
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` identifies the direct
image of modules of that morphism of ringed topoi with `modulePushforward` itself. -/
@[sga "4 IV 13.2.1" "special case"]
noncomputable def modulePushforwardOfStructureMap (f : X ⟶ Y)
    (fSharp : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⟶
      structureRingSheafDirectImage B S hS f) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  moduleDirectImage B S hS f ⋙ SheafOfModules.restrictScalars fSharp

end AlgebraicGeometry.Space

end
