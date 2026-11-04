module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapHorizontal
public import StacksFrontier.CategoryTheory.Adjunction.CompOfNatIsoRight
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.FlatBaseChange

/-!
# The degree-zero base change map of a square of algebraic spaces, at the ringed-topoi spelling

Let

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

be two commutative squares of algebraic spaces sharing a vertical edge.  The degree-zero base
change map of such a square is available at three spellings in this development:
`AlgebraicGeometry.Space.moduleBaseChangeMap` at the *module* spelling,
`AlgebraicGeometry.Space.siteBaseChangeMap` at the *site* spelling, and
`Stacks.Cohomology.ToposBaseChange.moduleBaseChange` at the spelling of the *ringed topoi* — the
direct and inverse images of **Stacks 03D6** for the morphism of small étale ringed topoi of
**Stacks 03G8**, which is the one the base change map of **Stacks 0736** on bounded below derived
categories is built from.

This file carries the characterization of the base change map as a *mate* — **Stacks 03D8** at a
square — from the module spelling to the ringed-topoi spelling.  That is one of the two things
`Stacks.Cohomology.BaseChange.mate_horizontal` asks of each square it pastes; the degree-zero
horizontal pasting law of **Stacks 0E47** at the ringed-topoi spelling is assembled from it in
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleBaseChangeHorizontal.lean`, as
`AlgebraicGeometry.Space.toposModuleBaseChangeMap_horizontal`.

## Main definitions

* `AlgebraicGeometry.Space.toposModulePushforward`: the direct image of **Stacks 03D6**, part (1)
  for the morphism of small étale ringed topoi, named at the categories
  `AlgebraicGeometry.Space.Modules`.  Every statement in this file is spelled through it.  Its
  additivity is the instance `AlgebraicGeometry.Space.additive_toposModulePushforward`.
* `AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso`: the comparison
  `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images around a commutative square, at
  the ringed-topoi spelling.  It is the module-spelling comparison
  `AlgebraicGeometry.Space.modulePushforwardSquareComparisonIso` conjugated by the four
  comparisons `AlgebraicGeometry.Space.modulePushforwardIso` of the two spellings of the direct
  image.
* `AlgebraicGeometry.Space.toposModuleBaseChangeMap`: the degree-zero base change map of the
  square at that spelling, named so that its instance arguments and the three universes of the
  small étale ringed topoi are resolved once rather than at every mention;
  `AlgebraicGeometry.Space.toposModuleBaseChangeMap_eq_moduleBaseChange` identifies it with
  `Stacks.Cohomology.ToposBaseChange.moduleBaseChange`.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_modulePullbackSquareComparison_inv_topos`: at the
  ringed-topoi spelling too, the comparison of the two composite direct images around a square is
  the conjugate of the comparison of the two composite inverse images.  This is **Stacks 03D8** at
  a square, in the form the pasting engine asks of each of its three squares.

## Implementation notes

*Why only the direct image needs carrying.*  The inverse image needs none:
`AlgebraicGeometry.Space.modulePullback` is *by definition*
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism of small étale ringed topoi,
so the two spellings of the inverse image are the same functor on the nose, and the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of inverse images along a composite, the square
comparison `AlgebraicGeometry.Space.modulePullbackSquareComparison` and the pasting identity
`AlgebraicGeometry.Space.modulePullbackSquareComparison_horizontal` are, as *types*, already the
statements wanted here.  Because the two readings are interchangeable, the type of
`AlgebraicGeometry.Space.toposModuleBaseChangeMap` below writes its two inverse images as
`modulePullback`, which is the reading everything the pasting law is applied to uses.  The direct
image is a genuine difference: the modules development's
`AlgebraicGeometry.Space.modulePushforward` takes the direct image first and restricts scalars
along the direct-image form `𝒪_Y ⟶ f_*𝒪_X` of the structure map, whereas the ringed-topoi
`pushforwardModules` restricts along the inverse-image form first, and
`AlgebraicGeometry.Space.modulePushforwardIso` is the comparison of the two.

*How the carrying is done.*  `AlgebraicGeometry.Space.modulePullbackAdjunction` is, by
definition, the ringed-topoi adjunction of **Stacks 03D7** with its right adjoint transported
along `AlgebraicGeometry.Space.modulePushforwardIso`.  So the two adjunctions whose conjugate
calculus the square comparison lives in differ by
`CategoryTheory.Adjunction.ofNatIsoRight` on each of their two factors, which is
`Stacks.CategoryTheory.comp_ofNatIsoRight` one transport of the *composite* right adjoint, and
`Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight` then conjugates the identity by it.  That is
the whole of the transport: no property of the comparisons is used, and the geometric content —
the associativity pentagon of **Stacks 03LU** — stays where it was proved, at the module
spelling.

*The categories of the direct images.*  A bare
`Stacks.Sheaves.RingedToposModules.pushforwardModules` is typed at
`SheafOfModules (structureRingSheaf (smallEtaleRingedTopos …))`, which is
`AlgebraicGeometry.Space.Modules` by definition but not as a term.  So the type of
`toposModuleBaseChangeMap` below supplies the categories of its two direct-image factors
positionally to `CategoryTheory.Functor.comp`, and every category in it is
`AlgebraicGeometry.Space.Modules`; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleBaseChangeHorizontal.lean` explain why the
pasting law needs this.

*Why the morphisms of ringed topoi are spelled through
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`.*  The additivity instances of the two
images at the small étale ringed topoi are registered at that spelling, in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean`;
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom` is a `def` for the same term, which
the search for an instance does not cross.  The two are interchangeable for elaboration, so the
statements of `AlgebraicGeometry.Space.modulePushforwardIso` and
`AlgebraicGeometry.Space.modulePullback` — written at the other spelling — compose with these
without a transport.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (pushforwardModules
  pullbackAdjPushforwardModules)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section DirectImage

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03D6, part (1)** for the morphism of small étale ringed topoi of **Stacks 03G8**
attached to a morphism `f : X ⟶ Y` of algebraic spaces:  the direct image `f_*` of `𝒪`-modules
at the *ringed-topoi* spelling, named at the categories `AlgebraicGeometry.Space.Modules`.

The functor is `Stacks.Sheaves.RingedToposModules.pushforwardModules` of that morphism and
nothing else;  `toposModulePushforward_eq` below is `rfl`.  It is **not**
`AlgebraicGeometry.Space.modulePushforward`, which is the modules development's own direct image
and agrees with this one only up to `AlgebraicGeometry.Space.modulePushforwardIso`.

What the name supplies is the *type*: a bare `pushforwardModules` of this morphism is typed at
`SheafOfModules (Stacks.Sheaves.RingedToposModules.structureRingSheaf (smallEtaleRingedTopos …))`,
whereas every inverse image here is typed at `AlgebraicGeometry.Space.Modules`. -/
noncomputable def toposModulePushforward (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  pushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

/-- `AlgebraicGeometry.Space.toposModulePushforward` **is** the direct image of **Stacks 03D6**,
part (1) of the morphism of small étale ringed topoi:  only its declared type differs, and that
by definition. -/
theorem toposModulePushforward_eq (f : X ⟶ Y) :
    toposModulePushforward f =
      pushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom := rfl

/-- **Stacks 03D6, part (1)**, additivity:  the direct image of `𝒪`-modules along a morphism of
algebraic spaces at the ringed-topoi spelling is additive.  This is
`Stacks.Sheaves.RingedToposModules.additive_pushforwardModules`, restated because instance search
does not unfold `AlgebraicGeometry.Space.toposModulePushforward`. -/
instance additive_toposModulePushforward (f : X ⟶ Y) : (toposModulePushforward f).Additive :=
  Stacks.Sheaves.RingedToposModules.additive_pushforwardModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

end DirectImage

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- **The comparison `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images around a
commutative square of algebraic spaces, at the ringed-topoi spelling.**

It is the module-spelling comparison
`AlgebraicGeometry.Space.modulePushforwardSquareComparisonIso` — the direct-image half of
**Stacks 03LU** used twice — conjugated by the four comparisons
`AlgebraicGeometry.Space.modulePushforwardIso` of the two spellings of the direct image. -/
def toposPushforwardSquareComparisonIso (comm : g' ≫ f = f' ≫ g) :
    toposModulePushforward g' ⋙ toposModulePushforward f ≅
      toposModulePushforward f' ⋙ toposModulePushforward g :=
  (Functor.isoWhiskerLeft _ (modulePushforwardIso B S hS f) ≪≫
      Functor.isoWhiskerRight (modulePushforwardIso B S hS g') _) ≪≫
    modulePushforwardSquareComparisonIso f g f' g' comm ≪≫
    (Functor.isoWhiskerLeft _ (modulePushforwardIso B S hS g) ≪≫
      Functor.isoWhiskerRight (modulePushforwardIso B S hS f') _).symm

/-- **Stacks 03D8 at a commutative square of algebraic spaces, at the ringed-topoi spelling.**
The comparison `AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso` of the two composite
direct images is the conjugate, under the two adjunctions of **Stacks 03D7** for the two
*vertical* morphisms of the square, of the comparison
`AlgebraicGeometry.Space.modulePullbackSquareComparison` of the two composite inverse images. -/
theorem conjugateEquiv_modulePullbackSquareComparison_inv_topos (comm : g' ≫ f = f' ≫ g) :
    conjugateEquiv
        ((pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
            (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
            (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS g').toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y')
            (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS g).toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
            (Y := smallEtaleRingedTopos B S hS Y')
            (smallEtaleRingedToposHom B S hS f').toRingedToposModulesHom))
        (modulePullbackSquareComparison f g f' g' comm).inv =
      (toposPushforwardSquareComparisonIso f g f' g' comm).hom :=
  Stacks.CategoryTheory.conjugateEquiv_comp_comp_ofNatIsoRight
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom)
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS g').toRingedToposModulesHom)
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS g).toRingedToposModulesHom)
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y')
      (smallEtaleRingedToposHom B S hS f').toRingedToposModulesHom)
    (modulePushforwardIso B S hS f) (modulePushforwardIso B S hS g')
    (modulePushforwardIso B S hS g) (modulePushforwardIso B S hS f')
    (modulePullbackSquareComparison f g f' g' comm).inv
    (modulePushforwardSquareComparisonIso f g f' g' comm).hom
    (conjugateEquiv_modulePullbackSquareComparison_inv_eq f g f' g' comm)

/-- **The degree-zero base change map `g^*f_* ⟶ f'_*(g')^*` of a commutative square of algebraic
spaces, at the ringed-topoi spelling**:  `Stacks.Cohomology.ToposBaseChange.moduleBaseChange` of
the square of small étale ringed topoi, for the comparison
`AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso` of the two composite direct images.

It is `Stacks.Cohomology.ToposBaseChange.moduleBaseChange` on the nose; its type reads the two
inverse images as `AlgebraicGeometry.Space.modulePullback` and gives the two direct-image factors
their categories positionally, so that every category in it is `Modules`. -/
def toposModuleBaseChangeMap (comm : g' ≫ f = f' ≫ g) :
    toposModulePushforward f ⋙ modulePullback B S hS g ⟶
      modulePullback B S hS g' ⋙ toposModulePushforward f' :=
  Stacks.Cohomology.BaseChange.mate
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS g).toRingedToposModulesHom)
    (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS g').toRingedToposModulesHom)
    (pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom)
    (pushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y')
      (smallEtaleRingedToposHom B S hS f').toRingedToposModulesHom)
    (toposPushforwardSquareComparisonIso f g f' g' comm)

/-- `AlgebraicGeometry.Space.toposModuleBaseChangeMap` **is** the base change map
`Stacks.Cohomology.ToposBaseChange.moduleBaseChange` of the square of small étale ringed topoi.
The latter is by definition the same mate, so this holds by `rfl`. -/
theorem toposModuleBaseChangeMap_eq_moduleBaseChange (comm : g' ≫ f = f' ≫ g) :
    toposModuleBaseChangeMap f g f' g' comm =
      Stacks.Cohomology.ToposBaseChange.moduleBaseChange
        (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS f')
        (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS g')
        (toposPushforwardSquareComparisonIso f g f' g' comm) := rfl

end Square

end AlgebraicGeometry.Space

end
