module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleBaseChangeSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.BaseChangeMateHorizontalNamed

/-!
# The adjunction of Stacks 03D7 at the spelling the pasting law of Stacks 0E47 needs

Two commutative squares of algebraic spaces sharing a vertical edge paste to a commutative
rectangle:

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

The degree-zero horizontal pasting law of **Stacks 0E47** — the base change map of the rectangle
is the composite of the two base change maps of its squares — is proved at the *module* spelling
in `StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeMapHorizontal.lean`, as
`AlgebraicGeometry.Space.moduleBaseChangeMap_horizontal`.  What
`Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal` asks for as its hypothesis `hτ`, and
what the reduction of **Stacks 073K**, part (1) to part (2) therefore owes, is the same law with
the direct images taken at the spelling of the *ringed topoi* — the direct image of
**Stacks 03D6**, part (1) for the morphism of small étale ringed topoi of **Stacks 03G8**, which
is the one the base change map of **Stacks 0736** on bounded below derived categories is built
from.

This file supplies the three inputs that the pasting engine
`Stacks.Cohomology.BaseChange.mate_horizontal` asks for at that spelling, each of them
unconditional and each a single application of something already proved, **and then assembles the
law**, as `AlgebraicGeometry.Space.toposModuleBaseChangeMap_horizontal`.  With the adjunction
named as it is here, every one of the engine's arguments elaborates, the cocycle condition of
**Stacks 03LU** included — it is passed verbatim as the module-spelling lemma and needs no
respelling at all.  The delicate point of the assembly is the identification of the engine's
conclusion with a written-out statement of it;  the implementation notes below explain the
obstruction and how the statement is spelled so that it does not arise.

## Main definitions

* `AlgebraicGeometry.Space.toposModulePullbackAdjunction`: **Stacks 03D7** for a morphism of
  algebraic spaces, with its left adjoint read as `AlgebraicGeometry.Space.modulePullback` and
  its right adjoint as `AlgebraicGeometry.Space.toposModulePushforward`.  The additivity of the
  left adjoint is `AlgebraicGeometry.Space.additive_modulePullback`.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_modulePullbackSquareComparison_inv_toposAdj`:
  **Stacks 03D8** at a square, at those adjunctions — one of the two things the pasting engine
  asks of each of its three squares.
* `AlgebraicGeometry.Space.toposModuleBaseChangeMap_eq_mate_toposAdj`: the base change map
  `AlgebraicGeometry.Space.toposModuleBaseChangeMap` of a square *is* the base change mate taken
  across those adjunctions, so that the engine's output is a statement about that map.
* `AlgebraicGeometry.Space.toposModuleBaseChangeMap_horizontal`: **Stacks 0E47** in degree zero at
  this spelling — the law itself, in the orientation the hypothesis `hτ` of
  `Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal` asks for.

## Implementation notes

*Which spelling of each image is taken.*  `AlgebraicGeometry.Space.modulePullback` is by
definition `Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism of small étale
ringed topoi, so the two spellings of the inverse image name the same functor and there is
nothing to choose.  The direct images genuinely differ, and the one taken here is the
ringed-topoi one, written as `AlgebraicGeometry.Space.toposModulePushforward` — that same functor
named at the categories `AlgebraicGeometry.Space.Modules`, which is what makes every statement
below seat its categories uniformly;  see the explanation further down.  Reading the
inverse images at the module development's spelling is what makes the engine's two demands
dischargeable by what is already proved:  the cocycle condition of **Stacks 03LU** is
`AlgebraicGeometry.Space.modulePullbackSquareComparison_horizontal` passed with nothing done to
it, and the per-square **Stacks 03D8** identification is
`AlgebraicGeometry.Space.conjugateEquiv_modulePullbackSquareComparison_inv_topos`, restated below
only because the engine asks for it at the adjunctions it is applied to.

*Why the adjunction is named.*  Both reasons are the ones recorded for
`AlgebraicGeometry.Space.toposModuleBaseChangeMap`, and they bite harder here because the engine
takes nine adjunctions at once.  The generic
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` carries some twenty instance
arguments — `HasSheafCompose`, `HasSheafify`, `WEqualsLocallyBijective` and `EnoughInjectives` at
its two corners — and the three universes of the small étale ringed topoi are not recovered from
the ambient data, so source and target have to be supplied by name.  Resolving that once per
morphism, here, is what lets one statement mention nine of them;  with the nine written inline
the elaboration reaches `maximum recursion depth` (8.9s to fail).

*What the obstruction is, and what it is not.*

The engine applied to the three squares of a rectangle, with these adjunctions, the three
comparisons `AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso`, the two comparisons
`AlgebraicGeometry.Space.modulePullbackCompIso` of the composite horizontal inverse images, the
three identifications below and the cocycle condition, elaborates, and its conclusion is
the wanted law with each of the three base change maps written as the mate of the corresponding
square.  Matching that conclusion against a naive *statement* of the law does not finish, in many
variants:  with the three maps written as
`AlgebraicGeometry.Space.toposModuleBaseChangeMap`, with that identification supplied to `rw`,
with the law stated through a named mate-valued definition both plain and `@[reducible]`, and
with the engine's own conclusion written out verbatim in both orientations and matched by `exact`
after the application had already been elaborated with no expected type — so that the only
remaining work was one comparison of two complete propositions.  The device
`Stacks.Cohomology.BaseChange.mate_horizontal_of_eq`
(`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/BaseChangeMateHorizontalNamed.lean`),
which takes the three base change maps as variables with one equation each, removes the mate from
the written statement and does not help either.

A tempting explanation is that the two vocabularies for the *inverse* image disagree
at this seating, `toposModuleBaseChangeMap` being typed through
`Stacks.Sheaves.RingedToposModules.pullbackModules` where `modulePullbackCompIso` and
`modulePullbackSquareComparison` are typed through `AlgebraicGeometry.Space.modulePullback`.
**That is not the obstruction.**  Reading the base change map's two inverse images as
`modulePullback` — which is a two-delta-step restatement of its type, and leaves both `rfl`
lemmas `rfl` — changes nothing:  the match is still `(deterministic) timeout at isDefEq` at
200,000 heartbeats.

*What it actually is, as printing both propositions with
`pp.explicit` shows.*  The two print identically and differ in the *categories*, which the pretty
printer hides.  The engine reads its six categories off the adjunctions it is given, so they are
the modules development's `AlgebraicGeometry.Space.Modules`;  a bare
`Stacks.Sheaves.RingedToposModules.pushforwardModules` is typed at
`SheafOfModules (structureRingSheaf (smallEtaleRingedTopos …))` instead, so a statement that
writes one gets the ringed-topoi categories.  The two are one category by definition, but
crossing them means unfolding `smallEtaleRingedTopos` at every occurrence:  the engine's
conclusion contains no `structureRingSheaf` and ten `smallEtaleRingedTopos`, where the
hand-written statement contains eighteen and ninety-two.  That is the same accumulation effect
the rest of these notes record — each crossing is cheap, eighty of them inside one `isDefEq` is
not — but located in the categories rather than in the functors.

*The fix, and two things that do not work.*  A type ascription does **not** pin a category
argument:  ascribing the direct images in the base change map's type to
`Modules … ⥤ Modules …` leaves its stored type with all fourteen `structureRingSheaf` occurrences,
because the ascription is discharged by a defeq check and the term keeps its own type.  Supplying
the categories positionally to `CategoryTheory.Functor.comp`, `CategoryTheory.Functor.obj` and
`CategoryTheory.Functor.map` does pin them, and in that form the law checks, in 1.8s.

That form is not enough for the *derived* law:  pinning
the categories of the positions a statement writes out leaves the engine to solve all the
others, and solving them from a bare direct image seats them in the ringed-topoi vocabulary
again.  The fix that works everywhere is to name the direct image at the categories wanted —
`AlgebraicGeometry.Space.toposModulePushforward`, whose declared type is
`Modules … ⥤ Modules …` and whose body is the bare `pushforwardModules`.  With the adjunction
below, the square comparison, the base change map and the law all spelled through it, no
`@`-annotation survives in any of their statements, every `rfl` lemma is still `rfl`, and the
derived law of **Stacks 0E47** becomes applicable — it is proved as
`AlgebraicGeometry.Space.toposModuleDerivedBaseChange_horizontal`, whose implementation notes
give the details.  A second thing that does not work:  pinning the engine's
`Category` arguments with `inferInstance` rather than with the instance itself, which leaves a
reducible `@inferInstance (Category.{u+1} (Modules …)) …` wrapper where the law carries
`@SheafOfModules.instCategory …` and reproduces the timeout.

The same degree-zero law at the *ringed-topoi* reading of the inverse images is proved
generically, as `Stacks.Cohomology.ToposBaseChange.moduleBaseChange_horizontal` and its named
form `moduleBaseChange_horizontal_of_eq`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/`
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/FlatBaseChangePastingDegreeZero.lean`:  that is the shape the hypothesis `hτ` of
`Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal` asks for, with the three squares'
**Stacks 03D8** identifications and the cocycle condition of **Stacks 03LU** as its hypotheses.
It too cannot be applied to a *geometric* rectangle, and there the one argument that fails is the
cocycle condition alone;  every other one of its arguments elaborates, and its instance
arguments at the six small étale ringed topoi cost 5.0s.

The first of the two routes the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleBaseChangeSquare.lean` propose is also closed:
stating the cocycle condition itself at the ringed-topoi spelling reaches `maximum recursion
depth` as its own isolated lemma (8.9s to fail, and 10.0s with the statement written out and
the module-spelling lemma as its whole proof), even though each
single cross-spelling
identification it is built from — at a functor and at an object alike, in both directions — is
`rfl` in under a second.  So no individual respelling is expensive and their accumulation inside
one equation is;  the seating here is the one that asks for none of them, which is why its
arguments all go through.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (pushforwardModules
  pullbackAdjPushforwardModules)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Adjunction

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03D7** for a morphism `f : X ⟶ Y` of algebraic spaces, with its left adjoint read
as `AlgebraicGeometry.Space.modulePullback` and its right adjoint as the direct image
`Stacks.Sheaves.RingedToposModules.pushforwardModules` of **Stacks 03D6**, part (1) for the
morphism of small étale ringed topoi of **Stacks 03G8**.

It is `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` on the nose:  the
inverse image of the modules development *is* the ringed-topoi one, by definition of
`AlgebraicGeometry.Space.modulePullback`, so no transport takes place and only the reading of
the left adjoint changes.  It is not `AlgebraicGeometry.Space.modulePullbackAdjunction`, which is
this adjunction with its *right* adjoint transported along
`AlgebraicGeometry.Space.modulePushforwardIso`.

Naming it resolves its twenty-odd instance arguments and the three universes of the small étale
ringed topoi once per morphism.  That is what lets the pasting engine
`Stacks.Cohomology.BaseChange.mate_horizontal` be applied to the nine adjunctions of a pasted
rectangle at all;  with the nine written inline the elaboration does not finish. -/
def toposModulePullbackAdjunction (f : X ⟶ Y) :
    modulePullback B S hS f ⊣ toposModulePushforward f :=
  pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

end Adjunction

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- **Stacks 03D8 at a commutative square of algebraic spaces**, at the adjunctions
`AlgebraicGeometry.Space.toposModulePullbackAdjunction`:  the comparison
`AlgebraicGeometry.Space.toposPushforwardSquareComparisonIso` of the two composite direct images
is the conjugate of the comparison
`AlgebraicGeometry.Space.modulePullbackSquareComparison` of the two composite inverse images.

This is `conjugateEquiv_modulePullbackSquareComparison_inv_topos` with nothing done to
it:  the adjunctions it is stated at are
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, and those are exactly what
`toposModulePullbackAdjunction` names.  It is restated because the pasting law of **Stacks 0E47**
asks for this identification at the adjunctions it is applied to, and matching nine inline
occurrences of the generic adjunction against the named one is itself an elaboration that does
not finish. -/
theorem conjugateEquiv_modulePullbackSquareComparison_inv_toposAdj (comm : g' ≫ f = f' ≫ g) :
    conjugateEquiv ((toposModulePullbackAdjunction f).comp (toposModulePullbackAdjunction g'))
        ((toposModulePullbackAdjunction g).comp (toposModulePullbackAdjunction f'))
        (modulePullbackSquareComparison f g f' g' comm).inv =
      (toposPushforwardSquareComparisonIso f g f' g' comm).hom :=
  conjugateEquiv_modulePullbackSquareComparison_inv_topos f g f' g' comm

/-- **The degree-zero base change map of a square at the ringed-topoi spelling is the base change
mate** taken across the two vertical adjunctions
`AlgebraicGeometry.Space.toposModulePullbackAdjunction`, which is the shape the output of
`Stacks.Cohomology.BaseChange.mate_horizontal` is in.

`AlgebraicGeometry.Space.toposModuleBaseChangeMap` is that mate taken across the generic
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` instead, so this holds by
`rfl`.  It is affordable exactly one square at a time:  it checks in 0.2s here, and using it
at the three squares of a pasted rectangle inside one equation does not elaborate.  See
the implementation notes of this file. -/
theorem toposModuleBaseChangeMap_eq_mate_toposAdj (comm : g' ≫ f = f' ≫ g) :
    toposModuleBaseChangeMap f g f' g' comm =
      Stacks.Cohomology.BaseChange.mate (toposModulePullbackAdjunction g)
        (toposModulePullbackAdjunction g') (toposModulePushforward f)
        (toposModulePushforward f')
        (toposPushforwardSquareComparisonIso f g f' g' comm) := rfl

end Square

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (f'' : X'' ⟶ Y'') (g : Y' ⟶ Y) (g' : X' ⟶ X) (h : Y'' ⟶ Y') (g'' : X'' ⟶ X')

/-- **Stacks 0E47 in degree zero, with the direct images at the ringed-topoi spelling.**  For two
commutative squares of algebraic spaces sharing a vertical edge, the degree-zero base change map
`AlgebraicGeometry.Space.toposModuleBaseChangeMap` of the pasted rectangle is the composite of
the two base change maps of its squares, read through the comparisons of **Stacks 03LU** for the
two composite horizontal inverse images.

This is the law that the hypothesis `hτ` of
`Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal` asks for, and which the reduction of
**Stacks 073K**, part (1) to part (2) owes;  it is stated in that hypothesis' orientation, with
the base change map of the rectangle on the left.

It is `Stacks.Cohomology.BaseChange.mate_horizontal_of_eq` applied to the three squares at the
adjunctions `AlgebraicGeometry.Space.toposModulePullbackAdjunction`, and every one of its
arguments is supplied by something already proved:  the three identifications
`toposModuleBaseChangeMap_eq_mate_toposAdj` of the base change maps with mates, the three
**Stacks 03D8** identifications
`conjugateEquiv_modulePullbackSquareComparison_inv_toposAdj`, and the cocycle condition
`AlgebraicGeometry.Space.modulePullbackSquareComparison_horizontal`, which is passed verbatim.

*Why the direct image is written `AlgebraicGeometry.Space.toposModulePushforward`.*  The engine
reads the six categories off the adjunctions it is given, and those are the modules development's
`AlgebraicGeometry.Space.Modules`, because the left adjoint of `toposModulePullbackAdjunction` is
`AlgebraicGeometry.Space.modulePullback`.  A bare
`Stacks.Sheaves.RingedToposModules.pushforwardModules` is instead typed at
`SheafOfModules (structureRingSheaf (smallEtaleRingedTopos …))`, so writing one here would make
this statement's categories the ringed-topoi ones and the engine's the module ones.  The two are
the same category by definition but not the same *term*, and crossing them inside one proposition
is what does not finish — see the implementation notes above.  `toposModulePushforward` is that
same direct image with its declared type already at `Modules`, so every category position of this
statement is the `Modules` one and there is nothing to cross.  *No `@[stacks 0E47]` attribute*,
for the reason recorded for the module spelling
`AlgebraicGeometry.Space.moduleBaseChangeMap_horizontal`: **Stacks 0E47** asserts the law for the
*derived* direct images, and this is the degree-zero input to it. -/
theorem toposModuleBaseChangeMap_horizontal (comm : g' ≫ f = f' ≫ g)
    (comm' : g'' ≫ f' = f'' ≫ h) (K : Modules.{u, u} B S hS X.1 X.2) :
    (toposModuleBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
          (pasteBaseComm f g f' g' h f'' g'' comm comm')).app K =
      (modulePullbackCompIso B S hS h g).inv.app ((toposModulePushforward f).obj K) ≫
        (modulePullback B S hS h).map ((toposModuleBaseChangeMap f g f' g' comm).app K) ≫
        (toposModuleBaseChangeMap f' h f'' g'' comm').app ((modulePullback B S hS g').obj K) ≫
        (toposModulePushforward f'').map ((modulePullbackCompIso B S hS g'' g').hom.app K) :=
  Stacks.Cohomology.BaseChange.mate_horizontal_of_eq
    (toposModulePullbackAdjunction f) (toposModulePullbackAdjunction f')
    (toposModulePullbackAdjunction f'')
    (toposModulePullbackAdjunction g) (toposModulePullbackAdjunction g')
    (toposModulePullbackAdjunction h) (toposModulePullbackAdjunction g'')
    (toposModulePullbackAdjunction (h ≫ g)) (toposModulePullbackAdjunction (g'' ≫ g'))
    (toposPushforwardSquareComparisonIso f g f' g' comm)
    (toposPushforwardSquareComparisonIso f' h f'' g'' comm')
    (toposPushforwardSquareComparisonIso f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    (modulePullbackCompIso B S hS h g) (modulePullbackCompIso B S hS g'' g')
    (modulePullbackSquareComparison f g f' g' comm).inv
    (modulePullbackSquareComparison f' h f'' g'' comm').inv
    (modulePullbackSquareComparison f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm')).inv
    (toposModuleBaseChangeMap f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    (toposModuleBaseChangeMap f g f' g' comm)
    (toposModuleBaseChangeMap f' h f'' g'' comm')
    (toposModuleBaseChangeMap_eq_mate_toposAdj f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    (toposModuleBaseChangeMap_eq_mate_toposAdj f g f' g' comm)
    (toposModuleBaseChangeMap_eq_mate_toposAdj f' h f'' g'' comm')
    (conjugateEquiv_modulePullbackSquareComparison_inv_toposAdj f g f' g' comm)
    (conjugateEquiv_modulePullbackSquareComparison_inv_toposAdj f' h f'' g'' comm')
    (conjugateEquiv_modulePullbackSquareComparison_inv_toposAdj f (h ≫ g) f'' (g'' ≫ g')
      (pasteBaseComm f g f' g' h f'' g'' comm comm'))
    (modulePullbackSquareComparison_horizontal f f' f'' g g' h g'' comm comm') K

end Horizontal

end AlgebraicGeometry.Space

end
