module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The derived base change map

A commutative square of ringed spaces

```
X' --g'--> X
|          |
f'         f
v          v
S' --g-->  S
```

determines a canonical morphism of functors `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on the unbounded
derived category of `𝒪_X`-modules.  It is the mate, under the derived adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`, of the comparison `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` of the two
iterated derived pullbacks, that is, the transpose of the derived pullback along `g'` of the
derived counit `Lf^* (Rf_* K) ⟶ K`.

Everything is stated for the canonical derived pullbacks and pushforwards of Tag 079W, which
exist for every morphism of ringed spaces, so the only data are the four morphisms of the square
and the commutativity of it.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` identifies the iterated derived
  pullback
  `Lg^* ⋙ Lf'^*`, down the left and along the bottom of the square, with the derived pullback
  along the common composite.
* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` is the comparison of the two iterated
  derived
  pullbacks, read as a two-square.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare` is the canonical morphism of
  functors.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` is its component at an object, which
  is the derived base
  change map `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint` identifies the adjoint of the
  base change map
  with that derived pullback of the counit, so clients can reason about the canonical map
  without unfolding its definition.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq`: the base change map is the
  transpose of the derived
  pullback of the counit.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality`: naturality in the complex,
  which the
  two-square formulation supplies.

## Implementation notes

*How the square enters.*  Commutativity of the square says `g' ≫ f = f' ≫ g`, and what the
construction uses of it is that the two iterated derived pullbacks `Lg^* ⋙ Lf'^*` and
`Lf^* ⋙ Lg'^*` are both derived pullback along that one morphism.  Each of the two is identified
with `L(g' ≫ f)^*` by the composition formula of Tag 0D5S,
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, at `(f', g)` and at `(g', f)`
  respectively.
Only the first needs the equality of composites, and `derivedPullbackCompIsoLeft` carries it; it
is the single transport in the file.

*Why the mate, rather than a bare morphism.*  `CategoryTheory.mateEquiv` is the bijection
between two-squares across a pair of adjunctions, so the base change map comes out as a
morphism of functors with its naturality already proved, and `derivedBaseChangeMap_adjoint`
records that its component is the transpose of the pullback of the counit, which is the
description the source gives.

*Why the derived functors are not hypotheses.*  Both derived pullback and derived pushforward
are everywhere defined for a morphism of ringed spaces —
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` by the
K-flat resolving datum of Tag 06YJ,
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` by K-injective
resolutions — and `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction` is the
  resulting adjunction `Lf^* ⊣ Rf_*`
for an arbitrary `f`.  The composition isomorphisms are likewise unconditional, by
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, so none of the derived
functors, adjunctions or composition isomorphisms is a parameter of the statements.

*Why the mate layer is still parametric.*  The `Stacks.Cohomology.DerivedBaseChange.Mate` namespace
  keeps the
construction over abstract functors and adjunctions, and the canonical declarations instantiate
it.  That is not generality for its own sake:
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` are `abbrev`s over total
  derived functors, and rewriting
inside a goal that mentions four of them at once builds a proof term the kernel cannot check in
its budget.  Proving each mate identity once with the functors as variables and then applying
it keeps every canonical proof term a single application.

*One spelling for the category of module sheaves.*  The categories are written
`SheafOfModules.{u} (structureSheafRing X)`, which is the spelling in the declared type of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, and not the `abbrev`
`ModuleSheaves X` for it, so that every type here is syntactically the one the imported
statements carry.

Do not read that as a diagnosis of a kernel timeout.  `ModuleSheaves` is a `noncomputable
abbrev` for `SheafOfModules.{u} (structureSheafRing _)` in `RingedSpaceModuleAdjunction`, and
the two types and their `Category` instances are `rfl`-equal in under a second; a statement
mixing them is not thereby out of reach.  What does defeat the kernel in this area, notably at the square's degreewise comparison, is
recorded in the implementation
notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/`
`DegreewiseAndDerivedPullbackSquare.lean`.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition

namespace StacksDraft.DerivedBaseChangeSplit

variable {C D : Type*} [CategoryTheory.Category C] [CategoryTheory.Category D]

/-- **A transport of functors, read at an object.**  The component of `CategoryTheory.eqToIso`
is a transport of *objects*, and may be presented as one with the object equality chosen freely.

This is what lets the two spellings of a derived pullback along the diagonal of a commutative
square meet.  Comparing the two *functors* exhausts the kernel, because
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` is reducible over a large
definition; comparing the two *objects* obtained by applying them to one complex does not.
Writing both transports as `CategoryTheory.eqToHom` of an object equality replaces the first
comparison by the second. -/
theorem eqToIso_hom_app_eq {F G : C ⥤ D} (h : F = G) (Y : C) (e : F.obj Y = G.obj Y) :
    (CategoryTheory.eqToIso h).hom.app Y = CategoryTheory.eqToHom e := by
  subst h
  simp

end StacksDraft.DerivedBaseChangeSplit

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace Mate

variable {X' X S' S : RingedSpace.{u, u}}
  {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- The comparison `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` of the two iterated derived pullbacks around
the square, read as a two-square.  Both composites are derived pullback along the common
composite of the square, and the comparison is the resulting isomorphism. -/
def derivedPullbackSquare : TwoSquare Lg Lf Lf' Lg' :=
  TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv)

/-- The canonical derived base change morphism of functors
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`: the mate of the comparison of the two iterated derived
pullbacks. -/
def derivedBaseChangeSquare : TwoSquare Rf Lg' Lg Rf' :=
  mateEquiv adjf adjf' (derivedPullbackSquare eg ef)

/-- The canonical derived base change map `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)` at an object of the
unbounded derived category. -/
def derivedBaseChangeMap (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K) :=
  (derivedBaseChangeSquare adjf adjf' eg ef).app K

/-- Under the adjunction `Lf'^* ⊣ Rf'_*`, the base change map is the derived pullback of the
counit, transported across the two composition isomorphisms.  This is
`CategoryTheory.mateEquiv_counit`, the defining property of the mate at a component. -/
@[simp]
theorem derivedBaseChangeMap_adjoint
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm
        (derivedBaseChangeMap adjf adjf' eg ef K) =
      eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K) := by
  simp only [derivedBaseChangeMap, derivedBaseChangeSquare]
  rw [Adjunction.homEquiv_counit, mateEquiv_counit]
  simp only [derivedPullbackSquare, NatTrans.comp_app, Category.assoc]

/-- The derived base change map is the transpose, under `Lf'^* ⊣ Rf'_*`, of the derived
pullback along `g'` of the derived counit `Lf^* (Rf_* K) ⟶ K`, transported across the two
composition isomorphisms. -/
theorem derivedBaseChangeMap_eq (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap adjf adjf' eg ef K =
      adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)
        (eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫
          Lg'.map (adjf.counit.app K)) := by
  rw [← derivedBaseChangeMap_adjoint, Equiv.apply_symm_apply]

/-- The derived base change map is natural in the complex. -/
theorem derivedBaseChangeMap_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (u : K ⟶ L) :
    Lg.map (Rf.map u) ≫ derivedBaseChangeMap adjf adjf' eg ef L =
      derivedBaseChangeMap adjf adjf' eg ef K ≫ Rf'.map (Lg'.map u) :=
  (derivedBaseChangeSquare adjf adjf' eg ef).naturality u

end Mate

section Canonical

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- The iterated derived pullback `Lg^* ⋙ Lf'^*`, down the left and along the bottom of the
square, identified with the derived pullback along the common composite `g' ≫ f = f' ≫ g`.

This is the composition formula of Tag 0D5S at `(f', g)`, transported along the commutativity of
the square. -/
def derivedPullbackCompIsoLeft :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f' ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (g' ≫ f) :=
  derivedPullbackCompIsoCanonical f' g ≪≫
    eqToIso (congrArg (fun h : X' ⟶ S =>
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h) sq.symm)

/-- The comparison `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` of the two iterated derived pullbacks around
a commutative square of ringed spaces, read as a two-square. -/
def derivedPullbackSquare :
    TwoSquare (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f')
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g') :=
  Mate.derivedPullbackSquare (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f)

/-- The canonical derived base change morphism of functors
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` attached to a commutative square of ringed spaces: the mate,
under the derived adjunctions of Tag 079W, of the comparison of the two iterated derived
pullbacks. -/
def derivedBaseChangeSquare :
    TwoSquare (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g')
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f') :=
  Mate.derivedBaseChangeSquare (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
      (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f)

/-- `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare` is the mate, under the two
derived adjunctions of Tag 079W, of the comparison
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` of the two iterated derived
pullbacks.  This is its definition; it is recorded as a lemma so that the two delta steps through
the `Mate` namespace are paid once rather than inside each consumer's goal, where the kernel has
to re-check them against the derived-functor terms. -/
theorem derivedBaseChangeSquare_eq_mateEquiv :
    derivedBaseChangeSquare g' f' f g sq =
      mateEquiv (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
        (derivedPullbackSquare g' f' f g sq) :=
  rfl

/-- **The derived base change map** `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)` of a commutative square
of ringed spaces, at an object of the unbounded derived category.  It is adjoint to the derived
pullback along `g'` of the derived counit `Lf^* (Rf_* K) ⟶ K`, after identifying the two
iterated derived pullbacks. -/
@[stacks 08HY "derived_base_change_map",
  sga "4 XVII 4.1.5" "ringed spaces",
  sga "4 XVII 4.1.4" "ringed spaces case"]
def derivedBaseChangeMap (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f').obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj K) :=
  Mate.derivedBaseChangeMap (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
      (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) K

/-- Under the derived adjunction `Lf'^* ⊣ Rf'_*`, the base change map is the derived pullback
of the counit, transported across the two composition isomorphisms. -/
@[simp, stacks 08HY "adjoint characterization of the canonical map"]
theorem derivedBaseChangeMap_adjoint
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f').homEquiv
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K))
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj K)).symm
        (derivedBaseChangeMap g' f' f g sq K) =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit.app K) :=
  Mate.derivedBaseChangeMap_adjoint
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
      (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) K

/-- The derived base change map is the transpose, under `Lf'^* ⊣ Rf'_*`, of the derived
pullback along `g'` of the derived counit `Lf^* (Rf_* K) ⟶ K`, transported across the two
composition isomorphisms. -/
theorem derivedBaseChangeMap_eq (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f').homEquiv
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K))
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj K)
        ((derivedPullbackCompIsoLeft g' f' f g sq).hom.app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
          (derivedPullbackCompIsoCanonical g' f).inv.app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit.app K))
              :=
  Mate.derivedBaseChangeMap_eq (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
      (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) K

include sq in
/-- **The two readings of the derived pullback along the diagonal of a commutative square
agree.**  This is the functor equality `derivedPullbackCompIsoLeft` transports along, named so
that a consumer can present the *same* proof term rather than a second proof of the same
equality: `congrArg (fun q => derivedPullback q) sq` cannot be elaborated against a written-out
expected type, so every consumer has to be handed this one. -/
theorem derivedPullback_diagonal_eq :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f' ≫ g) =
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (g' ≫ f) :=
  congrArg (fun q : X' ⟶ S =>
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback q) sq.symm

/-- `derivedPullbackCompIsoLeft` is the composition isomorphism of Tag 0D5S followed by the
transport along the commutativity of the square.  One unfolding step. -/
theorem derivedPullbackCompIsoLeft_eq_trans :
    derivedPullbackCompIsoLeft g' f' f g sq =
      derivedPullbackCompIsoCanonical f' g ≪≫
        eqToIso (derivedPullback_diagonal_eq g' f' f g sq) :=
  rfl

/-- `derivedPullbackCompIsoLeft_eq_trans` read on the underlying transformation. -/
theorem derivedPullbackCompIsoLeft_hom_eq :
    (derivedPullbackCompIsoLeft g' f' f g sq).hom =
      (derivedPullbackCompIsoCanonical f' g).hom ≫
        (eqToIso (derivedPullback_diagonal_eq g' f' f g sq)).hom := by
  rw [derivedPullbackCompIsoLeft_eq_trans, Iso.trans_hom]

/-- `derivedPullbackCompIsoLeft_hom_eq` at an object.

*Why this is not proved by `rfl`.*  It is true by definition, but the kernel cannot check it that
way: unfolding `derivedPullbackCompIsoLeft` at a component reaches
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, which is
`derivedPullbackCompIso` at a dozen large arguments, and the check runs out of fuel.  The descent
has to be made one level at a time — the isomorphism, then the transformation, then the component
— with `Iso.trans_hom` and `CategoryTheory.NatTrans.comp_app` doing the last two steps
propositionally. -/
theorem derivedPullbackCompIsoLeft_hom_app
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (derivedPullbackCompIsoLeft g' f' f g sq).hom.app N =
      (derivedPullbackCompIsoCanonical f' g).hom.app N ≫
        (eqToIso (derivedPullback_diagonal_eq g' f' f g sq)).hom.app N := by
  rw [derivedPullbackCompIsoLeft_hom_eq]
  exact NatTrans.comp_app _ _ N

/-- **`derivedPullbackCompIsoLeft` at an object, with the transport read as a transport of
objects.**  The last factor of `derivedPullbackCompIsoLeft_hom_app` is the component of
`CategoryTheory.eqToIso` at `N`, and `StacksDraft.DerivedBaseChangeSplit.eqToIso_hom_app_eq`
presents it as `CategoryTheory.eqToHom` of any equation of the two objects.

The composition is assembled by `Eq.trans` and `congrArg` rather than by `rw`: the rewrite builds
a motive over the whole component and the kernel runs out of fuel on it, while this term costs
under a second. -/
theorem derivedPullbackCompIsoLeft_hom_app_eqToHom
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f' ≫ g)).obj N =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (g' ≫ f)).obj N) :
    (derivedPullbackCompIsoLeft g' f' f g sq).hom.app N =
      (derivedPullbackCompIsoCanonical f' g).hom.app N ≫ eqToHom e :=
  (derivedPullbackCompIsoLeft_hom_app g' f' f g sq N).trans
    (congrArg (fun m => (derivedPullbackCompIsoCanonical f' g).hom.app N ≫ m)
      (StacksDraft.DerivedBaseChangeSplit.eqToIso_hom_app_eq
        (derivedPullback_diagonal_eq g' f' f g sq) N e))

/-- **The adjoint characterization of the derived base change map, with the transport along the
commutativity of the square split off.**  `derivedBaseChangeMap_adjoint` with
`derivedPullbackCompIsoLeft` replaced, through `derivedPullbackCompIsoLeft_hom_app_eqToHom`, by
the composition isomorphism of Tag 0D5S followed by a transport of *objects*.

*Why a consumer needs this and cannot do the replacement itself.*  The kernel cannot convert the
`derivedPullbackCompIsoLeft` factor of `derivedBaseChangeMap_adjoint`'s right-hand side — as this
module elaborated it — into a copy of the same text elaborated in another module.  A
declaration whose statement is that composite equated to *itself*, at abstract ringed spaces and
an abstract complex, exceeds 200000 heartbeats when its proof is
`(derivedBaseChangeMap_adjoint …).symm.trans (derivedBaseChangeMap_adjoint …)`, and still does
when the equation is taken from `Mate.derivedBaseChangeMap_adjoint` instantiated at the use site;
the same statement proved by `rfl` costs nothing, and the composite's other two factors convert in
seconds.  Replacing the factor here, in the module that owns the definition, is free, and what
comes out does convert: the same self-equation stated with this composite and proved from this
lemma is checked in seconds. -/
theorem derivedBaseChangeMap_adjoint_split
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f' ≫ g)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (g' ≫ f)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K)) :
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f').homEquiv
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K))
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj K)).symm
        (derivedBaseChangeMap g' f' f g sq K) =
      ((derivedPullbackCompIsoCanonical f' g).hom.app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
          eqToHom e) ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              f).counit.app K) :=
  (derivedBaseChangeMap_adjoint g' f' f g sq K).trans
    (congrArg (fun m =>
        m ≫
          (derivedPullbackCompIsoCanonical g' f).inv.app
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                f).counit.app K))
      (derivedPullbackCompIsoLeft_hom_app_eqToHom g' f' f g sq
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) e))

/-- **The derived base change map as an adjoint transpose, with the transport along the
commutativity of the square split off.**  `derivedBaseChangeMap_eq` in the form a consumer can
use: the right-hand side mentions only
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` and a
`CategoryTheory.eqToHom`, and so can be matched against terms written elsewhere.  See
`derivedBaseChangeMap_adjoint_split` for why `derivedBaseChangeMap_eq` itself cannot. -/
theorem derivedBaseChangeMap_eq_split
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f' ≫ g)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (g' ≫ f)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K)) :
    derivedBaseChangeMap g' f' f g sq K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f').homEquiv
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K))
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').obj K)
        (((derivedPullbackCompIsoCanonical f' g).hom.app
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
            eqToHom e) ≫
          (derivedPullbackCompIsoCanonical g' f).inv.app
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K) ≫
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                f).counit.app K)) :=
  (Equiv.symm_apply_eq _).1 (derivedBaseChangeMap_adjoint_split g' f' f g sq K e)

/-- The derived base change map is natural in the complex. -/
theorem derivedBaseChangeMap_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (u : K ⟶ L) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map u) ≫
        derivedBaseChangeMap g' f' f g sq L =
      derivedBaseChangeMap g' f' f g sq K ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f').map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g').map u) :=
  Mate.derivedBaseChangeMap_naturality
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f')
      (derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) u

end Canonical

end

end Stacks.Cohomology.DerivedBaseChange

end
