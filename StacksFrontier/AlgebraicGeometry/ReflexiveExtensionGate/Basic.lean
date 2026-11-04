module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction
public import StacksFrontier.AlgebraicGeometry.ReflexiveHullCriterion.Basic

/-!
# What an extension equivalence across a depth-two complement forces

[Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) asserts that on an integral
locally Noetherian scheme `X`, restriction to an open `U` whose complement consists of points
where the structure sheaf has depth at least two is an equivalence from the coherent reflexive
modules on `X` to those on `U`, with direct image as inverse, and that both functors are
identified -- after inclusion into all modules -- with the ordinary pullback and pushforward
along `U.ι`.

This file does two things.

First, it supplies the iso-transport lemmas for the properties that cut out the categories in
question.  All are unconditional: no coherence, no local Noetherianity, no integrality, and in
particular no passage through stalks.

Second, it records what an inhabitant of that packaged assertion forces.  Because the forward
functor is identified with `Scheme.Modules.pullback U.ι` and the inverse with
`Scheme.Modules.pushforward U.ι`, and because both functors land in the stated full
subcategories, the mere existence of the package implies that pullback and pushforward along
`U.ι` preserve coherence and reflexivity.  Those four statements are therefore lower bounds on
the assertion: it cannot be proved without them.  Two of them are the open-immersion instances
of [Stacks, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF).

## Main results

* `isReflexive_iff_of_iso` and the `ObjectProperty.IsClosedUnderIsomorphisms` instance for
  reflexivity: reflexivity transports along an isomorphism of modules, in the two forms a
  transport argument wants it.
* `isCoherent_of_iso`: coherence transports along an isomorphism, for the root coherence
  predicate.
* `DepthTwoExtension X U`: the packaged assertion of Tag 0EBJ, stated over library names.
* `isCoherent_pullback_of_extension`, `isReflexive_pullback_of_extension`,
  `isCoherent_pushforward_of_extension`, `isReflexive_pushforward_of_extension`: the four
  preservation statements an inhabitant forces.

## Implementation notes

`DepthTwoExtension` omits the depth hypothesis of the source statement on purpose: the four
consequences hold for *any* inhabitant, whatever the hypotheses under which it was obtained,
so stating them without the hypothesis makes the gating claim stronger and keeps the
hypothesis out of the covering set.  A proof of Tag 0EBJ produces an inhabitant under the
depth hypothesis and these theorems then apply to it.

The reflexivity predicate is `Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive`, which is
`IsIso` of the canonical map `toDoubleDual`.  That is the same predicate the source statement
uses: the map is pinned by its local evaluation formula, which is
`Stacks.AlgebraicGeometry.ReflexiveHull.toReflexiveHull_eq`.

Transport of reflexivity along a single isomorphism is
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_of_iso`, proved there from the fact that
an isomorphism is a retract in both directions.  It needs no hypothesis on the scheme or on the
modules, and the two forms recorded here are immediate from it.

## References

* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveHull

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveExtensionGate

variable {X : Scheme.{u}}

/-! ### Transport along an isomorphism -/

/-- Reflexivity is invariant under isomorphism. -/
theorem isReflexive_iff_of_iso {F G : X.Modules} (e : F ≅ G) :
    IsReflexive F ↔ IsReflexive G :=
  ⟨isReflexive_of_iso e, isReflexive_of_iso e.symm⟩

/-- Reflexivity, as a property of objects of the category of modules on a scheme, is closed
under isomorphisms. -/
instance isReflexive_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (fun F : X.Modules => IsReflexive F) where
  of_iso e hF := isReflexive_of_iso e hF

/-- **Coherence transports along an isomorphism of modules.**  This is the already-proved
closure of the root coherence predicate under isomorphisms, in the form a transport argument
wants it. -/
theorem isCoherent_of_iso {F G : X.Modules} (e : F ≅ G) (hF : F.IsCoherent) :
    G.IsCoherent :=
  ObjectProperty.prop_of_iso (fun M : SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent) e hF

/-! ### The packaged assertion, and what it forces -/

/-- Being coherent and reflexive, as a property of objects of the category of modules. -/
abbrev reflexiveCoherentProperty (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun F => F.IsCoherent ∧ IsReflexive F

/-- The full category of coherent reflexive modules on a scheme. -/
abbrev ReflexiveCoherentModules (X : Scheme.{u}) :=
  (reflexiveCoherentProperty X).FullSubcategory

/-- **The packaged assertion of Stacks Tag 0EBJ, over library names.**  An equivalence between
the coherent reflexive modules on `X` and those on an open `U`, together with natural
isomorphisms identifying its two functors -- after inclusion into all modules -- with pullback
and pushforward along `U.ι`.

The depth hypothesis of the source statement is deliberately absent: the consequences below
hold for any inhabitant. -/
abbrev DepthTwoExtension (X : Scheme.{u}) (U : X.Opens) :=
  Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
    (e.functor ⋙ ObjectProperty.ι (reflexiveCoherentProperty U.toScheme) ≅
        ObjectProperty.ι (reflexiveCoherentProperty X) ⋙ Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι (reflexiveCoherentProperty X) ≅
        ObjectProperty.ι (reflexiveCoherentProperty U.toScheme) ⋙
          Scheme.Modules.pushforward U.ι)

variable {U : X.Opens}

/-- The forward identification of an extension package, read on one object: the image of a
coherent reflexive module under the equivalence is isomorphic to its pullback along `U.ι`. -/
noncomputable def functorObjIso (p : DepthTwoExtension X U)
    (A : ReflexiveCoherentModules X) :
    (p.1.functor.obj A).obj ≅ (Scheme.Modules.pullback U.ι).obj A.obj :=
  p.2.1.app A

/-- The inverse identification of an extension package, read on one object: the preimage of a
coherent reflexive module under the equivalence is isomorphic to its pushforward along
`U.ι`. -/
noncomputable def inverseObjIso (p : DepthTwoExtension X U)
    (B : ReflexiveCoherentModules U.toScheme) :
    (p.1.inverse.obj B).obj ≅ (Scheme.Modules.pushforward U.ι).obj B.obj :=
  p.2.2.app B

/-- **An extension package forces pullback along `U.ι` to preserve coherence of coherent
reflexive modules.**  This is the open-immersion instance of Stacks Tag 0EBF, coherence of the
pullback, restricted to reflexive modules. -/
theorem isCoherent_pullback_of_extension (p : DepthTwoExtension X U)
    (F : X.Modules) (hc : F.IsCoherent) (hr : IsReflexive F) :
    ((Scheme.Modules.pullback U.ι).obj F).IsCoherent :=
  isCoherent_of_iso (functorObjIso p ⟨F, hc, hr⟩) (p.1.functor.obj ⟨F, hc, hr⟩).property.1

/-- **An extension package forces pullback along `U.ι` to preserve reflexivity of coherent
reflexive modules.**  This is the open-immersion instance of Stacks Tag 0EBF, reflexivity of
the pullback. -/
theorem isReflexive_pullback_of_extension (p : DepthTwoExtension X U)
    (F : X.Modules) (hc : F.IsCoherent) (hr : IsReflexive F) :
    IsReflexive ((Scheme.Modules.pullback U.ι).obj F) :=
  isReflexive_of_iso (functorObjIso p ⟨F, hc, hr⟩) (p.1.functor.obj ⟨F, hc, hr⟩).property.2

/-- **An extension package forces pushforward along `U.ι` to preserve coherence of coherent
reflexive modules.**  Unlike the pullback statements this one is genuinely global: it is the
assertion that a coherent reflexive module on `U` extends to a coherent module on `X`. -/
theorem isCoherent_pushforward_of_extension (p : DepthTwoExtension X U)
    (G : U.toScheme.Modules) (hc : G.IsCoherent) (hr : IsReflexive G) :
    ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent :=
  isCoherent_of_iso (inverseObjIso p ⟨G, hc, hr⟩) (p.1.inverse.obj ⟨G, hc, hr⟩).property.1

/-- **An extension package forces pushforward along `U.ι` to preserve reflexivity of coherent
reflexive modules.** -/
theorem isReflexive_pushforward_of_extension (p : DepthTwoExtension X U)
    (G : U.toScheme.Modules) (hc : G.IsCoherent) (hr : IsReflexive G) :
    IsReflexive ((Scheme.Modules.pushforward U.ι).obj G) :=
  isReflexive_of_iso (inverseObjIso p ⟨G, hc, hr⟩) (p.1.inverse.obj ⟨G, hc, hr⟩).property.2

/-- **The four preservation statements an extension package forces, together.**  Nothing about
the assertion of Tag 0EBJ can be proved below this: both of its functors are specified, and
both are required to land in the coherent reflexive modules. -/
theorem forced_preservation (p : DepthTwoExtension X U) :
    (∀ (F : X.Modules), F.IsCoherent → IsReflexive F →
        ((Scheme.Modules.pullback U.ι).obj F).IsCoherent ∧
          IsReflexive ((Scheme.Modules.pullback U.ι).obj F)) ∧
      ∀ (G : U.toScheme.Modules), G.IsCoherent → IsReflexive G →
        ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
          IsReflexive ((Scheme.Modules.pushforward U.ι).obj G) :=
  ⟨fun F hc hr =>
      ⟨isCoherent_pullback_of_extension p F hc hr,
        isReflexive_pullback_of_extension p F hc hr⟩,
    fun G hc hr =>
      ⟨isCoherent_pushforward_of_extension p G hc hr,
        isReflexive_pushforward_of_extension p G hc hr⟩⟩

end Stacks.AlgebraicGeometry.ReflexiveExtensionGate
