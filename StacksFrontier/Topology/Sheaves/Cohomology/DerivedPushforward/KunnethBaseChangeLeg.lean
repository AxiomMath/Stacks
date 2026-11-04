module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap

/-!
# The base-change leg of the Künneth map is the derived base-change map of Stacks 08HY

The second input of the first proof of Tag 0FLQ is the base-change comparison

`La^* Rb_* M ⟶ Rp_* Lq^* M`

of a commutative square `q ≫ b = p ≫ a` of ringed spaces.  The Künneth development builds it as
`Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg`, the adjoint transpose under
`Lp^* ⊣ Rp_*` of the second counit leg of the Künneth map; the base-change development builds it
as `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, the mate of the comparison of the
two iterated derived pullbacks around the square.  This file proves that the two are the same
morphism.

Nothing new is constructed here.  The point is that the hypothesis `hbase` of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` is stated
with the first spelling, while every invertibility result for the base-change comparison in this
repository — the open-immersion case, the closed-immersion case, the chartwise Tor-independence
input of Stacks 08IB and the global statement of Stacks 08IB itself — is stated with the second.

## Main results

* `Stacks.Cohomology.DerivedKunneth.homEquiv_leg_eq_of_eq`: the identification at the level of
  abstract adjunctions, where its content lies.
* `Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg_eq_derivedBaseChangeMap`: the two
  spellings agree, for every square and every derived module, with no hypothesis beyond the
  commutativity `q ≫ b = p ≫ a` that both constructions take as data.
* `Stacks.Cohomology.DerivedKunneth.isIso_kunnethBaseChangeLeg_iff` and
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethBaseChangeLeg_of_isIso_derivedBaseChangeMap`:
  the resulting equivalence of the two invertibility statements.

## Implementation notes

*Why the two definitions agree.*  Both are the transpose under `Lp^* ⊣ Rp_*` of a composite out
of `L(p ≫ a)^* Rb_* M`, and the legs match pairwise: the composition isomorphism of Stacks 0D5S
for `(p, a)` with the first factor of
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`, the transport along
`p ≫ a = q ≫ b` with the `eqToIso` that definition composes onto it, and the whiskered inverse
composition isomorphism for `(q, b)` with the counit of `Lb^* ⊣ Rb_*` inside
`Stacks.Cohomology.DerivedKunneth.pullbackCounitLegComp`.  Once the transport is substituted away
the two composites differ by an associator, a left unitor and one bracketing, all of which `simp`
removes.

*Why the comparison is abstract, and why the three concrete steps avoid `.app`.*  The content is
proved once in `homEquiv_leg_eq_of_eq`, over arbitrary categories, functors and adjunctions, and
the geometric statement is a single application of it.  The three concrete inputs —
`pullbackCounitLeg_eq`, `pullbackCounitLegComp_eq` and `derivedPullbackCompIsoLeft_eq` — are
equalities of natural transformations and of isomorphisms, not of their components.

That shape is forced.  At the derived functors of module sheaves the kernel exceeds its budget on
any definitional equality it must settle by reducing a component projection `α.app M` through the
structure of the functor category, because that forces weak-head reduction of the category
instance of `DerivedCategory (SheafOfModules ..)` underneath; the same equalities stated one level
up, between the transformations themselves, are settled by delta reduction alone and cost nothing.
Stated at an object, each step fails in the kernel.  So every passage to a component here is a lemma application inside the abstract proof, and
the only obligations left at the geometric statement are the delta unfoldings of
`kunnethBaseChangeLeg` and of `derivedBaseChangeMap_eq`'s right-hand side.  This is the
phenomenon the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeMap.lean` record for the
mate layer, with the same remedy.

*The commutativity proof is irrelevant.*  `q ≫ b = p ≫ a` is a `Prop`, so the two constructions
may be fed the same proof term, and a client holding any other proof of it gets the same
morphism.

## References

* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedBaseChange

universe u

namespace Stacks.Cohomology.DerivedKunneth

/-- **The transpose of a transported counit leg is the transpose of the mate's composite.**

Let `adjf : Lf ⊣ Rf` and `adjf' : Lf' ⊣ Rf'` be adjunctions, `Lg` and `Lg'` further functors,
`eg' : Lg ⋙ Lf' ≅ Lc'` and `ef : Lf ⋙ Lg' ≅ Lc` isomorphisms, and `hLc : Lc' = Lc` an equality
with `hRfLc : Rf ⋙ Lc' = Rf ⋙ Lc` the induced one.  Suppose given

* `legComp : Rf ⋙ Lc ⟶ Lg'` equal to the whiskered `ef.inv`, the associator, the whiskered
  counit of `adjf` and the left unitor (`hlegComp`);
* `leg : Rf ⋙ Lc' ⟶ Lg'` equal to the transport along `hRfLc` followed by `legComp` (`hleg`);
* `egL : Lg ⋙ Lf' ≅ Lc` equal to `eg'` followed by the transport along `hLc` (`hegL`).

Then the transpose under `adjf'` of `eg'` followed by `leg` equals the transpose of `egL`
followed by `ef.inv` and `Lg'` of the counit.

The first expression is the shape of `Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg`, with
`leg` the counit leg of the Künneth map, and the second is the shape of
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` through
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq`, with `egL` the left iterated
pullback of the square.  Nothing about ringed spaces or derived categories enters, which is why
this is where the identification is proved.

`legComp`, `leg` and `egL` are parameters constrained by equations, rather than being written out
in the statement, so that a client may pass its own three definitions and leave the kernel only
their delta unfoldings.  `hLc` and `hRfLc` are independent for the same reason; being proofs of
propositions, they lose no generality. -/
theorem homEquiv_leg_eq_of_eq {C D E F : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] {Lg : C ⥤ D} {Lf' : D ⥤ E} {Rf' : E ⥤ D} {Lf : C ⥤ F} {Rf : F ⥤ C}
    {Lg' : F ⥤ E} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') {Lc Lc' : C ⥤ E}
    (eg' : Lg ⋙ Lf' ≅ Lc') (hLc : Lc' = Lc) (hRfLc : (Rf ⋙ Lc' : F ⥤ E) = Rf ⋙ Lc)
    (ef : Lf ⋙ Lg' ≅ Lc) (legComp : Rf ⋙ Lc ⟶ Lg')
    (hlegComp : legComp =
      Functor.whiskerLeft Rf ef.inv ≫
        (Functor.associator Rf Lf Lg').inv ≫
        Functor.whiskerRight adjf.counit Lg' ≫
        (Functor.leftUnitor Lg').hom)
    (leg : Rf ⋙ Lc' ⟶ Lg') (hleg : leg = eqToHom hRfLc ≫ legComp)
    (egL : Lg ⋙ Lf' ≅ Lc) (hegL : egL = eg' ≪≫ eqToIso hLc) (K : F) :
    adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)
        (eg'.hom.app (Rf.obj K) ≫ leg.app K) =
      adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)
        (egL.hom.app (Rf.obj K) ≫
          ef.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K)) := by
  subst hegL
  subst hleg
  subst hlegComp
  subst hLc
  have hrefl : hRfLc = rfl := rfl
  subst hrefl
  simp

attribute [local instance] HasDerivedCategory.standard

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (hq : q ≫ b = p ≫ a)

/-- The counit leg `L(q ≫ b)^* Rb_* ⟶ Lq^*` of Stacks 0D5S and Stacks 079W, written out: the
whiskered inverse composition isomorphism for `(q, b)`, the associator, the whiskered counit of
`Lb^* ⊣ Rb_*` and the left unitor.  This is the definition of `pullbackCounitLegComp`, recorded
as an equation of natural transformations so that it may be handed to `homEquiv_leg_eq_of_eq`. -/
theorem pullbackCounitLegComp_eq :
    pullbackCounitLegComp b q =
      Functor.whiskerLeft (derivedPushforward b)
          (derivedPullbackCompIsoCanonical q b).inv ≫
        (Functor.associator (derivedPushforward b) (derivedPullback b)
          (derivedPullback q)).inv ≫
        Functor.whiskerRight (derivedAdjunction b).counit (derivedPullback q) ≫
        (Functor.leftUnitor (derivedPullback q)).hom :=
  rfl

/-- The counit leg of the Künneth map at the factorization `q ≫ b = p ≫ a`: the transport in the
functor category along that equality, followed by the leg for the composite `q ≫ b`.  This is the
definition of `pullbackCounitLeg`. -/
theorem pullbackCounitLeg_eq :
    pullbackCounitLeg b q (p ≫ a) hq =
      eqToHom (congrArg (fun z : W ⟶ S =>
          derivedPushforward b ⋙ derivedPullback z) hq.symm) ≫
        pullbackCounitLegComp b q :=
  rfl

/-- The iterated derived pullback down the left of the square: the composition isomorphism of
Stacks 0D5S for `(p, a)` followed by the transport along `p ≫ a = q ≫ b`.  This is the definition
of `derivedPullbackCompIsoLeft`. -/
theorem derivedPullbackCompIsoLeft_eq :
    derivedPullbackCompIsoLeft q p b a hq =
      derivedPullbackCompIsoCanonical p a ≪≫
        eqToIso (congrArg (fun z : W ⟶ S => derivedPullback z) hq.symm) :=
  rfl

/-- **The base-change leg of the Künneth map is the derived base-change map of Stacks 08HY.**

For `a : X ⟶ S`, `b : Y ⟶ S`, `p : W ⟶ X`, `q : W ⟶ Y` morphisms of ringed spaces with
`q ≫ b = p ≫ a`, and for every `M` in the unbounded derived category of `𝒪_Y`-modules, the
comparison `La^* Rb_* M ⟶ Rp_* Lq^* M` built in the Künneth development as the adjoint transpose
of the second counit leg is the canonical derived base-change map of the square.

There is no hypothesis beyond the commutativity of the square, which both constructions take as
data; in particular nothing is assumed of `M`, of the four spaces, or of the four morphisms.

The proof is `homEquiv_leg_eq_of_eq` at the two derived adjunctions of `b` and of `p`, the
composition isomorphisms of Stacks 0D5S for `(p, a)` and for `(q, b)`, the transport along
`p ≫ a = q ≫ b` and the three equations above, followed by
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq`. -/
theorem kunnethBaseChangeLeg_eq_derivedBaseChangeMap
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethBaseChangeLeg a b p q hq M = derivedBaseChangeMap q p b a hq M :=
  (homEquiv_leg_eq_of_eq (derivedAdjunction b) (derivedAdjunction p)
      (derivedPullbackCompIsoCanonical p a)
      (congrArg (fun z : W ⟶ S => derivedPullback z) hq.symm)
      (congrArg (fun z : W ⟶ S => derivedPushforward b ⋙ derivedPullback z) hq.symm)
      (derivedPullbackCompIsoCanonical q b)
      (pullbackCounitLegComp b q) (pullbackCounitLegComp_eq b q)
      (pullbackCounitLeg b q (p ≫ a) hq) (pullbackCounitLeg_eq a b p q hq)
      (derivedPullbackCompIsoLeft q p b a hq)
      (derivedPullbackCompIsoLeft_eq a b p q hq) M).trans
    (derivedBaseChangeMap_eq q p b a hq M).symm

/-- **The two invertibility statements agree.**  The base-change leg of the Künneth map of the
square `q ≫ b = p ≫ a` is invertible exactly when the derived base-change map of Stacks 08HY of
that square is, so a result about the one applies to the other.  This is the form in which the
hypothesis `hbase` of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange` is
discharged. -/
theorem isIso_kunnethBaseChangeLeg_iff
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (kunnethBaseChangeLeg a b p q hq M) ↔
      IsIso (derivedBaseChangeMap q p b a hq M) :=
  iff_of_eq (congrArg IsIso (kunnethBaseChangeLeg_eq_derivedBaseChangeMap a b p q hq M))

/-- The base-change leg of the Künneth map is invertible as soon as the derived base-change map
of Stacks 08HY of the same square is, which is the direction every geometric input supplies. -/
theorem isIso_kunnethBaseChangeLeg_of_isIso_derivedBaseChangeMap
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (derivedBaseChangeMap q p b a hq M)) :
    IsIso (kunnethBaseChangeLeg a b p q hq M) :=
  (isIso_kunnethBaseChangeLeg_iff a b p q hq M).2 h

end Stacks.Cohomology.DerivedKunneth

end
