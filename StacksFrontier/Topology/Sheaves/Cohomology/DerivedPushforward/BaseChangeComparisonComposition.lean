module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeTranspose

/-!
# The comparison of the two iterated derived pushforwards is the pair of composition isomorphisms

For a commutative square of ringed spaces
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare` compares the two
routes from `X'` to `S`,

> `Rf_*(Rg'_* M) ⟶ Rg_*(Rf'_* M)`,

as the mate of the derived base change map under the derived adjunctions of the square's two
horizontal morphisms. `derivedPushforwardComparisonSquare_eq_conjugateEquiv` already identifies it
with the conjugate of the comparison of the two iterated derived *pullbacks*, which is how its
invertibility is seen. That identification still describes it through the pullback side, so it
says nothing about how the comparison meets a statement about derived *sections*, where only
pushforward data occurs.

This file removes the pullbacks from the description. The comparison of the two iterated derived
pullbacks is by construction a composite of two composition isomorphisms of [Stacks, Tag 0D5S],
and the conjugate of each of those is a composition isomorphism of [Stacks, Tag 079W] — that is
`…DerivedPushforwardAssociativity.conjugateEquiv_derivedPullbackCompIsoCanonical_inv`
and `conjugateEquiv_derivedPullbackCompIsoCanonical_hom`. Since `CategoryTheory.conjugateEquiv`
turns composition into composition, the comparison is

> `Rg'_* ⋙ Rf_* ≅ R(g' ≫ f)_* = R(f' ≫ g)_* ≅ Rf'_* ⋙ Rg_*`,

the composition isomorphism of [Stacks, Tag 079W] for `(g', f)`, the transport along the
commutativity of the square, and the inverse of the composition isomorphism for `(f', g)`.

This is the form in which a consumer reads the comparison over an open: the Leray comparison for
derived sections along a composite,
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp`, is stated through the composition
isomorphism of [Stacks, Tag 079W] and meets nothing else.

## Main results

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `Mate.derivedPushforwardComparisonSquare_eq_conjugateEquiv_comp`: **the comparison split at the
  common composite**, at variables of abstract adjunctions — given any adjunction `adjc` whose
  left part is the common value `Lc` of the two iterated derived pullbacks, the comparison is the
  conjugate of `ef.inv` followed by the conjugate of `eg.hom`.
* `conjugateEquiv_eqToHom_derivedPullback`: the conjugate of the transport between the derived
  pullbacks along two equal morphisms is the transport between the derived pushforwards.
* `conjugateEquiv_derivedPullbackCompIsoLeft_hom`: the conjugate of the left-hand comparison of
  iterated derived pullbacks is the transport along the square followed by the inverse of the
  composition isomorphism of [Stacks, Tag 079W] for `(f', g)`.
* `derivedPushforwardComparisonSquare_natTrans_eq_compIso`: **the comparison of the two iterated
  derived pushforwards of a commutative square of ringed spaces is the composition isomorphism of
  [Stacks, Tag 079W] for `(g', f)`, the transport along the square, and the inverse of the
  composition isomorphism for `(f', g)`**, with no hypothesis on the square beyond its
  commutativity.
* `derivedPushforwardComparisonSquare_app_eq_compIso`: the same at an object of the unbounded
  derived category.

## Implementation notes

*Why the split is stated at variables.* As everywhere in this directory, the rearrangement is
carried out where every functor is a variable: `CategoryTheory.conjugateEquiv_comp` is applied
once, with the adjunction along the common composite supplied as an argument, so that the only
thing done at the concrete spelling of an iterated derived functor is one instantiation.

*Why the transport survives in the conclusion.* `derivedPullbackCompIsoLeft` identifies
`Lg^* ⋙ Lf'^*` with the derived pullback along `g' ≫ f` rather than along `f' ≫ g`, and carries
a transport along the square's commutativity to do so. Its conjugate therefore carries the
matching transport between `R(g' ≫ f)_*` and `R(f' ≫ g)_*`, and no choice of spelling removes
it: the two composites are equal but not syntactically so. The transport is identified by
substituting the equation, which is why `conjugateEquiv_eqToHom_derivedPullback` is stated at an
arbitrary equality of morphisms rather than at `sq` — `CategoryTheory.eqToHom` between two
*functors* is the shape whose kernel cost `BaseChangePasting.lean` records, and after a
substitution nothing about it has to be decided.

*The component identity is derived from the identity of natural transformations.* A `Mate`
two-square is reconciled at functor level and never at `.app`, the measurement
`PushforwardComparisonAgreesWithOrdinary.lean` records; the component statement is therefore one
`CategoryTheory.NatTrans.congr_app` of the functor-level one, with the transport pushed onto the
object by `eqToHom_derivedPushforward_app`.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardAssociativity

namespace Stacks.Cohomology.DerivedBaseChange

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

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
  {Rc : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Rg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The comparison of the two iterated derived pushforwards, split at the common composite.**
Given in addition an adjunction `adjc : Lc ⊣ Rc` for the functor both iterated derived pullbacks
are identified with, the comparison `Rg'_* ⋙ Rf_* ⟶ Rf'_* ⋙ Rg_*` is the conjugate of `ef.inv`
followed by the conjugate of `eg.hom`.

The comparison is the conjugate of `eg.hom ≫ ef.inv`
(`derivedPushforwardComparisonSquare_eq_conjugateEquiv`) and `CategoryTheory.conjugateEquiv`
turns composition into composition, so the only step is `CategoryTheory.conjugateEquiv_comp` at
`adjc`. Stated at variables of abstract adjunctions, where it costs nothing; a consumer
instantiates `adjc` at the derived adjunction along the square's common composite. -/
theorem derivedPushforwardComparisonSquare_eq_conjugateEquiv_comp (adjc : Lc ⊣ Rc) :
    (derivedPushforwardComparisonSquare adjf adjf' adjg adjg' eg ef) =
      conjugateEquiv (adjf.comp adjg') adjc ef.inv ≫
        conjugateEquiv adjc (adjg.comp adjf') eg.hom :=
  (derivedPushforwardComparisonSquare_eq_conjugateEquiv adjf adjf' adjg adjg' eg ef).trans
    (conjugateEquiv_comp (adjf.comp adjg') adjc (adjg.comp adjf') ef.inv eg.hom).symm

end Mate

section Canonical

/-- Two composites agree when their factors do. Stated at variables of an abstract category, so
that the identities below are assembled without a rewrite inside a composite of derived
functors. -/
private lemma comp_congr {C : Type*} [Category* C] {A B D : C} {a a' : A ⟶ B} {b b' : B ⟶ D}
    (ha : a = a') (hb : b = b') : a ≫ b = a' ≫ b' := by
  rw [ha, hb]

/-- **The conjugate of a transport between derived pullbacks is the transport between derived
pushforwards.** For two equal morphisms of ringed spaces `a = b`, the transport
`Lb^* ⟶ La^*` corresponds, under the two derived adjunctions, to the transport
`Ra_* ⟶ Rb_*`.

Proved by substituting the equation, after which both sides are identities and the statement is
`CategoryTheory.conjugateEquiv_id`. No equality of total derived functors is decided, which is
what `BaseChangePasting.lean` records as unaffordable. -/
theorem conjugateEquiv_eqToHom_derivedPullback {A C : RingedSpace.{u, u}} {a b : A ⟶ C}
    (hab : a = b) :
    conjugateEquiv (derivedAdjunction a) (derivedAdjunction b)
        (eqToHom (congrArg (fun k : A ⟶ C => derivedPullback k) hab.symm)) =
      eqToHom (congrArg (fun k : A ⟶ C => derivedPushforward k) hab) := by
  subst hab
  simp

/-- The transport between the derived pushforwards along two equal morphisms, read at an object
of the unbounded derived category. -/
private theorem eqToHom_derivedPushforward_app {A C : RingedSpace.{u, u}} {a b : A ⟶ C}
    (hab : a = b) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing A))) :
    (eqToHom (congrArg (fun k : A ⟶ C => derivedPushforward k) hab)).app M =
      eqToHom (congrArg (fun k : A ⟶ C => (derivedPushforward k).obj M) hab) := by
  subst hab
  simp

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g)

/-- **The conjugate of the left-hand comparison of iterated derived pullbacks.** Under the
derived adjunction along the square's common composite and the composite derived adjunction
along the bottom, `derivedPullbackCompIsoLeft` — the identification of `Lg^* ⋙ Lf'^*` with the
derived pullback along `g' ≫ f` — corresponds to the transport along the commutativity of the
square followed by the inverse of the composition isomorphism of [Stacks, Tag 079W] for
`(f', g)`.

Its two factors are `conjugateEquiv_eqToHom_derivedPullback` for the transport and
`conjugateEquiv_derivedPullbackCompIsoCanonical_hom` for the composition isomorphism; the split
is `CategoryTheory.conjugateEquiv_comp` at the derived adjunction along `f' ≫ g`. This carries
one cost of its own — abstracting `derivedPullbackCompIsoLeft` inside a `conjugateEquiv` — and
so is a declaration of its own, the per-declaration budget this directory measures being what it
is. -/
theorem conjugateEquiv_derivedPullbackCompIsoLeft_hom :
    conjugateEquiv (derivedAdjunction (g' ≫ f))
        ((derivedAdjunction g).comp (derivedAdjunction f'))
        (derivedPullbackCompIsoLeft g' f' f g sq).hom =
      eqToHom (congrArg (fun k : X' ⟶ S => derivedPushforward k) sq) ≫
        (derivedPushforwardCompIso f' g).inv :=
  (congrArg (fun x => conjugateEquiv (derivedAdjunction (g' ≫ f))
        ((derivedAdjunction g).comp (derivedAdjunction f')) x)
      (derivedPullbackCompIsoLeft_hom_eq g' f' f g sq)).trans
    ((conjugateEquiv_comp (derivedAdjunction (g' ≫ f)) (derivedAdjunction (f' ≫ g))
          ((derivedAdjunction g).comp (derivedAdjunction f'))
          (eqToHom (congrArg (fun k : X' ⟶ S => derivedPullback k) sq.symm))
          (derivedPullbackCompIsoCanonical f' g).hom).symm.trans
      (comp_congr (conjugateEquiv_eqToHom_derivedPullback sq)
        (conjugateEquiv_derivedPullbackCompIsoCanonical_hom f' g)))

/-- **The comparison of the two iterated derived pushforwards around a commutative square of
ringed spaces is the pair of composition isomorphisms of [Stacks, Tag 079W].** For
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
the comparison `Rg'_* ⋙ Rf_* ⟶ Rf'_* ⋙ Rg_*` is

> `Rg'_* ⋙ Rf_* ≅ R(g' ≫ f)_* = R(f' ≫ g)_* ≅ Rf'_* ⋙ Rg_*`,

the composition isomorphism of [Stacks, Tag 079W] for `(g', f)`, the transport along the
commutativity of the square, and the inverse of the composition isomorphism for `(f', g)`. There
is no hypothesis on the square beyond `sq`, and no derived pullback occurs on the right-hand
side.

The two factors are the two factors of the comparison of the two iterated derived pullbacks read
through `CategoryTheory.conjugateEquiv`:
`…DerivedPushforwardAssociativity.conjugateEquiv_derivedPullbackCompIsoCanonical_inv`
for the first and `conjugateEquiv_derivedPullbackCompIsoLeft_hom` for the second. -/
theorem derivedPushforwardComparisonSquare_natTrans_eq_compIso :
    (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedAdjunction g) (derivedAdjunction g')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (derivedPullbackCompIsoCanonical g' f)) =
      (derivedPushforwardCompIso g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ S => derivedPushforward k) sq) ≫
          (derivedPushforwardCompIso f' g).inv :=
  (Mate.derivedPushforwardComparisonSquare_eq_conjugateEquiv_comp (derivedAdjunction f)
      (derivedAdjunction f') (derivedAdjunction g) (derivedAdjunction g')
      (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f)
      (derivedAdjunction (g' ≫ f))).trans
    (comp_congr (conjugateEquiv_derivedPullbackCompIsoCanonical_inv g' f)
      (conjugateEquiv_derivedPullbackCompIsoLeft_hom g' f' f g sq))

/-- **The comparison of the two iterated derived pushforwards at an object**, written through the
two composition isomorphisms of [Stacks, Tag 079W]. This is
`derivedPushforwardComparisonSquare_natTrans_eq_compIso` read at a complex, with the transport
pushed onto the object. -/
theorem derivedPushforwardComparisonSquare_app_eq_compIso
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
          (derivedAdjunction g) (derivedAdjunction g')
          (derivedPullbackCompIsoLeft g' f' f g sq)
          (derivedPullbackCompIsoCanonical g' f)).app M =
      (derivedPushforwardCompIso g' f).hom.app M ≫
        eqToHom (congrArg (fun k : X' ⟶ S => (derivedPushforward k).obj M) sq) ≫
          (derivedPushforwardCompIso f' g).inv.app M := by
  have h := congr_app (derivedPushforwardComparisonSquare_natTrans_eq_compIso g' f' f g sq) M
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_derivedPushforward_app sq M] at h
  exact h

end Canonical

end

end Stacks.Cohomology.DerivedBaseChange

end
