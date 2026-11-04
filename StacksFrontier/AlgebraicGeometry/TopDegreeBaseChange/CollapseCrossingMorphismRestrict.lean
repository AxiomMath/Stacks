module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.RestrictionCollapseSquareTransport
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CollapseCrossingTransport

/-!
# The collapse crossing of [Stacks, Tag 0EX3] (c) at Mathlib's restricted morphism

`…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` (`CollapseCrossingGeometric.lean`)
crosses the two readings of Grothendieck's comparison of [Stacks, Tag 01XK] that the two sides of
conclusion (c) of [Stacks, Tag 0EX3] arrive in. It is stated at
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`, because that is the restricted morphism
the three abstract squares of `AffineCohomologyVanishing/` construct from `f` themselves. The `ψ`
side of (c) is stated at Mathlib's `f ∣_ V` throughout — see
`…TopDegreeBaseChange.prefix_transport_eq_openSubschemeSectionsComparison_comp` — and the two
spellings of the restricted morphism are equal only propositionally, by
`…SchemeHigherDirectImage.toShHom_morphismRestrict`.

This file builds the vocabulary in which the crossing can be *stated* at `f ∣_ V`: the cast
between the two spellings' right derived pushforwards, [Stacks, Tag 01E5] at `f ∣_ V` with that
cast packaged inside it, and the `f ∣_ V` form of the derived transport the restriction square is
applied at. With these, the whole crossing equation typechecks at the `ψ` side's own spelling,
which the notes of `BaseChangeSectionsTail.lean` describe as impossible; see this module's
implementation notes for which part of that claim holds.

## Main definitions

* `…TopDegreeBaseChange.higherDirectImageRestrictIsoMorphismRestrict` — **[Stacks, Tag 01E5] at
  Mathlib's restricted morphism, for `CategoryTheory.Functor.rightDerived`**: restricting a sheaf
  of modules to `f⁻¹V` and taking the `p`-th higher direct image along `f ∣_ V` agrees with taking
  the `p`-th higher direct image along `f` and restricting to `V`. It is the ringed-space
  `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso` transported along
  `rightDerived_modulePushforward_morphismRestrict`, and no `eqToHom` survives into its statement.
* `…TopDegreeBaseChange.restrictCollapseNatTransMorphismRestrict` and
  `…TopDegreeBaseChange.restrictCollapseTransportMorphismRestrict` — the `f ∣_ V` forms of
  `…TopDegreeBaseChange.restrictCollapseNatTrans` and `…restrictCollapseTransport`, the derived
  transport the restriction square is glued along.
* `…TopDegreeBaseChange.openSubschemePushforward` — **the pushforward along `f ∣_ V`, declared at
  the ringed-space spellings of its source and target.** This is the one declaration in which the
  two spellings of the two restricted spaces meet, and it is what makes the square statable at
  `f ∣_ V` without a kernel timeout; see the implementation notes.
* `…TopDegreeBaseChange.restrictCollapseNatTransAscribed` and
  `…TopDegreeBaseChange.restrictCollapseTransportAscribed` — the derived transport along
  `openSubschemePushforward`, at the association the restriction square writes its `τ` at.

## Main results

* `…TopDegreeBaseChange.rightDerived_modulePushforward_morphismRestrict` — **the cast.** The `p`-th
  right derived functor of the pushforward along `f ∣_ V` is the one along
  `…HigherDirectImage.restrictedMorphism`.
* `…TopDegreeBaseChange.restrictCollapseTransportMorphismRestrict_app` — the transport's reading on
  the chosen injective resolution, the shape the restriction square asks its `hτ` in.
* `…TopDegreeBaseChange.openSubschemePushforward_eq`,
  `…moduleRestriction_comp_openSubschemePushforward_eq` and
  `…moduleRestriction_comp_rightDerived_openSubschemePushforward_eq` — the three equalities the
  cast at variables asks for, at the ascription.
* `…TopDegreeBaseChange.restrictCollapseTransportAscribed_app` — the ascribed transport's reading
  on the chosen injective resolution.
* `…TopDegreeBaseChange.restrictCollapseSquare_morphismRestrict` — **the restriction-collapse
  square of [Stacks, Tag 01E5] against [Stacks, Tag 01E1], at Mathlib's `f ∣_ V`.**

## Implementation notes

*Why the cast cannot be `congrArg`, and why it is not vacuous.*
`congrArg RingedSpaceModuleAdjunction.modulePushforward (…toShHom_morphismRestrict f V)` is the
equality of the two *underived* pushforwards and typechecks as it stands. The derived equality does
not follow from it by `congrArg`: `CategoryTheory.Functor.rightDerived` takes the additivity of its
argument as an instance argument, so `fun F => F.rightDerived p` is not a function of the functor
alone. It is proved instead by rewriting along the morphism equality and closing the remaining goal
by `rfl` — the two sides are then syntactically equal and differ only in their additivity instance,
which is a proof of a `Prop`-valued class. Closing it needs `rfl` *written out*: `rw`'s own closing
`rfl` runs at reducible transparency and leaves the goal.

*The three spellings, and which of them is a real difference.* Between the crossing's `ψ`-side
factors and the ones the `ψ` side of (c) carries there are four differences.
`…TopDegreeBaseChange.openSubschemeRestriction f V` against
`…HigherDirectImage.moduleRestriction X (preimageOpen f V)`,
`…TopDegreeBaseChange.sectionsOnOpenSubschemeTop V` against
`…DerivedSectionsLeray.sectionsOverOpen (V : Scheme).toRingedSpace ⊤`, and
`…TopDegreeBaseChange.baseTopRestrictScalars V` against its `ModuleCat.restrictScalars` are each a
`def` and its body, so they unify in term position; only the restricted morphism is a genuine,
propositional difference, and it is what this file pays.

*Which spellings can be mixed.* The two
spellings cannot be *mixed*: with the index functor at `moduleRestriction X (preimageOpen f V)` and
the pushforward at `f ∣_ V`, the ambient category is pinned at the
`…HigherDirectImage.restrictToOpen` spelling and `(modulePushforward (f ∣_ V).toLRSHom.toShHom)`
`.Additive` is not synthesised; re-ascribing that instance does not help, because
`modulePushforward` determines its own source and target from the morphism, so neither a type
ascription nor naming the categories with `(C := …)` moves the instance's key. It does **not** follow that the
crossing's equation cannot be written at `f ∣_ V` at all. Written in the *pure* `f ∣_ V`
vocabulary — `openSubschemeRestriction f V`, `modulePushforward (f ∣_ V).toLRSHom.toShHom`,
`sectionsOverOpen (V : Scheme).toRingedSpace ⊤` and `baseTopRestrictScalars V`, which is the
vocabulary the `ψ` side of (c) actually carries — every category is the one the pushforward names
itself, every instance is found, and the whole equation elaborates. The one instance that was
missing is `(openSubschemeRestriction f V).PreservesInjectiveObjects`, declared below beside the
three re-ascriptions `LerayOpenSubschemeDerived.lean` already makes.

*How the equation is **not** proved.* `simp only [toShHom_morphismRestrict f V]` is not a proof
of it. Three facts about the elaborated statement:

1. `simp only [toShHom_morphismRestrict f V]` does **not** move the restricted morphism in it. It
   reports progress when definitions of this file are unfolded alongside, which is what makes the
   failure quiet; the goal it leaves still reads `f ∣_ V` at every occurrence.
2. `rw [toShHom_morphismRestrict f V]` is a motive failure, and the position that fails is named:
   `(openSubschemeTopSections V).obj` applied to
   `(openSubschemeRestriction f V ⋙ (modulePushforward (f ∣_ V).toLRSHom.toShHom).rightDerived p)`
   `.obj (E.obj Z)`, whose category the ascription of `openSubschemeTopSections` pins at
   `restrictToOpen Y.toSheafedSpace V` while the object is at `(V : Scheme).toSheafedSpace`. The
   two are definitionally equal and not syntactically, so abstracting the morphism is not type
   correct there. Writing that one factor at the unascribed
   `sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙ baseTopRestrictScalars V` removes *that*
   obstruction, but not the next: once the two definitions of this file are unfolded so that the
   morphism is exposed at all, their `eqToIso` proof terms mention the very equality being
   rewritten, and abstracting the morphism under an `eqToIso` is not type correct either.
3. Transporting the existing crossing forward instead and matching it against this statement by
   `exact` is a 200,000-heartbeat `whnf` timeout — the mismatch cannot even be pretty-printed.

*The route that discharges it.* A cancellation in
`StacksFrontier/CategoryTheory/CompositeCancellation.lean` taking the existing equation and the two
`eqToHom` conjugations to the conjugated one does **not** do it: a cancellation would *move* the cast onto the
other side of the equation, whereas hoisting the restricted pushforward onto a variable and
substituting *discharges* it. The cast at variables is
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square_of_eq`
(`AffineCohomologyVanishing/RestrictionCollapseSquareTransport.lean`).

What the instantiation at the geometric data then needed, and what this file's second half
supplies, is that **every crossing be paid in a declaration of its own, between single objects**.
In order:

* the two spellings still cannot be *mixed*: with the index functor at
  `moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V)` and the pushforward at
  `f ∣_ V`, `(modulePushforward (f ∣_ V).toLRSHom.toShHom).Additive` is not synthesised, exactly as
  recorded above;
* instantiating the cast directly at the pure `f ∣_ V` vocabulary — index functor, pushforward and
  outer functor all at the open subscheme — elaborates and is then a **`(kernel) deterministic
  timeout`**, which no raised heartbeat limit could reach;
* with the pushforward hoisted into `openSubschemePushforward` below, whose own declaration is the
  only place the two spellings of the two restricted spaces meet, the cast's conclusion is in the
  *ringed-space* vocabulary throughout and both the elaborator and the kernel accept the term;
* restating that conclusion by hand is then one single `isDefEq`, which `convert … using 2`
  closes by splitting it factor by factor, where `exact` is a 200,000-heartbeat `whnf` timeout.
  The statement on its own, and each of its three factors on its own, elaborate in seconds, so the
  cost was never the type identification but paying it at every implicit argument of the equation
  simultaneously.

*No `@[stacks …]` attribute is placed.* `higherDirectImageRestrictIsoMorphismRestrict` is a change
of spelling of [Stacks, Tag 01E5], which carries its tag where it is built, and conclusion (c) of
[Stacks, Tag 0EX3] is proved elsewhere, as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap`
(`BaseChangeTopDegreeConclusion.lean`), by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (toShHom_morphismRestrict)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)

/-! ### The cast between the two spellings of the restricted pushforward -/

/-- Restriction to the open subscheme `f⁻¹V` preserves injective objects, at the ascribed
spelling `…TopDegreeBaseChange.openSubschemeRestriction`. This is
`Stacks.Cohomology.HigherDirectImage.moduleRestriction_preservesInjectiveObjects` named at the
source and target `openSubschemeRestriction` declares, which is what
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` asks of its first factor at that
spelling. -/
instance openSubschemeRestriction_preservesInjectiveObjects :
    (openSubschemeRestriction f V).PreservesInjectiveObjects :=
  moduleRestriction_preservesInjectiveObjects X.toRingedSpace (f ⁻¹ᵁ V)

/-- **The `p`-th right derived pushforward along Mathlib's `f ∣_ V` is the one along the
ringed-space restricted morphism.** The two morphisms of sheaved spaces are equal, by
`…SchemeHigherDirectImage.toShHom_morphismRestrict`, but the equality of their right derived
pushforwards is not that equality's `congrArg`: `CategoryTheory.Functor.rightDerived` takes the
additivity of its argument as an instance argument. Nothing is assumed of `f` or of `V`. -/
theorem rightDerived_modulePushforward_morphismRestrict :
    (modulePushforward (f ∣_ V).toLRSHom.toShHom).rightDerived p =
      (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p := by
  rw [toShHom_morphismRestrict f V]
  rfl

/-- **[Stacks, Tag 01E5] at Mathlib's restricted morphism, for the `ℕ`-indexed right derived
functors.** Restricting a sheaf of `𝒪_X`-modules to `f⁻¹V` and taking the `p`-th higher direct
image along `f ∣_ V` agrees with taking the `p`-th higher direct image along `f` and restricting
to `V`, naturally in the module.

This is the ringed-space `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso`
transported along `rightDerived_modulePushforward_morphismRestrict`; nothing about 01E5 is
re-proved, and because the transport is an equality of functors no `eqToHom` survives into the
statement. It is the factor the crossing of conclusion (c) of [Stacks, Tag 0EX3] carries on the
side the `γ⁺` reading supplies, read at the spelling the `ψ` side meets it at. There is no
hypothesis on `f` and none on `V`. -/
def higherDirectImageRestrictIsoMorphismRestrict :
    openSubschemeRestriction f V ⋙
        (modulePushforward (f ∣_ V).toLRSHom.toShHom).rightDerived p ≅
      (modulePushforward f.toLRSHom.toShHom).rightDerived p ⋙
        moduleRestriction Y.toSheafedSpace V :=
  eqToIso (congrArg (openSubschemeRestriction f V ⋙ ·)
      (rightDerived_modulePushforward_morphismRestrict f V p)) ≪≫
    higherDirectImageRestrictIso f.toLRSHom.toShHom V p

/-! ### The derived transport of the restriction square, at `f ∣_ V` -/

/-- **[Stacks, Tag 01E5] underived, inverted and read under the outer functor, at Mathlib's
restricted morphism.** This is `CategoryTheory.Functor.whiskerRight` of
`…TopDegreeBaseChange.modulePushforwardMorphismRestrictIso` inverted and nothing else, with its
source and target declared at the association
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` writes them
at.

It is the `f ∣_ V` form of `…TopDegreeBaseChange.restrictCollapseNatTrans`, and the ascription is
where this file's one reassociation is paid: `whiskerRight` produces `(f_* ⋙ (-|_V)) ⋙ P` while
the square asks for `f_* ⋙ (-|_V) ⋙ P`, and crossing the two after
`CategoryTheory.Functor.rightDerived` has been applied is a 200,000-heartbeat `isDefEq` timeout,
whereas at the level of a transformation of degreewise functors it costs nothing. -/
def restrictCollapseNatTransMorphismRestrict :
    modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V ⟶
      openSubschemeRestriction f V ⋙
        modulePushforward (f ∣_ V).toLRSHom.toShHom ⋙
          sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙ baseTopRestrictScalars V :=
  Functor.whiskerRight (modulePushforwardMorphismRestrictIso f V).inv
    (sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙ baseTopRestrictScalars V)

/-- **The derived transport the restriction square is applied at, at Mathlib's restricted
morphism**: the `p`-th right derived functor of `restrictCollapseNatTransMorphismRestrict`. This is
the `f ∣_ V` form of `…TopDegreeBaseChange.restrictCollapseTransport`. -/
def restrictCollapseTransportMorphismRestrict :
    (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).rightDerived p ⟶
      (openSubschemeRestriction f V ⋙
        modulePushforward (f ∣_ V).toLRSHom.toShHom ⋙
          sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙
            baseTopRestrictScalars V).rightDerived p :=
  NatTrans.rightDerived (restrictCollapseNatTransMorphismRestrict f V) p

/-- **The reading of `restrictCollapseTransportMorphismRestrict` on the chosen injective
resolution**, which is the shape
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` asks its
defining hypothesis `hτ` in. This is `CategoryTheory.InjectiveResolution.rightDerived_app_eq` and
nothing else. -/
theorem restrictCollapseTransportMorphismRestrict_app
    (M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) :
    (restrictCollapseTransportMorphismRestrict f V p).app M =
      ((injectiveResolution M).isoRightDerivedObj
          (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
            openSubschemeTopSections V) p).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((restrictCollapseNatTransMorphismRestrict f V).mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex) ≫
          ((injectiveResolution M).isoRightDerivedObj
            (openSubschemeRestriction f V ⋙
              modulePushforward (f ∣_ V).toLRSHom.toShHom ⋙
                sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙
                  baseTopRestrictScalars V) p).inv :=
  InjectiveResolution.rightDerived_app_eq (restrictCollapseNatTransMorphismRestrict f V)
    (injectiveResolution M) p

/-! ### The square at Mathlib's restricted morphism

The restriction-collapse square is stated at the ringed-space `…HigherDirectImage
.restrictedMorphism`. Instantiating its transport
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square_of_eq`
directly at the *pure* `f ∣_ V` vocabulary — every category at the open subscheme — elaborates and
is then a `(kernel) deterministic timeout`. The cure is that the two spellings of the two
restricted spaces meet in **one declaration of their own**, `openSubschemePushforward`, after which
everything the square sees is in its own vocabulary. -/

section Ascription

open Stacks.Cohomology.AffineBase
  (rightDerivedCompNatIso rightDerivedCompNatIso_restrictChosenResolution_square_of_eq)
open Stacks.Cohomology.CompositeRightDerived (compRightDerivedNatIso)

variable {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))

/-- **The pushforward along Mathlib's `f ∣_ V`, declared at the ringed-space spellings of its
source and target.** This is `RingedSpaceModuleAdjunction.modulePushforward (f ∣_ V).toLRSHom
.toShHom` and nothing else; what the declaration adds is that the two identifications

> `restrictToOpen X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) = (f ⁻¹ᵁ V : Scheme)
> .toRingedSpace` and `restrictToOpen Y.toSheafedSpace V = (V : Scheme).toRingedSpace`

are paid here, once, between single spaces, rather than inside every implicit argument of the
restriction square's equation at once. Both are `rfl` and cost nothing in this position; forcing
them simultaneously inside the equation is what the kernel cannot do. Nothing is assumed of `f`
or of `V`. -/
def openSubschemePushforward :
    SheafOfModules.{u} (structureSheafRing
        (restrictToOpen X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V))) ⥤
      SheafOfModules.{u} (structureSheafRing (restrictToOpen Y.toSheafedSpace V)) :=
  modulePushforward (f ∣_ V).toLRSHom.toShHom

/-- `openSubschemePushforward` is additive. This is the existing
`RingedSpaceModuleAdjunction.modulePushforward_additive`, named at the restricted morphism;
instance search does not find it at the declared spelling of the source and target, which is
the one measurement 3 of this module's implementation notes records. -/
instance openSubschemePushforward_additive : (openSubschemePushforward f V).Additive :=
  modulePushforward_additive (f ∣_ V).toLRSHom.toShHom

/-- **The cast, at the ascription**: the pushforward along `f ∣_ V` is the one along
`…HigherDirectImage.restrictedMorphism`. This is `congrArg` of
`…SchemeHigherDirectImage.toShHom_morphismRestrict`. -/
theorem openSubschemePushforward_eq :
    openSubschemePushforward f V = modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) :=
  congrArg modulePushforward (toShHom_morphismRestrict f V)

/-- The cast after restriction to `f⁻¹V`, underived — one of the two composite equalities the
restriction square's two `eqToIso`s are built from. It is a separate statement because
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square_of_eq`
substitutes its pushforward variable, which it may only do if the equality it substitutes along
occurs in no other hypothesis's type. -/
theorem moduleRestriction_comp_openSubschemePushforward_eq :
    moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        openSubschemePushforward f V =
      moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) :=
  congrArg (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙ ·)
    (openSubschemePushforward_eq f V)

/-- The cast after restriction to `f⁻¹V`, derived — the other composite equality. It is **not**
the `congrArg` of the underived one: `CategoryTheory.Functor.rightDerived` takes the additivity of
its argument as an instance argument, so it is the `congrArg` of
`rightDerived_modulePushforward_morphismRestrict` instead. -/
theorem moduleRestriction_comp_rightDerived_openSubschemePushforward_eq :
    moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        (openSubschemePushforward f V).rightDerived p =
      moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p :=
  congrArg (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙ ·)
    (rightDerived_modulePushforward_morphismRestrict f V p)

/-- **[Stacks, Tag 01E5] underived, inverted and read under the outer functor, at the
ascription.** This is `…TopDegreeBaseChange.modulePushforwardMorphismRestrictIso` written out at
the ringed-space spelling of its source: the conjugating `eqToIso` must be the one the restriction
square's `hτ` is instantiated at, namely
`moduleRestriction_comp_openSubschemePushforward_eq`, so that no crossing is left for the match of
`hτ` to perform. The source and target are declared at the association the square writes them
at. -/
def restrictCollapseNatTransAscribed :
    modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V ⟶
      moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        openSubschemePushforward f V ⋙ openSubschemeTopSections V :=
  Functor.whiskerRight
    (eqToIso (moduleRestriction_comp_openSubschemePushforward_eq f V) ≪≫
      modulePushforwardRestrictIso f.toLRSHom.toShHom V).inv
    (openSubschemeTopSections V)

/-- **The derived transport the restriction square is applied at, at the ascription**: the `p`-th
right derived functor of `restrictCollapseNatTransAscribed`. -/
def restrictCollapseTransportAscribed :
    (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).rightDerived p ⟶
      (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        openSubschemePushforward f V ⋙ openSubschemeTopSections V).rightDerived p :=
  NatTrans.rightDerived (restrictCollapseNatTransAscribed f V) p

/-- **The reading of `restrictCollapseTransportAscribed` on the chosen injective resolution**,
which is the shape the restriction square asks its defining hypothesis `hτ` in. This is
`CategoryTheory.InjectiveResolution.rightDerived_app_eq` and nothing else. -/
theorem restrictCollapseTransportAscribed_app
    (M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) :
    (restrictCollapseTransportAscribed f V p).app M =
      ((injectiveResolution M).isoRightDerivedObj
          (modulePushforward f.toLRSHom.toShHom ⋙ moduleRestriction Y.toSheafedSpace V ⋙
            openSubschemeTopSections V) p).hom ≫
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map
          (((restrictCollapseNatTransAscribed f V).mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution M).cocomplex) ≫
          ((injectiveResolution M).isoRightDerivedObj
            (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
              openSubschemePushforward f V ⋙ openSubschemeTopSections V) p).inv :=
  InjectiveResolution.rightDerived_app_eq (restrictCollapseNatTransAscribed f V)
    (injectiveResolution M) p

/-- **The restriction-collapse square of [Stacks, Tag 01E5] against [Stacks, Tag 01E1], at
Mathlib's `f ∣_ V`.** For a morphism of schemes `f : X ⟶ Y`, an open `V ⊆ Y`, an index functor
`E` into the modules on `X` and a degree `p`, the composite

> [Stacks, Tag 01E5] at `f ∣_ V` conjugated by the cast, under the outer functor
> `openSubschemeTopSections V`, then Grothendieck's collapse at the ambient pair
> `(f_*, (-|_V) ⋙ openSubschemeTopSections V)`, then `restrictCollapseTransportAscribed`

is

> Grothendieck's collapse at the restricted pair `((f ∣_ V)_*, openSubschemeTopSections V)`, then
> [Stacks, Tag 01E1]'s source edge at `((-|_{f⁻¹V}), (f ∣_ V)_* ⋙ openSubschemeTopSections V)`
> inverted.

This is `Stacks.Cohomology.AffineBase`
`.rightDerivedCompNatIso_restrictChosenResolution_square_of_eq` at
`Q = openSubschemePushforward f V`, with the three equalities of this section and with its
transport taken to be `restrictCollapseTransportAscribed`, whose `hτ` is
`restrictCollapseTransportAscribed_app`. **Nothing is assumed** of `f`, of `V`, of `E`, of `Z` or
of `p` beyond the two pointwise homology hypotheses the two collapses carry.

The proof closes the single remaining `isDefEq` with `convert … using 2`, which splits it factor
by factor; `exact` on the same term is a 200,000-heartbeat `whnf` timeout, while the statement and
each of its three factors elaborate in seconds on their own. -/
theorem restrictCollapseSquare_morphismRestrict
    (hamb : ∀ Z : Dc, (moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hres : ∀ Z : Dc, (openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((openSubschemePushforward f V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p))
    (Z : Dc)
    [(moduleRestriction Y.toSheafedSpace V ⋙
        openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [(openSubschemeTopSections V).PreservesLeftHomologyOf
      ((((openSubschemePushforward f V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p)] :
    (openSubschemeTopSections V).map
          ((eqToIso (moduleRestriction_comp_rightDerived_openSubschemePushforward_eq f V p) ≪≫
            higherDirectImageRestrictIso f.toLRSHom.toShHom V p).hom.app (E.obj Z)) ≫
        (rightDerivedCompNatIso E (modulePushforward f.toLRSHom.toShHom)
            (moduleRestriction Y.toSheafedSpace V ⋙
              openSubschemeTopSections V) p hamb).hom.app Z ≫
          (restrictCollapseTransportAscribed f V p).app (E.obj Z) =
      (rightDerivedCompNatIso (E ⋙ moduleRestriction X.toSheafedSpace
            (preimageOpen f.toLRSHom.toShHom V)) (openSubschemePushforward f V)
          (openSubschemeTopSections V) p hres).hom.app Z ≫
        (compRightDerivedNatIso
          (moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V))
          (openSubschemePushforward f V ⋙ openSubschemeTopSections V) p).inv.app (E.obj Z) := by
  have h := rightDerivedCompNatIso_restrictChosenResolution_square_of_eq
    f.toLRSHom.toShHom V E (openSubschemeTopSections V) p (openSubschemePushforward f V)
    (openSubschemePushforward_eq f V) (moduleRestriction_comp_openSubschemePushforward_eq f V)
    (moduleRestriction_comp_rightDerived_openSubschemePushforward_eq f V p) hamb hres
    (restrictCollapseTransportAscribed f V p) Z
    (restrictCollapseTransportAscribed_app f V p (E.obj Z))
  convert h using 2

end Ascription

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
