module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartDirectImageUnitArrowSheafTransfer

/-!
# Splitting the sheaf-of-sets functor over a composite of direct images

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and write `𝒱` for `CategoryTheory.Sheaf.moduleSheafFunctor` at the structure sheaf.  The
arrows of the sequence of Stacks 03M8 for `𝒪`-modules are *composites* in
`AlgebraicGeometry.Space.Modules`, so reading one of them on underlying sheaves of sets means
splitting `𝒱.map` over such a composite.  The two factor comparisons of the first arrow are in
hand — `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_unit_app` for the
unit and `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` for the
composition comparison of Stacks 03LU — and what this file supplies is the splitting itself,
together with the spelling bridge the split composite then needs.

Asking for any of this *at* the composite is not affordable; asking for it at **variable modules
and variable arrows** is, and using the result at the composite is then an instantiation.  That is
the whole content of this file, and the implementation notes record which conversions are
affordable, including the one crossing that is not and where it sits.

## Main results

* `AlgebraicGeometry.Space.comp_congr₂`: congruence for a composite at the level of variables,
  used in place of `rw`, which abstracts a motive over the offending term.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_comp`:
  **`CategoryTheory.Functor.map_comp` for `CategoryTheory.Sheaf.moduleSheafFunctor` at a direct
  image of `𝒪`-modules**, proved once at variable modules and variable arrows, so that using it
  at a composite is an instantiation rather than a higher-order match.
* `AlgebraicGeometry.Space.moduleSheafFunctor_modulePushforward_comp_mid`: **the middle object of
  a composite of sheaves of sets may be read through the direct image of sheaves of sets instead
  of through the direct image of modules** — `𝒱(f_*N)` replaced by `f_*(𝒱N)`.  This is
  `AlgebraicGeometry.Space.moduleSheaf_modulePushforward` carried inside a composite, and it is
  the position in which the two spellings of the sequence of Stacks 03M8 meet.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_eq_comp`: **the whole splitting**, for an arrow
  *named* by a definition and for factor comparisons supplied as hypotheses: from `α = a ≫ κ`,
  `𝒱.map a = a'`, `𝒱.map κ = b'` and `β = a' ≫ b'` — the last read through the direct image of
  sheaves of sets — it concludes `𝒱.map α = β`.  Every crossing it performs is performed at
  variable modules.
* `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds_eq_comp`: the hub
  `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds` written out as its two
  factors, which is the shape the previous result wants its `β` in.

## Implementation notes

**Why the composite is formed in `Modules`.**  The composites the arrows of Stacks 03M8 are built
from live in `AlgebraicGeometry.Space.Modules`, while
`CategoryTheory.Sheaf.moduleSheafFunctor` is declared on `CategoryTheory.SheafOfModules` of the
structure sheaf.  These are the same category — `Modules` abbreviates exactly that
`SheafOfModules` — but a composite written as the *argument* of `𝒱.map` is elaborated at the
`SheafOfModules` spelling of the hom, and that is not the same term as one written at the
`Modules` spelling.  The statements below therefore ascribe the composite's type as
`(modulePushforward f).obj M ⟶ Q`, which is the spelling the arrows carry; without the ascription
the lemma is true and useless, since `rw` then reports that it cannot find the pattern
`Functor.map ?F (?a ≫ ?b)` in a goal that displays exactly that.

**What is affordable and what is not.**  The cost is always the same mechanism:
`CategoryTheory.CategoryStruct.comp` in `AlgebraicGeometry.Space.Modules` has an instance that is
not a structure literal, and
`AlgebraicGeometry.Space.etaleModulePullback` is built from an essential-image witness, so a
conversion that congruence cannot settle on the arguments reduces the composition itself and runs
into the structure maps of the small étale ringed topos and through a `Classical.choose`.  With
`diagnostics` on, one such `rfl` spends its whole budget unfolding
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` (15898 times),
`CategoryTheory.Functor.asEquivalence` (15405),
`CategoryTheory.Functor.sheafPushforwardContinuous` (14407),
`CategoryTheory.CategoryStruct.comp` (13638), `AlgebraicGeometry.Space.structureSheaf` (10394),
`Classical.choose` (6847) and `CategoryTheory.Functor.essImage.witness` (3265).

* **Objects are affordable.**  `(modulePushforward f).obj F = (modulePushforward f).obj ((𝟭 _).obj
  F)` and a `CategoryTheory.Functor.comp` delta under `(modulePushforward f).obj` are both `rfl`
  in well under a second: the two sides are applications of the same
  `CategoryTheory.Functor.obj`, so congruence settles them without reducing anything.
* **A composite's middle object is affordable at variable arrows, and only there.**  Both a
  `CategoryTheory.Functor.comp` delta and the crossing of
  `AlgebraicGeometry.Space.moduleSheaf_modulePushforward` in the middle of a composite are `rfl`
  in 0.7 s when the two factors are variables — that is
  `AlgebraicGeometry.Space.moduleSheafFunctor_modulePushforward_comp_mid` below.
* **A named arrow is never to be converted against its own body.**  Asking for
  `moduleChartDirectImageUnitArrow f hτ F = <its body, written out>` by `rfl` reports
  `(deterministic) timeout at 'whnf'`, and so does the same question with the body's type
  ascribed, with the body given through a `show`, and with the body named by a second definition
  carrying the same declared type.  The definition's own elaboration of that body is of course
  fine; it is the *comparison* of two elaborations of it that is not.  Use the arrow's equation
  lemma — `moduleChartDirectImageUnitArrow.eq_def` elaborates in a fraction of a second, and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_eq_comp` below takes it as the hypothesis `hα`
  for exactly this reason — or `rw`, which matches at reducible transparency and succeeds.

Nothing here raises a compiler limit or disables a linter.  Note that
`attribute [local implicit_reducible] Modules structureRingSheaf` is *not* a way out: both are
abbreviations, so the attribute is refused with `failed to set [local implicit_reducible],
'Modules' is currently [reducible]`, and the override it points at is a compiler option, which
this development does not use.

## What is not done

**The image under `𝒱` of the first arrow of Stacks 03M8 is not identified with the hub**, that is

`𝒱.map (moduleChartDirectImageUnitArrow f hτ F) =
  moduleSheafChartDirectImageUnitArrowModuleEnds f hτ F`

is not proved.  It is not a statement problem, nor a splitting problem: the gap is one
named conversion.  Writing `L = etaleModulePullback τ hτ` and `R = modulePushforward τ`, the four
hypotheses `AlgebraicGeometry.Space.moduleSheafFunctor_map_eq_comp` asks for are all available in
exactly the shapes it wants, each in a declaration that compiles: `hα` is
`moduleChartDirectImageUnitArrow.eq_def`; `hβ` is
`AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds_eq_comp` composed with
`AlgebraicGeometry.Space.moduleSheafFunctor_modulePushforward_comp_mid`; and `ha`, `hb` are the
two factor comparisons with their right-hand sides ascribed the module spelling.  Supplying `hα`
and `ha` succeeds **in 0.7 seconds**; supplying `hb` as well reports
`(deterministic) timeout at 'whnf'`.

**What that one conversion is, and the rule behind it.**  The splitting lemma reads the second
factor at `(modulePushforward f).obj ((L ⋙ R).obj F)`, because that is the middle object of the
composite that the arrow's own equation lemma produces, while
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` reads it at
`(R ⋙ modulePushforward f).obj (L.obj F)`.  The two are the same object, and reconciling them is
where the budget goes, because of the following rule — which is what all of the observations
above come down to:

> `isDefEq` between two applications of `CategoryTheory.Functor.obj` **with the same functor** is
> congruence, and costs nothing.  Between two applications with **different** functors it is not:
> the unifier unfolds the taller definition first, and `AlgebraicGeometry.Space.modulePushforward`
> is built from the structure map of the small étale ringed topos through a
> `CategoryTheory.Functor.essImage.witness`, hence a `Classical.choose`, so unfolding it does not
> terminate.  Reducing the `CategoryTheory.Functor.comp` projection instead would settle the
> question in one step, but it is the shorter definition and is not the one chosen.

That is also why every result in this file is stated at variable modules: there the two spellings
never meet.  Driving the whole chain by `rewrite` instead moves the same obstruction behind the
elaborator — **a complete proof is accepted** (in 37 s, no error) and the kernel then rejects the
declaration with `error: (kernel) deterministic timeout`, since `rw` matches up to conversion and
leaves the reconciliation inside its motive.

**The missing vocabulary** is therefore a reassociation bridge between those two readings.  The
obvious form of it is *not* enough: the clause

`(κ : (H ⋙ modulePushforward f).obj (G.obj N) ⟶ Q) → 𝒱.map κ = b' →
  @Functor.map _ _ _ _ 𝒱 ((modulePushforward f).obj ((G ⋙ H).obj N)) Q κ = b'`

— `CategoryTheory.Functor.comp_obj` twice, at variable functors `G`, `H` and a variable object
`N`, lifted into the implicit arguments of `𝒱.map`, with `b'` declared at `κ`'s own spelling — is
proved by `hb` and **compiles**; supplying the library's comparison for its `hb` at
`G = L`, `H = R`, `N = F` nevertheless reports `(deterministic) timeout at 'whnf'`, which leaves
the two `[Category]` instance arguments that the call site has to synthesize for `G`'s and `H`'s
source categories as the remaining suspect.  The alternative is the
**section-level** route: restate
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_comp` and
`AlgebraicGeometry.Space.moduleSheafFunctor_modulePushforward_comp_mid` on a single local section
`fun m ↦ m.hom.app W z` and reassemble with `CategoryTheory.Sheaf.hom_ext_sections`, the manoeuvre
that dissolved the composition comparison itself (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`); on sections a
composite is an application of functions rather than a `CategoryTheory.CategoryStruct.comp`, so
the offending object moves into the type of an intermediate section.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

section General

variable {C : Type*} [Category C]

/-- Congruence for a composite, at the level of variables: used instead of `rw`, which abstracts
a motive over the offending term. -/
theorem comp_congr₂ {A A' A'' : C} {a b : A ⟶ A'} {c d : A' ⟶ A''} (hab : a = b) (hcd : c = d) :
    a ≫ c = b ≫ d :=
  (congrArg (fun z ↦ z ≫ c) hab).trans (congrArg (fun z ↦ b ≫ z) hcd)

end General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-! ### The splitting -/

/-- **`CategoryTheory.Functor.map_comp` for `CategoryTheory.Sheaf.moduleSheafFunctor` at a direct
image of `𝒪`-modules**, at variable modules and variable arrows.

The composite is ascribed the type `(modulePushforward f).obj M ⟶ Q`, so that it is formed in
`AlgebraicGeometry.Space.Modules` and not at the `CategoryTheory.SheafOfModules` spelling of the
same category that `CategoryTheory.Sheaf.moduleSheafFunctor` carries.  The former is the spelling
the arrows of the sequence of Stacks 03M8 are written in, and without the ascription this
left-hand side cannot be found in any goal about them; see this file's implementation notes. -/
theorem moduleSheafFunctor_map_modulePushforward_comp (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (a : (modulePushforward B S hS f).obj M ⟶ (modulePushforward B S hS f).obj N)
    {Q : Modules.{u, u} B S hS Y.1 Y.2} (κ : (modulePushforward B S hS f).obj N ⟶ Q) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((a ≫ κ : (modulePushforward B S hS f).obj M ⟶ Q)) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map a ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map κ :=
  Functor.map_comp _ _ _

/-! ### The middle object of a split composite -/

/-- **The middle object of a composite of sheaves of sets may be read through the direct image of
sheaves of sets instead of through the direct image of modules**: `𝒱(f_*N)` may be replaced by
`f_*(𝒱N)`.

The two are the same sheaf of sets by `AlgebraicGeometry.Space.moduleSheaf_modulePushforward`, and
this carries that identification inside a composite, which is where the module spelling that
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_comp` produces meets the set
spelling that the factor comparisons of Stacks 03M8 and the hub
`AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds` carry.

It is stated at variable arrows because that is the only form in which it is affordable: with the
two factors variable this `rfl` is checked in under a second, and with them the concrete factors
of the first arrow of Stacks 03M8 the same conversion exhausts the kernel's budget.  See this
file's implementation notes. -/
theorem moduleSheafFunctor_modulePushforward_comp_mid (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    {Z : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)}
    (a : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj M) ⟶
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj N))
    (b : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj N) ⟶ Z) :
    a ≫ b =
      ((a : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
            ((modulePushforward B S hS f).obj M) ⟶
          (smallEtaleDirectImage B S hS f).obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)) ≫ b) :=
  rfl

/-- **The splitting of `𝒱.map` over a composite of direct images, assembled**: an arrow `α` of
`𝒪_Y`-modules which factors as `a ≫ κ` with `a` a direct image along `f`, together with readings
`a'` of `𝒱.map a` and `b'` of `𝒱.map κ` on underlying sheaves of sets, has `𝒱.map α` the
composite `a' ≫ b'` — and the composite is formed with its middle object through the direct image
of sheaves of sets, which is the spelling the arrows of Stacks 03M8 meet it in.

All four hypotheses are what makes this usable at a concrete arrow: `hα` is the arrow's own
equation, so that the named arrow is never converted against its body; `ha` and `hb` are the
factor comparisons; and `hβ` names the resulting composite, so that the one `moduleSheaf`/direct
image crossing is performed here, at variable modules, where it is affordable.  See this file's
implementation notes, and its "What is not done" for the one conversion this still leaves at the
first arrow of Stacks 03M8. -/
theorem moduleSheafFunctor_map_eq_comp (f : X ⟶ Y) {M N : Modules.{u, u} B S hS X.1 X.2}
    (a : (modulePushforward B S hS f).obj M ⟶ (modulePushforward B S hS f).obj N)
    {Q : Modules.{u, u} B S hS Y.1 Y.2} (κ : (modulePushforward B S hS f).obj N ⟶ Q)
    {α : (modulePushforward B S hS f).obj M ⟶ Q} (hα : α = a ≫ κ)
    {a' : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj M) ⟶
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj N)}
    (ha : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map a = a')
    {b' : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj N) ⟶
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj Q}
    (hb : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map κ = b')
    {β : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
          ((modulePushforward B S hS f).obj M) ⟶
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj Q}
    (hβ : β =
      ((a' : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
            ((modulePushforward B S hS f).obj M) ⟶
          (smallEtaleDirectImage B S hS f).obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)) ≫ b')) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map α = β :=
  ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map hα).trans
    ((moduleSheafFunctor_map_modulePushforward_comp B S hS f a κ).trans
      ((comp_congr₂ ha hb).trans
        (moduleSheafFunctor_modulePushforward_comp_mid B S hS f a' b')))).trans hβ.symm

/-! ### The hub of Stacks 03M8, written out -/

/-- **The hub `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds` is its two
factors**: the direct image along `f` of
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`, followed by the composition comparison of
Stacks 03G2, part (3), read at `𝒱_U(F|_U)`.

This is the hub's body, so the two sides are the same term and this `rfl` has only the hub's own
source and target crossings to check — the ones
`AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds_eq` already spends.  It is
the shape `AlgebraicGeometry.Space.moduleSheafFunctor_map_eq_comp` wants its `β` in. -/
theorem moduleSheafChartDirectImageUnitArrowModuleEnds_eq_comp (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleSheafChartDirectImageUnitArrowModuleEnds B S hS f hτ F =
      (smallEtaleDirectImage B S hS f).map (moduleSheafRestrictionUnitApp B S hS τ hτ F) ≫
        (smallToposMorphismTypeU_comp B S hS τ f).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).obj
            ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) :=
  rfl

end AlgebraicGeometry.Space

end
