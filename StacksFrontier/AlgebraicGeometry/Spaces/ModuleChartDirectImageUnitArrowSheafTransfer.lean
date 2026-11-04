module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartUnitArrowSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardPresentationArrows

/-!
# The first arrow of Stacks 03M8 on underlying sheaves of sets

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `τ : U ⟶ X` be étale, put `a = τ ≫ f`, and write `𝒱` for
`CategoryTheory.Sheaf.moduleSheafFunctor` at the structure sheaf.  The first arrow
`f_*F ⟶ a_*(F|_U)` of the sequence of Stacks 03M8 comes in two shapes: for `𝒪`-modules it is
`AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow` — the direct image along `f` of the
unit of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at `τ`, followed by the
composition comparison of Stacks 03LU — and for sheaves of sets on the small étale sites it is
`AlgebraicGeometry.Space.chartDirectImageUnitArrow`, built the same way from the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` and the comparison of Stacks 03G2,
part (3).

Each of the two *factors* of the module arrow was read on underlying sheaves of sets already:
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_unit_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartUnitArrowSheafTransfer.lean`) for the unit and
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`) for the
comparison.  What this file supplies is the **composite of those two right-hand sides**, namely

`chartDirectImageUnitArrow f hτ (𝒱F) = (smallEtaleDirectImage f).map
  (moduleSheafRestrictionUnitApp τ hτ F) ≫ (smallToposMorphismTypeU_comp τ f).hom.app (𝒱_U(F|_U))`

— the set-level first arrow at the sheaf of sets underlying a module, written as the two factor
comparisons prescribe.  The two sides are the same term with two of their implicit objects spelled
differently, so the statement is true by `Eq.refl`; but that single `rfl` does not terminate, and
the file's work is the ladder of names that makes the reduction finite.  See the implementation
notes.

## Main definitions

The three definitions below are one and the same morphism of sheaves of sets — the direct image
along `f` of `AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`, followed by the composition
comparison of Stacks 03G2, part (3) — differing only in how their source and target are spelled.

* `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrow`: **the first arrow of
  Stacks 03M8 at the sheaf of sets underlying an `𝒪_X`-module**, as `f_*(𝒱F) ⟶ a_*(𝒱(F|_U))`.
  This is the hub, and the spelling the two factor comparisons meet in.
* `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowSetRestriction`: the same arrow as
  `f_*(𝒱F) ⟶ a_*((𝒱F)|_U)`, with its target through the small étale restriction of sheaves of
  sets — the spelling `AlgebraicGeometry.Space.chartDirectImageUnitArrow` carries.
* `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds`: the same arrow as
  `𝒱(f_*F) ⟶ 𝒱(a_*(F|_U))`, with its source and target through the direct image of *modules* —
  the spelling the image under `𝒱` of the module arrow carries, and so the spelling a comparison
  with the module arrow has to be stated in.

## Main results

* `AlgebraicGeometry.Space.chartDirectImageUnitArrow_moduleSheaf`: **the set-level first arrow of
  Stacks 03M8, read at the sheaf of sets underlying an `𝒪_X`-module, is the composite of the two
  factor comparisons.**  This is the identification the two factor comparisons were waiting on.
* `AlgebraicGeometry.Space.chartDirectImageUnitArrow_moduleSheaf_eq_setRestriction`,
  `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrow_eq` and
  `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds_eq`: the rungs of the
  ladder, each one spelling change of one object.

## Implementation notes

**The reconciliations, and why they have to be taken one at a time.**  The composite of the two
factor comparisons reads its second factor at `𝒱_U(F|_U)`, because that is the object
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` names, while
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` reads its own second factor at `(𝒱_XF)|_U`;
and its first factor is named through `𝒱` by
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`, where
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` writes the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` raw.  Each of these spellings is
definitionally equal to the next, by `AlgebraicGeometry.Space.moduleSheaf_modulePushforward` and
`AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback`, both of which hold by `Eq.refl`, and
each single crossing is checked in a fraction of a second.  Two of them at once is not: the
displayed equation of this file's header, which has one crossing in each of its two factors,
reports

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been
reached`

after 77 seconds when it is proved by `rfl` in one step.  The section-level form of it — the
manoeuvre that dissolved the comparison factor itself, see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean` — diverges the
same way, because here the reconciliation lies in the two sides' *result* type rather than in
their arguments, and assembling the whole arrow in one `show` reports
`(deterministic) timeout at 'isDefEq'`.

The definitions below are what take the crossings one at a time.  Consecutive rungs differ in the
spelling of exactly one thing, so each `rfl` below has exactly one crossing to check, and
`Eq.trans` composes them: the reduction the kernel performs is the same, but it is performed
three times on a third of the problem instead of once on the whole of it.  This is the discipline
of `AlgebraicGeometry.Space.modulePullbackUnitApp`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationTriangle.lean`) and of
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`, applied to a composite rather than to a
factor.

Nothing here raises a compiler limit or disables a linter.

## What is not done

**The module arrow's image under `𝒱` is not identified with the composite**, that is

`𝒱.map (moduleChartDirectImageUnitArrow f hτ F) =
  moduleSheafChartDirectImageUnitArrowModuleEnds f hτ F`

is not proved, and with it the chain down to
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` is not closed.  The statement is the right
one — its two sides have the same source and target, and
`AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds` exists precisely so that
it can be stated — and the two factor comparisons are exactly the two halves of its proof.  What
blocks it is the *splitting* of `𝒱.map` over the composite.  Concretely:

* the split `𝒱.map (moduleChartDirectImageUnitArrow f hτ F) = 𝒱.map ((modulePushforward f).map
  (unit.app F)) ≫ 𝒱.map ((modulePushforwardCompIso τ f).hom.app (F|_U))` **elaborates as a
  statement** — a `def` returning it as a `Prop` is accepted in under a second — and is *not*
  provable: `CategoryTheory.Functor.map_comp`, with its two arguments supplied explicitly,
  reports `(deterministic) timeout at 'whnf'`, and so does `rfl`, and so does
  `rw [moduleChartDirectImageUnitArrow]` followed by `exact Functor.map_comp _ _` — the rewrite
  succeeds and the `exact` is what times out.  The rewrite also leaves a goal that `rw` itself
  then reports as "not type-correct under the `implicit` transparency level", which is the shape
  of the trouble: the composite's category is `AlgebraicGeometry.Space.Modules`, a definition for
  `SheafOfModules` of the structure sheaf, and its `CategoryTheory.Category` instance is what the
  two sides have to be compared through;
* feeding the two factor comparisons to a generic clause
  `G.map a = a' → G.map b = b' → G.map (a ≫ b) = a' ≫ b'` elaborates and is then rejected by the
  kernel, `error: (kernel) deterministic timeout`;
* rewriting the two comparisons backwards into `𝒱` and collecting them with
  `CategoryTheory.Functor.map_comp` leaves that clause inapplicable: `rw` reports that it cannot
  find the pattern `Functor.map ?F ?f ≫ Functor.map ?F ?g`, because the middle object of the
  goal's composite is not of the form `𝒱.obj ?N`, and applying it by `exact` instead reports
  `(deterministic) timeout at 'isDefEq'`;
* pinning that middle object with a type ascription inside a further rung of the ladder makes
  the two sides' middle objects agree — the rung and its `rfl` to
  `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrowModuleEnds` both go through — but
  does not make `CategoryTheory.Functor.map_comp` applicable: the `exact` still reports
  `(deterministic) timeout at 'whnf'`, so the obstruction is the splitting itself and not the
  spelling of the objects it is split at.

The vocabulary that would plausibly dissolve it is therefore on the *module* side, not the sheaf
side: a declaration naming the `CategoryTheory.Category` instance of
`AlgebraicGeometry.Space.Modules` through which the composite is formed, or a restatement of
`CategoryTheory.Functor.map_comp` for `CategoryTheory.Sheaf.moduleSheafFunctor` proved once at
variable modules and arrows, so that the splitting is an instantiation rather than a match — the
manoeuvre of `Stacks.AlgebraicGeometry.ProjInclusionTwist.comp_congr` and its neighbours
(`StacksFrontier/AlgebraicGeometry/ProjInclusionTwist/Basic.lean`), whose implementation notes record
the same distinction between instantiating a general `rfl` lemma and asking for `rfl` at the
instance.

The clause is also stated for the first arrow only.  The two parallel arrows
`AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow` and
`AlgebraicGeometry.Space.chartDirectImageParallelArrow` need the same treatment, and they have one
factor more: between the two composition comparisons sits
`AlgebraicGeometry.Space.moduleRestrictionUnitArrow`, whose set-level counterpart
`AlgebraicGeometry.Space.restrictionUnitArrow` substitutes the factorization `h ≫ τ = ρ` before
producing its term, so the clause for it is a statement under a `subst` rather than a composite of
comparisons.  The inverse half of the composition comparison those arrows use is in hand, as
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_inv_app`.

Granted the parallel arrows, the module sequence of Stacks 03M8 is a complex by
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow_eq` and faithfulness of the
underlying sheaf of sets (`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`), and its
exactness follows from the exactness of the set-level sequence by
`AlgebraicGeometry.Space.isLimitOfIsLimitModuleSheaf`.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-! ### The first arrow on underlying sheaves of sets, and the ladder of its spellings -/

/-- **The first arrow `f_*(𝒱F) ⟶ a_*(𝒱(F|_U))` of Stacks 03M8 at the sheaf of sets underlying
an `𝒪_X`-module**, for `a = τ ≫ f`: the direct image along `f` of
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`, followed by the composition comparison of
Stacks 03G2, part (3), read at `𝒱_U(F|_U)`.

Its two factors are the right-hand sides of
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_unit_app` and
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`, so this is the
sheaf of sets underlying the first arrow of the module sequence of Stacks 03M8, factor by factor;
and it is `AlgebraicGeometry.Space.chartDirectImageUnitArrow` at `𝒱F`, by
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_moduleSheaf`. -/
def moduleSheafChartDirectImageUnitArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    (smallEtaleDirectImage B S hS f).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) ⟶
      (smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).obj
          ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) :=
  (smallEtaleDirectImage B S hS f).map (moduleSheafRestrictionUnitApp B S hS τ hτ F) ≫
    (smallToposMorphismTypeU_comp B S hS τ f).hom.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).obj
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))

/-- **The first arrow of Stacks 03M8 at the sheaf of sets underlying an `𝒪_X`-module, with its
target written through the small étale restriction of sheaves of sets**, as `a_*((𝒱F)|_U)` rather
than as `a_*(𝒱(F|_U))`.

This is the spelling `AlgebraicGeometry.Space.chartDirectImageUnitArrow` carries, and the whole
difference from `AlgebraicGeometry.Space.moduleSheafChartDirectImageUnitArrow` is the object the
composition comparison is read at. -/
def moduleSheafChartDirectImageUnitArrowSetRestriction (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    (smallEtaleDirectImage B S hS f).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) ⟶
      (smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  (smallEtaleDirectImage B S hS f).map (moduleSheafRestrictionUnitApp B S hS τ hτ F) ≫
    (smallToposMorphismTypeU_comp B S hS τ f).hom.app
      ((smallEtaleSetRestriction B S hS τ hτ).obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))

/-- **The first arrow of Stacks 03M8 at the sheaf of sets underlying an `𝒪_X`-module, with its
source and target written through the direct image of modules**, as `𝒱(f_*F) ⟶ 𝒱(a_*(F|_U))`
rather than as `f_*(𝒱F) ⟶ a_*(𝒱(F|_U))`.

This is the spelling the image under `𝒱` of
`AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow` carries, so it is the spelling in which
a comparison of the two arrows can be *stated*; the two agree on both ends by
`AlgebraicGeometry.Space.moduleSheaf_modulePushforward`, at `f` and at `τ ≫ f`.  See this file's
"What is not done" for the comparison itself. -/
def moduleSheafChartDirectImageUnitArrowModuleEnds (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj F) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS (τ ≫ f)).obj
          ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) :=
  (smallEtaleDirectImage B S hS f).map (moduleSheafRestrictionUnitApp B S hS τ hτ F) ≫
    (smallToposMorphismTypeU_comp B S hS τ f).hom.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).obj
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))

/-- **The first rung: the source and target may be read through the direct image of sheaves of
sets instead of through the direct image of modules.**  Both crossings are
`AlgebraicGeometry.Space.moduleSheaf_modulePushforward`, at `f` and at `τ ≫ f`, and they are
checked independently of one another, being the source and the target of the arrow; the two sides
are otherwise the same term. -/
theorem moduleSheafChartDirectImageUnitArrowModuleEnds_eq (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleSheafChartDirectImageUnitArrowModuleEnds B S hS f hτ F =
      moduleSheafChartDirectImageUnitArrow B S hS f hτ F := rfl

/-- **The second rung: the composition comparison may be read at `(𝒱F)|_U` instead of at
`𝒱(F|_U)`.**  The two objects are the same sheaf of sets by
`AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback`; the first factor is the same term on
both sides, which is what keeps this `rfl` to the one crossing. -/
theorem moduleSheafChartDirectImageUnitArrow_eq (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    moduleSheafChartDirectImageUnitArrow B S hS f hτ F =
      moduleSheafChartDirectImageUnitArrowSetRestriction B S hS f hτ F := rfl

/-! ### The set-level first arrow -/

/-- **The third rung: the set-level first arrow of Stacks 03M8, read at the sheaf of sets
underlying an `𝒪_X`-module, is the composite with its target written through the small étale
restriction.**

The two sides' second factors are the same term, and their first factors differ only by the name
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`, which is the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` with its type written through `𝒱`;
so this `rfl` is the reconciliation of that one spelling, and nothing else. -/
theorem chartDirectImageUnitArrow_moduleSheaf_eq_setRestriction (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    chartDirectImageUnitArrow B S hS f hτ
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) =
      moduleSheafChartDirectImageUnitArrowSetRestriction B S hS f hτ F := rfl

/-- **The set-level first arrow `f_*P ⟶ a_*(P|_U)` of Stacks 03M8, read at the sheaf of sets `P`
underlying an `𝒪_X`-module `F`, is the composite of the two factors as the module arrow spells
them**: the direct image along `f` of `AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`,
followed by the composition comparison of Stacks 03G2, part (3), at `𝒱_U(F|_U)`.

This is the identification the two factor comparisons of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartUnitArrowSheafTransfer.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean` were waiting on:
with it, the set-level first arrow of Stacks 03M8 at the sheaf of sets underlying a module is the
composite of the sheaves of sets underlying the two factors of the module arrow.

It is two rungs of the ladder composed; stated as a single `rfl` it does not terminate, as this
file's implementation notes record. -/
theorem chartDirectImageUnitArrow_moduleSheaf (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    chartDirectImageUnitArrow B S hS f hτ
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) =
      moduleSheafChartDirectImageUnitArrow B S hS f hτ F :=
  (chartDirectImageUnitArrow_moduleSheaf_eq_setRestriction B S hS f hτ F).trans
    (moduleSheafChartDirectImageUnitArrow_eq B S hS f hτ F).symm

end AlgebraicGeometry.Space

end
